////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////


/**************STUFF TO DO***************
 * fix memory so that it isn't a bunch if registers.
 * add pipelining
 * - add registers
 * - add control logic
 * - squash bad instructions for branches
*/
module cpu (
  input  wire       clk,
  input  wire       resetn,
  output wire       led,
  output wire [7:0] debug_port1,
  output wire [7:0] debug_port2,
  output wire [7:0] debug_port3
  );

  assign led = (read_reg_one[1] & read_reg_one[0]) | (read_reg_one[0] & read_reg_one[2]);
  assign debug_port1 = ALU_o_m[7:0];
  assign debug_port2 = read_data_m[7:0];
  assign debug_port3 = {3'b0,store_inst_m,3'b0,load_inst_m};

 //control wires
  wire reg_w_en_d, reg_w_en_x, reg_w_en_m, reg_w_en_w;
  wire load_inst_d, load_inst_x, load_inst_m, load_inst_w;
  wire store_inst_d, store_inst_x, store_inst_m;
  wire immediate_inst_d, immediate_inst_x;
  wire branch_inst_d, branch_inst_x;
  wire branch_link_d, branch_link_x, branch_link_m, branch_link_w;
  wire [3:0] opcode_d, opcode_x;
  wire take_branch, take_branch_n, take_branch_n_n;
  wire squash;
  ///////////////

  //connection wires/////
  reg [31:0] instruction_f, instruction_d, instruction_x, instruction_m, instruction_w;
  reg [31:0] pc, pc_d, pc_x, pc_m, pc_n, pc_w;
  reg [31:0] read_reg_one_d, read_reg_one_x, read_reg_two_d, read_reg_two_x;
  reg [31:0] reg_or_forward_x, reg_or_forward_m;
  reg [31:0] ALU_o_x, ALU_o_m;
  reg [31:0] read_data_m;
  reg [31:0] write_reg;
  reg [31:0] immediate_d, immediate_x;
  reg [31:0] ALU_one_i, ALU_two_i;
  reg [31:0] data_into_reg_m, data_into_reg_w;
  reg [3:0]  inst_write_addr;
  reg [1:0]  choice_one, choice_two;
  reg        overflow;
  reg        carry;
  ///////////////////////

  //condition bits//
  reg negative_r, zero_r, carry_r, overflow_r;
  //////////////////

  control_unit main_control
    (.instruction(instruction_d[31:20])
    ,.resetn(resetn)
    ,.reg_w_en(reg_w_en_d)
    ,.load_inst(load_inst_d)
    ,.store_inst(store_inst_d)
    ,.immediate_inst(immediate_inst_d)
    ,.branch_inst(branch_inst_d)
    ,.opcode(opcode_d)
    ,.branch_link(branch_link_d)
    );

  branch_control_unit branch_check
    (.instruction(instruction_x[31:28])
    ,.zero_r(zero_r)
    ,.negative_r(negative_r)
    ,.carry_r(carry_r)
    ,.overflow_r(overflow_r)
    ,.pass_cond(pass_cond)
    );

  assign take_branch = branch_inst_x & pass_cond;
  assign squash = ((take_branch | take_branch_n) & ~take_branch_n_n);

  mux32b2to1 pc_add
    (.zero_i(pc + 4)
    ,.one_i(pc_x + {{6{instruction_x[23]}}, instruction_x[23:0], 2'b00})
    ,.select_i(take_branch)
    ,.out_o(pc_n)
    );

  inst_mem code_data
    (.rd_addr_i(pc)
    ,.inst_o(instruction_f)
    );

  mux4b2to1 write_reg_mux
    (.zero_i(instruction_w[15:12])
    ,.one_i(4'b1110)
    ,.select_i(branch_link_w)
    ,.out_o(inst_write_addr)
    );

  registers arm_regs
    (.rd_addr_1_i(instruction_d[19:16])
    ,.rd_addr_2_i(instruction_d[3:0])
    ,.w_addr_i(inst_write_addr)
    ,.data_i(write_reg)
    ,.w_en_i(reg_w_en_w)
    ,.clk_i(clk)
    ,.data_1_o(read_reg_one_d)
    ,.data_2_o(read_reg_two_d)
    );

  mux32b2to1 immediate_choice
    (.zero_i({{24{instruction_d[7]}}, instruction_d[7:0]})
    ,.one_i({{20{instruction_d[11]}}, instruction_d[11:0]})
    ,.select_i(store_inst_d | load_inst_d)
    ,.out_o(immediate_d)
    );

  forwarding_unit data_one_mux
    (.destination_p(instruction_m[15:12])
    ,.destination_pp(instruction_w[15:12])
    ,.source(instruction_x[19:16])
    ,.load_p(load_inst_m)
    ,.store_p(store_inst_m)
    ,.load_pp(load_inst_w)
    ,.store_pp(store_inst_w)
    ,.choice(choice_one)
    );

  forwarding_unit data_two_mux
    (.destination_p(instruction_m[15:12])
    ,.destination_pp(instruction_w[15:12])
    ,.source(instruction_x[3:0])
    ,.load_p(load_inst_m)
    ,.store_p(store_inst_m)
    ,.load_pp(load_inst_w)
    ,.store_pp(store_inst_w)
    ,.choice(choice_two)
    );


  mux32b3to1 forwarding_one
    (.zero_i(read_reg_one_x)
    ,.one_i(data_into_reg_m)
    ,.two_i(data_into_reg_w)
    ,.select_i(choice_one)
    ,.out_o(ALU_one_i)
    );

  mux32b3to1 forwarding_two
    (.zero_i(read_reg_two_x)
    ,.one_i(data_into_reg_m)
    ,.two_i(data_into_reg_w)
    ,.select_i(choice_two)
    ,.out_o(reg_or_forward_x)
    );

  mux32b2to1 imm_or_reg
    (.zero_i(reg_or_forward_x)
    ,.one_i(immediate_x)
    ,.select_i(immediate_inst_x)
    ,.out_o(ALU_two_i)
    );

  ALU main_alu
    (.data_1_i(ALU_one_i)
    ,.data_2_i(ALU_two_i)
    ,.data_o(ALU_o_x)
    ,.control_i(opcode_x)
    ,.overflow(overflow)
    ,.carry(carry)
    );

  data_mem cpu_data
    (.addr_i(ALU_o_m)
    ,.data_i(reg_or_forward_m)
    ,.w_en_i(store_inst_m)
    ,.rd_en_i(load_inst_m)
    ,.clk_i(clk)
    ,.data_o(read_data_m)
    );

  mux32b2to1 write_choice
    (.zero_i(ALU_o_m)
    ,.one_i(read_data_m)
    ,.select_i(load_inst_m)
    ,.out_o(data_into_reg_m)
    );

  mux32b2to1 link_choice
    (.zero_i(data_into_reg_w)
    ,.one_i(pc_w)
    ,.select_i(branch_link_w)
    ,.out_o(write_reg)
    );


  //pc gen
  always @(posedge clk) begin
    if (~resetn) begin
      pc <= 32'b0;
    end else begin
      pc <= pc_n;
    end
  end

  //condition bits register
  always @(posedge clk) begin
    if ((~branch_inst_x) & (~store_inst_x) & (~load_inst_x)) begin
      negative_r <= ALU_o_x[31];
      zero_r <= (ALU_o_x == 32'b0);
      carry_r <= carry;
      overflow_r <= overflow;
    end
  end

  //fetch to decode
  always @(posedge clk) begin
    if (~resetn) begin
      instruction_d <= 32'b0;
      pc_d <=32'b0;
    end else begin
      instruction_d <= instruction_f;
      pc_d <= pc;
    end
  end

  //decode to execute
  always @(posedge clk) begin
    if (squash) begin
      instruction_x <= 32'b0;
      pc_x <= 32'b0;
      read_reg_one_x <= 32'b0;
      read_reg_two_x <= 32'b0;
      opcode_x <= 4'b0;
      immediate_x <= 32'b0;
      load_inst_x <= 1'b0;
      store_inst_x <= 1'b0;
      reg_w_en_x <= 1'b0;
      branch_link_x <= 1'b0;
      immediate_inst_x <= 1'b0;
      branch_inst_x <= 1'b0;
    end else begin
      instruction_x <= instruction_d;
      pc_x <= pc_d;
      read_reg_one_x <= read_reg_one_d;
      read_reg_two_x <= read_reg_two_d;
      opcode_x <= opcode_d;
      immediate_x <= immediate_d;
      load_inst_x <= load_inst_d;
      store_inst_x <= store_inst_d;
      reg_w_en_x <= reg_w_en_d;
      branch_link_x <= branch_link_d;
      immediate_inst_x <= immediate_inst_d;
      branch_inst_x <= branch_inst_d;
    end
  end

  //execute to memory
  always @(posedge clk) begin
    instruction_m <= instruction_x;
    reg_or_forward_m <= reg_or_forward_x;
    ALU_o_m <= ALU_o_x;
    pc_m <= pc_x;
    load_inst_m <= load_inst_x;
    store_inst_m <= store_inst_x;
    reg_w_en_m <= reg_w_en_x;
    branch_link_m <= branch_link_x;
    take_branch_m <= take_branch_x;
  end

  //memory to write
  always @(posedge clk) begin
    data_into_reg_w <= data_into_reg_m;
    instruction_w <= instruction_m;
    pc_w <= pc_m;
    load_inst_w <= load_inst_m;
    store_inst_w <= store_inst_m;
    reg_w_en_w <= reg_w_en_m;
    branch_link_w <= branch_link_m;
  end

  //squash instructions
  always @(posedge clk) begin
    take_branch_n <= take_branch;
    take_branch_n_n <= take_branch_n;
  end
endmodule
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////helper modules//////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

module inst_mem
  ( input wire [31:0] rd_addr_i
  , output reg [31:0] inst_o
  );

  always @(*) begin
    case (rd_addr_i)
      //testing imm add,imm subtract, and unconditional branch
      // 32'h00000000 : inst_o = 32'he2811003; //ADD R1, R1, #3
      // 32'h00000004 : inst_o = 32'he2411002; //SUB R1, R1, #2
      // 32'h00000008 : inst_o = 32'heafffffe; //B #-2
      // default : inst_o = 32'heaffffff; //B #-1

      // testing reg add, load, store, branch
      32'h00000000 : inst_o = 32'he2822003; //ADD R2, R2, #3
      32'h00000004 : inst_o = 32'he0823003; //ADD R3, R2, R3
      32'h00000008 : inst_o = 32'he5823000; //STR R3, [R2]
      32'h0000000c : inst_o = 32'he5923000; //LDR R3, [R2]
      32'h00000010 : inst_o = 32'heafffffd; //B #-2
      // default : inst_o = 32'heaffffff; //B #-1

      // testing branch+link, conditinal branch
      //32'h00000000 : inst_o = 32'he2811003; //ADD R1, R1, #3
      //32'h00000004 : inst_o = 32'he2822007; //ADD R2, R2, #7
      //32'h00000008 : inst_o = 32'he0423001; //SUB R3, R2, R1
      //32'h0000000c : inst_o = 32'h0a000002; //BEQ #2
      //32'h00000010 : inst_o = 32'he2422001; //SUB R2, R2, #1
      //32'h00000014 : inst_o = 32'hebfffffd; //Bl #-3

      // 12 instructions
      // 32'h00000000 : inst_o = 32'he2811003; //ADD R1, R1, #3 TESTING ADD IMM 1
      // 32'h00000004 : inst_o = 32'he2411002; //SUB R1, R1, #2 TESTING SUB IMM 2
      // 32'h00000008 : inst_o = 32'he2822003; //ADD R2, R2, #3
      // 32'h0000000c : inst_o = 32'he0823003; //ADD R3, R2, R3 TESTING ADD REG 3
      // 32'h00000010 : inst_o = 32'he5823000; //STR R3, [R2]   TESTING STR     4
      // 32'h00000014 : inst_o = 32'he5924000; //LDR R4, [R2]   TESTING LDR     5
      // 32'h00000018 : inst_o = 32'he0423001; //SUB R3, R2, R1 TESTING SUB REG 6
      // 32'h0000001c : inst_o = 32'he1811002; //ORR R1, R2     TESTING ORR     7
      // 32'h00000020 : inst_o = 32'he0011002; //AND R1, R2     TESTING AND     8
      // 32'h00000024 : inst_o = 32'he0211002; //EOR R1, R2     TESTING EOR     9
      // 32'h00000028 : inst_o = 32'he0411001; //RESET R1 to 0
      // 32'h0000002c : inst_o = 32'he0422002; //RESET R2 to 0
      // 32'h00000030 : inst_o = 32'hea000004; //B #4           TESTING B       10
      //
      // 32'h00000040 : inst_o = 32'he2811003; //ADD R1, R1, #3
      // 32'h00000044 : inst_o = 32'he2822007; //ADD R2, R2, #7
      // 32'h00000048 : inst_o = 32'he0423001; //SUB R3, R2, R1
      // 32'h0000004c : inst_o = 32'h0a000002; //BEQ #2         TESTING BEQ     11
      // 32'h00000050 : inst_o = 32'he2422001; //SUB R2, R2, #1
      // 32'h00000054 : inst_o = 32'hebfffffd; //Bl #-3         TESTING BL      12
      default : inst_o = 32'heaffffff; //B #-1
    endcase
  end
endmodule

module data_mem
  ( input wire [31:0] addr_i
  , input wire [31:0] data_i
  , input wire w_en_i
  , inout wire rd_en_i
  , input wire clk_i
  , output reg [31:0] data_o
  );

  reg [31:0] data [31:0];
  assign data_o = (rd_en_i) ? data[addr_i] : 32'b0;
  always @(posedge clk_i) begin
    if (w_en_i) begin
      data[addr_i] <= data_i;
    //end else if (rd_en_i) begin
      //data_o <= data[addr_i];
    end
  end
endmodule

module registers
  ( input wire [3:0] rd_addr_1_i
  , input wire [3:0] rd_addr_2_i
  , input wire [3:0] w_addr_i
  , input wire [31:0] data_i
  , input wire w_en_i
  , input wire clk_i
  , output wire [31:0] data_1_o
  , output wire [31:0] data_2_o
  );

  reg [31:0] regist [15:0];

  assign data_1_o = regist[rd_addr_1_i];
  assign data_2_o = regist[rd_addr_2_i];

  always @(posedge clk_i) begin
    if (w_en_i) begin
      regist[w_addr_i] <= data_i;
    end
  end
endmodule

module ALU
  ( input wire [31:0] data_1_i
  , input wire [31:0] data_2_i
  , output wire [31:0] data_o
  , output wire overflow
  , output wire carry
  , input wire [3:0] control_i
  );

  reg [32:0] data_t;

  always @(*) begin
    case (control_i)
      4'b0000 : data_t = data_1_i & data_2_i;
      4'b0001 : data_t = data_1_i ^ data_2_i;
      4'b0010 : data_t = data_1_i + ~data_2_i + 1;
      4'b0011 : data_t = data_2_i + ~data_1_i + 1;
      4'b0100 : data_t = data_1_i + data_2_i;
      4'b1100 : data_t = ~(data_1_i | data_2_i);
      4'b1101 : data_t = data_2_i;
      4'b1110 : data_t = data_1_i & (~data_2_i);
      4'b1111 : data_t = ~data_2_i;
      default : data_t = data_1_i;
    endcase
  end
  assign overflow = ((data_t[32:31] == 2'b01) | (data_t[32:31] == 2'b10));
  assign carry = (((data_o < data_1_i) & (control_i == 4'b0100)) | ((data_o > data_1_i) & (control_i[3:1] == 3'b001)));
  assign data_o = data_t[31:0];
endmodule

module mux32b2to1
  ( input wire [31:0] zero_i
  , input wire [31:0] one_i
  , input wire select_i
  , output reg [31:0] out_o
  );

  always @(*) begin
    case (select_i)
      1'b0 : out_o = zero_i;
      1'b1 : out_o = one_i;
      default : out_o = 32'b0;
    endcase
  end
endmodule

module mux32b3to1
  ( input wire [31:0] zero_i
  , input wire [31:0] one_i
  , input wire [31:0] two_i
  , input wire [1:0] select_i
  , output reg [31:0] out_o
  );

  always @(*) begin
    case (select_i)
      2'b00 : out_o = zero_i;
      2'b01 : out_o = one_i;
      2'b10 : out_o = two_i;
      default : out_o = 32'b0;
    endcase
  end
endmodule

module mux4b2to1
  ( input wire [3:0] zero_i
  , input wire [3:0] one_i
  , input wire select_i
  , output reg [3:0] out_o
  );

  always @(*) begin
    case (select_i)
      1'b0 : out_o = zero_i;
      1'b1 : out_o = one_i;
      default : out_o = 4'b0;
    endcase
  end
endmodule

module control_unit
  (input wire [11:0] instruction
  , input wire resetn
  , output wire reg_w_en
  , output wire load_inst
  , output wire store_inst
  , output wire immediate_inst
  , output wire branch_inst
  , output reg [3:0] opcode
  , output wire branch_link
  );
//////////////////////////branch and link ////////////////////////////////////////////////////////data processing/////////////////////////////////////////load/////////////////////////
  assign reg_w_en = ((instruction[7] & ~instruction[6] & instruction[5] & instruction[4]) | (~instruction[7] & ~instruction[6]) | (~instruction[7] & instruction[6] & instruction[0])) & resetn;
  assign load_inst = ((~instruction[7]) & instruction[6] & instruction[0]) & resetn;
  assign store_inst = ((~instruction[7]) & instruction[6] & (~instruction[0])) & resetn;
  assign immediate_inst = ((~instruction[7]) & (instruction[6] ^ instruction[5]));
  assign branch_inst = (instruction[7] & (~instruction[6]) & instruction[5]);
  assign branch_link = (branch_inst & instruction[4]);

  always @(*) begin
    if ((~branch_inst) & (~store_inst) & (~load_inst)) begin
      opcode = instruction[4:1];
    end else begin
      opcode = 4'b0100;
    end
  end
endmodule

module branch_control_unit
  ( input wire [3:0] instruction
  , input wire zero_r
  , input wire negative_r
  , input wire carry_r
  , input wire overflow_r
  , output reg pass_cond
  );

  always @(*) begin
    case (instruction)
      4'b0000 : pass_cond = zero_r;
      4'b0001 : pass_cond = ~zero_r;
      4'b0010 : pass_cond = carry_r;
      4'b0011 : pass_cond = ~carry_r;
      4'b0100 : pass_cond = negative_r;
      4'b0101 : pass_cond = ~negative_r;
      4'b0110 : pass_cond = overflow_r;
      4'b0111 : pass_cond = ~overflow_r;
      4'b1000 : pass_cond = carry_r & ~zero_r;
      4'b1010 : pass_cond = ~carry_r & zero_r;
      4'b1001 : pass_cond = negative_r == overflow_r;
      4'b1011 : pass_cond = negative_r !== overflow_r;
      4'b1100 : pass_cond = ~zero_r & (negative_r == overflow_r);
      4'b1101 : pass_cond = zero_r | (negative_r !== overflow_r);
      4'b1110 : pass_cond = 1'b1;
      4'b1111 : pass_cond = 1'b0;
      default : pass_cond = 1'b0;
    endcase
  end
endmodule

module forwarding_unit
  ( input wire [3:0] destination_pp
  , input wire [3:0] destination_p
  , input wire [3:0] source
  , input wire load_pp
  , input wire store_pp
  , input wire load_p
  , input wire store_p
  , output reg [1:0] choice
  );

  always @(*) begin
    if (destination_p == source & ~store_p) begin
      choice = 2'b01;
    end else if (destination_pp == source & ~store_pp) begin
      choice = 2'b10;
    end else begin
      choice = 2'b00;
    end
  end
endmodule
