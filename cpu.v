module cpu(
  input wire clk,
  input wire resetn,
  output wire led,
  output wire [7:0] debug_port1,
  output wire [7:0] debug_port2,
  output wire [7:0] debug_port3
  );

localparam data_width = 32;
localparam data_width_l2b = $clog2(data_width / 8);
localparam data_words = 512;
localparam data_words_l2 = $clog2(data_words);
localparam data_addr_width = data_words_l2;

  reg [data_width - 1:0]  data_mem[data_words - 1:0];
  reg [data_width - 1:0]  data_mem_rd;
  reg [data_width - 1:0]  data_mem_wd;
  reg [data_addr_width - 1:0] data_addr;
  reg data_mem_we;

localparam code_width = 32;
localparam code_width_l2b = $clog2(data_width / 8);
localparam code_words = 512;
localparam code_words_l2 = $clog2(data_words);
localparam code_addr_width = code_words_l2 - code_width_l2b;
  reg [code_width - 1:0]  code_mem[data_words - 1:0];
  reg [code_width - 1:0]  code_mem_rd;
  wire [code_addr_width - 1:0] code_addr;

  reg [29:0]  pc;

  assign led = pc[1]; // make the LED blink on the low order bit of the PC

  assign code_addr = pc[code_addr_width - 1:0];

  reg [31:0] rf[0:31];
  reg [31:0] rf_d1;
  reg [31:0] rf_d2;
  reg [4:0] rf_rs1;
  reg [4:0] rf_rs2;
  reg [4:0] rf_ws;
  reg [31:0] rf_wd;
  reg rf_we;

  // UPDATE CODE_MEM_RD
  always @(posedge clk) begin
    code_mem_rd <= code_mem[code_addr];
  end

  // UPDATE DATA_MEM
  always @(posedge clk) begin
    if (data_mem_we)
        data_mem[data_addr] <= data_mem_wd;
    data_mem_rd <= data_mem[data_addr];
  end

  // UPDATE REGS
  always @(posedge clk) begin
    data_mem_wd <= 0;
    data_addr <= 0;
    data_mem_we <= 0;
    if (!resetn) begin
      pc <= 0;
    end else begin
      data_addr <= pc;
      // if INST is branch then branch
      if (code_mem_rd[27:25] == 3'b101) begin
        pc <= code_mem_rd[23:0];
        rf_we <= 1'b0;
      end else begin
        pc <= pc + 1;
        // if INST is add then add immediate
        if (code_mem_rd[24:21] == 4'b0100) begin
          rf_we <= 1'b1;
          rf_ws <= code_mem_rd[15:12];
          rf_wd <= rf[code_mem_rd[19:16]] + code_mem_rd[7:0];
          rf_d1 <= rf[rf_rs1];
          rf_d2 <= rf[rf_rs2];
          // rf[ws] <= rf_wd
          rf[code_mem_rd[15:12]] <= rf[code_mem_rd[19:16]] + code_mem_rd[7:0];
        end else begin
          rf_we <= 1'b0;
        end
      end
    end
  end

  // CODE TESTING BLOCK
  initial begin
    // initialize reg
    rf[0] = 1'b1;
    rf[1] = 1'b1;
    // add instructions between reg0 and reg1, with immediate 1
    code_mem[0] = 32'b11100010100000000001000000000001;
    code_mem[1] = 32'b11100010100000010000000000000001;
    code_mem[2] = 32'b11100010100000000001000000000001;
    code_mem[3] = 32'b11100010100000010000000000000001;
    // branch instruction to set pc to 0
    code_mem[4] = 32'b11101010000000000000000000000000;
  end

  assign debug_port1 = pc[7:0];
  assign debug_port2 = rf_d1[7:0];
  assign debug_port3 = rf_we;

endmodule
