/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.SerialCRCBurstDetection

@[expose] public section

namespace CSLibExtTest.Coding.SerialCRCBurstDetection

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.SerialCRCBurstDetection

/-- The CRC-16/XMODEM check value for the ASCII payload `"123456789"` is `0x31C3`. -/
example : finalRegister 16 xmodemTaps xmodemCheckPayload = 0x31C3#16 :=
  finalRegister_xmodem_check

/-- The transmitted XMODEM check frame is the payload followed by `0x31C3`, MSB first. -/
example :
    serialCodeword 16 xmodemTaps xmodemCheckPayload =
      xmodemCheckPayload ++ Nat.toBitsBE 16 0x31C3 :=
  serialCodeword_xmodem_check

/-- The XMODEM check payload has 72 bits, so its codeword has 88 bits. -/
example : (serialCodeword 16 xmodemTaps xmodemCheckPayload).length = 88 := by
  rw [length_serialCodeword]
  decide

/-- The receiver accepts the error-free XMODEM check frame. -/
example : finalRegister 16 xmodemTaps (serialCodeword 16 xmodemTaps xmodemCheckPayload) = 0#16 :=
  finalRegister_serialCodeword 16 xmodemTaps xmodemCheckPayload

/-- A leading zero byte leaves the XMODEM check value `0x31C3` unchanged. -/
example :
    finalRegister 16 xmodemTaps (List.replicate 8 false ++ xmodemCheckPayload) = 0x31C3#16 :=
  finalRegister_xmodem_leading_zero_byte

/-- A length-16 burst at positions `3, ..., 18` of the 88-bit check frame is rejected. -/
example :
    finalRegister 16 xmodemTaps
        (List.zipWith Bool.xor (serialCodeword 16 xmodemTaps xmodemCheckPayload)
          (List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false)) ≠
        0#16 :=
  xmodem_detects_length_sixteen_burst.2

end CSLibExtTest.Coding.SerialCRCBurstDetection
