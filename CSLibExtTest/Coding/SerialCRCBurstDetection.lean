/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.SerialCRCBurstDetection
public import CSLibExt.Coding.FixedLengthCRCFrames

@[expose] public section

namespace CSLibExtTest.Coding.SerialCRCBurstDetection

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.SerialCRCBurstDetection
open CSLibExt.Coding.FixedLengthCRCFrames

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
example : runRegister 16 xmodemTaps (serialCodeword 16 xmodemTaps xmodemCheckPayload) = 0#16 :=
  runRegister_serialCodeword 16 xmodemTaps xmodemCheckPayload

/-- The augmented check of the error-free XMODEM check frame is zero as well. -/
example : finalRegister 16 xmodemTaps (serialCodeword 16 xmodemTaps xmodemCheckPayload) = 0#16 :=
  finalRegister_serialCodeword 16 xmodemTaps xmodemCheckPayload

/-- A leading zero byte leaves the XMODEM check value `0x31C3` unchanged. -/
example :
    finalRegister 16 xmodemTaps (List.replicate 8 false ++ xmodemCheckPayload) = 0x31C3#16 :=
  finalRegister_xmodem_leading_zero_byte

/-- A length-16 burst at positions `3, ..., 18` of the 88-bit check frame is rejected. -/
example :
    runRegister 16 xmodemTaps
        (List.zipWith Bool.xor (serialCodeword 16 xmodemTaps xmodemCheckPayload)
          (List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false)) ≠
        0#16 :=
  xmodem_detects_length_sixteen_burst.2

/-- The serial codeword is the body that the fixed-length frame encoder transmits. -/
example (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    serialCodeword r taps bits = encodedBody r taps bits :=
  rfl

/-- Burst detection reaches the frame parser: a frame whose body is a codeword hit by a nonzero
nonwrapping burst of length at most `r` has no accepted translation, because the parser's
acceptance test is the receiver register `runRegister` on the body. -/
example (l r : ℕ) (hr : 1 ≤ r) (taps : BitVec r) (h0 : taps.getLsbD 0 = true)
    (bits e : List Bool) (hbits : bits.length = l) (hlen : e.length = bits.length + r) (L : ℕ)
    (he : IsBitBurstLE e L) (hL : L ≤ r) (out : List Bool) :
    ¬(frameParser l r taps).Translates
        (FrameToken.start ::
          (List.zipWith Bool.xor (serialCodeword r taps bits) e).map FrameToken.bit ++
            [FrameToken.endTok])
        out :=
  nonzeroRemainderBody_rejected l r taps _
    (by rw [List.length_zipWith, length_serialCodeword, hlen, hbits, Nat.min_self])
    (runRegister_ne_zero_of_isBitBurstLE r hr taps h0 bits e hlen L he hL) out

/-- The receiver rejects the length-16 XMODEM burst frame in the frame parser. -/
example (out : List Bool) :
    ¬(frameParser 72 16 xmodemTaps).Translates
        (FrameToken.start ::
          (List.zipWith Bool.xor (serialCodeword 16 xmodemTaps xmodemCheckPayload)
            (List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false)).map
              FrameToken.bit ++
            [FrameToken.endTok])
        out :=
  nonzeroRemainderBody_rejected 72 16 xmodemTaps _ (by decide +kernel)
    xmodem_detects_length_sixteen_burst.2 out

end CSLibExtTest.Coding.SerialCRCBurstDetection
