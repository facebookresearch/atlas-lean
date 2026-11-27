/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.SerialCRCBurstDetection
import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# Tests for serial CRC burst detection

The CRC-16/XMODEM fixtures follow the CRC RevEng catalogue entry CRC-16/XMODEM (width `16`,
polynomial `0x1021`, zero initial value, no reflection, no final XOR, check value `0x31C3` for the
ASCII payload `"123456789"`):
https://reveng.sourceforge.io/crc-catalogue/16.htm#crc.cat.crc-16-xmodem
-/

namespace CSLibExtTest.Coding.SerialCRCBurstDetection

open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.SerialCRCBurstDetection
open CSLibExt.Coding.FixedLengthCRCFrames

/-! ### The burst predicate -/

/-- A word with no `true` bit is no burst. -/
example : ¬IsBitBurstLE [false, false, false] 3 := by
  rintro ⟨hmem, -⟩
  simp at hmem

/-- A burst has positive length. -/
example : ¬IsBitBurstLE [true] 0 := by
  rintro ⟨-, i, hi⟩
  have := hi 0 (by decide) rfl
  omega

/-- The burst window may run past the end of the word. -/
example : IsBitBurstLE [false, true] 5 :=
  ⟨by decide, 1, by decide⟩

/-- The window is exact: the 17-bit pattern of the generator `0x11021` at positions `3, ..., 19`
is a burst of length `17` but not of length `16`. -/
example :
    ¬IsBitBurstLE (List.replicate 3 false ++ Nat.toBitsBE 17 0x11021 ++ List.replicate 68 false)
      16 := by
  rintro ⟨-, i, hi⟩
  have h3 := hi 3 (by decide) (by decide +kernel)
  have h19 := hi 19 (by decide) (by decide +kernel)
  omega

/-! ### CRC-16/XMODEM -/

/-- The CRC-16/XMODEM generator `X^16 + X^12 + X^5 + 1`. -/
private noncomputable def xmodemGenerator : Polynomial (ZMod 2) :=
  Polynomial.X ^ 16 + Polynomial.X ^ 12 + Polynomial.X ^ 5 + 1

/-- The CRC-16/XMODEM taps word `0x1021`. -/
private def xmodemTaps : BitVec 16 :=
  0x1021#16

/-- The standard CRC check payload, ASCII `"123456789"`, as MSB-first bits, eight bits per
character. Every character of the literal is ASCII, so its low eight bits are its byte. -/
private def xmodemCheckPayload : List Bool :=
  "123456789".toList.flatMap fun c => Nat.toBitsBE 8 c.toNat

/-- The canonical modulus determines its taps word. -/
private theorem eq_of_monicModulus_eq {r : ℕ} {a b : BitVec r}
    (h : a.monicModulus = b.monicModulus) : a = b := by
  unfold BitVec.monicModulus at h
  simpa using congrArg (Polynomial.toBitVec r) (add_left_cancel h)

private theorem monicModulus_xmodemTaps : xmodemTaps.monicModulus = xmodemGenerator := by
  have h : xmodemTaps.toBoolListLE = [true, false, false, false, false, true, false, false,
      false, false, false, false, true, false, false, false] := by decide
  simp only [BitVec.monicModulus, BitVec.toPolynomial, xmodemGenerator, h]
  simp [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil]
  ring

/-- The XMODEM generator enters the serial register model through the taps word `0x1021`. -/
private theorem toBitVec_xmodemGenerator : xmodemGenerator.toBitVec 16 = xmodemTaps := by
  apply eq_of_monicModulus_eq
  rw [← monicModulus_xmodemTaps, BitVec.monicModulus_toBitVec _
    (BitVec.monicModulus_monic _) (BitVec.monicModulus_natDegree _)]

private theorem monic_xmodemGenerator : xmodemGenerator.Monic := by
  unfold xmodemGenerator
  monicity!

private theorem natDegree_xmodemGenerator : xmodemGenerator.natDegree = 16 := by
  unfold xmodemGenerator
  compute_degree!

private theorem eval_zero_xmodemGenerator : xmodemGenerator.eval 0 = 1 := by
  simp [xmodemGenerator]

/-- The CRC-16/XMODEM check value for the ASCII payload `"123456789"` is `0x31C3`. -/
example : finalRegister 16 xmodemTaps xmodemCheckPayload = 0x31C3#16 := by
  decide +kernel

/-- The transmitted XMODEM check frame is the payload followed by `0x31C3`, MSB first. -/
example :
    encodedBody 16 xmodemTaps xmodemCheckPayload =
      xmodemCheckPayload ++ Nat.toBitsBE 16 0x31C3 := by
  decide +kernel

/-- The XMODEM check payload has 72 bits, so its codeword has 88 bits. -/
example : (encodedBody 16 xmodemTaps xmodemCheckPayload).length = 88 := by
  decide +kernel

/-- A leading zero byte lengthens the payload but leaves the zero-init XMODEM check value
`0x31C3` unchanged. -/
example :
    finalRegister 16 xmodemTaps (List.replicate 8 false ++ xmodemCheckPayload) = 0x31C3#16 := by
  decide +kernel

/-- The receiver accepts the error-free XMODEM check frame. -/
example : runRegister 16 xmodemTaps (encodedBody 16 xmodemTaps xmodemCheckPayload) = 0#16 :=
  runRegister_encodedBody_eq_zero 16 xmodemTaps xmodemCheckPayload

/-- The augmented check of the error-free XMODEM check frame is zero as well. -/
example : finalRegister 16 xmodemTaps (encodedBody 16 xmodemTaps xmodemCheckPayload) = 0#16 :=
  finalRegister_encodedBody_eq_zero 16 xmodemTaps xmodemCheckPayload

/-- The length-16 error at positions `3, ..., 18` of the 88-bit check frame. -/
private def burst16 : List Bool :=
  List.replicate 3 false ++ List.replicate 16 true ++ List.replicate 69 false

private theorem isBitBurstLE_burst16 : IsBitBurstLE burst16 16 :=
  ⟨by decide +kernel, 3, by decide +kernel⟩

private theorem length_burst16 : burst16.length = xmodemCheckPayload.length + 16 := by
  decide +kernel

/-- The receiver rejects the length-16 burst, computed directly. -/
example :
    runRegister 16 xmodemTaps
        (List.zipWith Bool.xor (encodedBody 16 xmodemTaps xmodemCheckPayload) burst16) ≠
      0#16 := by
  decide +kernel

/-- The same rejection from the taps-form theorem, since `0x1021` has bit `0` set. -/
example :
    runRegister 16 xmodemTaps
        (List.zipWith Bool.xor (encodedBody 16 xmodemTaps xmodemCheckPayload) burst16) ≠
      0#16 :=
  runRegister_ne_zero_of_isBitBurstLE 16 xmodemTaps (by decide) xmodemCheckPayload burst16
    length_burst16 16 isBitBurstLE_burst16 le_rfl

/-- The augmented check rejects it as well. -/
example :
    finalRegister 16 xmodemTaps
        (List.zipWith Bool.xor (encodedBody 16 xmodemTaps xmodemCheckPayload) burst16) ≠
      0#16 :=
  finalRegister_ne_zero_of_isBitBurstLE 16 xmodemTaps (by decide) xmodemCheckPayload burst16
    length_burst16 16 isBitBurstLE_burst16 le_rfl

/-- `serialCRC_rejects_burst` at the XMODEM generator: every nonzero nonwrapping burst of length
at most `16` in an XMODEM codeword is rejected. -/
example (bits e : List Bool) (hlen : e.length = bits.length + 16) (L : ℕ)
    (he : IsBitBurstLE e L) (hL : L ≤ 16) :
    runRegister 16 xmodemTaps (List.zipWith Bool.xor (encodedBody 16 xmodemTaps bits) e) ≠
      0#16 := by
  have := serialCRC_rejects_burst xmodemGenerator 16 monic_xmodemGenerator
    natDegree_xmodemGenerator eval_zero_xmodemGenerator bits e hlen L he hL
  rwa [toBitVec_xmodemGenerator] at this

/-- `serialCRC_rejects_burst_finalRegister` at the XMODEM generator. -/
example (bits e : List Bool) (hlen : e.length = bits.length + 16) (L : ℕ)
    (he : IsBitBurstLE e L) (hL : L ≤ 16) :
    finalRegister 16 xmodemTaps (List.zipWith Bool.xor (encodedBody 16 xmodemTaps bits) e) ≠
      0#16 := by
  have := serialCRC_rejects_burst_finalRegister xmodemGenerator 16 monic_xmodemGenerator
    natDegree_xmodemGenerator eval_zero_xmodemGenerator bits e hlen L he hL
  rwa [toBitVec_xmodemGenerator] at this

/-- The bound is sharp: the 17-bit burst equal to the generator `0x11021`, at positions
`3, ..., 19` of the check frame, passes the receiver's check. -/
example :
    IsBitBurstLE (List.replicate 3 false ++ Nat.toBitsBE 17 0x11021 ++ List.replicate 68 false)
        17 ∧
      runRegister 16 xmodemTaps
        (List.zipWith Bool.xor (encodedBody 16 xmodemTaps xmodemCheckPayload)
          (List.replicate 3 false ++ Nat.toBitsBE 17 0x11021 ++ List.replicate 68 false)) =
        0#16 :=
  ⟨⟨by decide, 3, by decide +kernel⟩, by decide +kernel⟩

/-- Violated premise `g(0) = 1`: for `g = X^2 + X` (taps `0b10`), the length-2 burst `110`
(the error polynomial `X^2 + X = g`) on the codeword of the one-bit payload `0` passes the
receiver's check. -/
example :
    IsBitBurstLE [true, true, false] 2 ∧
      runRegister 2 0b10#2
          (List.zipWith Bool.xor (encodedBody 2 0b10#2 [false]) [true, true, false]) =
        0#2 :=
  ⟨⟨by decide, 0, by decide⟩, by decide⟩

/-! ### The frame parser -/

/-- Burst detection reaches the frame parser: a frame whose body is a codeword hit by a nonzero
nonwrapping burst of length at most `r` has no accepted translation, because the parser's
acceptance test is the receiver register `runRegister` on the body. -/
example (l r : ℕ) (taps : BitVec r) (h0 : taps.getLsbD 0 = true)
    (bits e : List Bool) (hbits : bits.length = l) (hlen : e.length = bits.length + r) (L : ℕ)
    (he : IsBitBurstLE e L) (hL : L ≤ r) (out : List Bool) :
    ¬(frameParser l r taps).Translates
        (FrameToken.start ::
          (List.zipWith Bool.xor (encodedBody r taps bits) e).map FrameToken.bit ++
            [FrameToken.endTok])
        out :=
  nonzeroRemainderBody_rejected l r taps _
    (by simp [encodedBody, checkBits, Nat.length_toBitsBE, hlen, hbits])
    (runRegister_ne_zero_of_isBitBurstLE r taps h0 bits e hlen L he hL) out

/-- The receiver rejects the length-16 XMODEM burst frame in the frame parser. -/
example (out : List Bool) :
    ¬(frameParser 72 16 xmodemTaps).Translates
        (FrameToken.start ::
          (List.zipWith Bool.xor (encodedBody 16 xmodemTaps xmodemCheckPayload) burst16).map
              FrameToken.bit ++
            [FrameToken.endTok])
        out :=
  nonzeroRemainderBody_rejected 72 16 xmodemTaps _ (by decide +kernel)
    (runRegister_ne_zero_of_isBitBurstLE 16 xmodemTaps (by decide) xmodemCheckPayload burst16
      length_burst16 16 isBitBurstLE_burst16 le_rfl) out

end CSLibExtTest.Coding.SerialCRCBurstDetection
