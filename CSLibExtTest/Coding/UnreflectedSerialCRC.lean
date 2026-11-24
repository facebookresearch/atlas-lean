/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.UnreflectedSerialCRC
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.IntervalCases

@[expose] public section

open CSLibExt.Coding.UnreflectedSerialCRC

namespace CSLibExtTest.Coding.UnreflectedSerialCRC

/-- The CRC-3 fixtures as executable bit words: payload `101`
leaves register `0b100`, `110` leaves `0b001`, and its reverse
`011` leaves `0b101`. -/
example : finalRegister 3 crc3Taps [true, false, true] = 0b100#3 :=
  final_register_crc3_payload_101_bits

example : finalRegister 3 crc3Taps [true, true, false] = 0b001#3 :=
  final_register_crc3_payload_110_bits

example : finalRegister 3 crc3Taps [false, true, true] = 0b101#3 :=
  final_register_crc3_payload_011_bits

/-- The same fixtures read as polynomials: `101` gives `X^2`. The
payload `011` is the reverse of `110`; the two reversed payloads
give different remainders (`X^2 + 1` versus `1`), as the
unreflected convention requires. -/
example : (finalRegister 3 crc3Taps [true, false, true]).toPolynomial
    = Polynomial.X ^ 2 :=
  final_register_crc3_payload_101

example : (finalRegister 3 crc3Taps [true, true, false]).toPolynomial = 1 :=
  final_register_crc3_payload_110

example : (finalRegister 3 crc3Taps [false, true, true]).toPolynomial
    ≠ (finalRegister 3 crc3Taps [true, true, false]).toPolynomial := by
  rw [final_register_crc3_payload_011, final_register_crc3_payload_110]
  intro h
  have h0 := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  simp at h0

/-- The register is exactly the encoder's check remainder: the
codeword of payload `101` is the shifted message plus the final
register polynomial `X^2`. -/
example : Cslib.CodingTheory.CRC.encode crc3Generator (messagePoly [true, false, true])
    = messagePoly [true, false, true] * Polynomial.X ^ 3 + Polynomial.X ^ 2 := by
  have hg : crc3Generator.Monic := by
    have h : (Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial (ZMod 2))
        = Polynomial.X ^ 3 + (Polynomial.X + 1) := by ring
    unfold crc3Generator
    rw [h]
    exact Polynomial.monic_X_pow_add (by compute_degree!)
  have hr : crc3Generator.natDegree = 3 := by
    unfold crc3Generator
    compute_degree!
  have h1 : crc3Generator.toBitVec 3 = crc3Taps := by
    have hgL : ∀ i, (crc3Generator.toBitVec 3).getLsbD i
        = (if i < 3 then decide (crc3Generator.coeff i = 1) else false) := by
      intro i
      unfold Polynomial.toBitVec
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
      by_cases hi : i < 3
      · simp only [hi, ite_true]
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi),
          List.getElem_ofFn (by rw [List.length_ofFn]; exact hi)]
      · simp only [hi, ite_false]
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact Nat.le_of_not_gt hi)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [hgL]
    simp only [hi, ite_true]
    interval_cases i <;>
      simp [crc3Generator, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one] <;> decide
  rw [encode_eq_messagePoly_shift_add_finalRegister crc3Generator 3 hg hr,
    h1, final_register_crc3_payload_101]

/-- Width zero: the monic generator `g = 1` has degree `0`, and both the remainder theorem
and the encoder bridge apply to it without a positive-degree hypothesis. -/
example (bits : List Bool) :
    (finalRegister 0 ((1 : Polynomial (ZMod 2)).toBitVec 0) bits).toPolynomial
      = (messagePoly bits * Polynomial.X ^ 0) %ₘ 1 :=
  final_register_represents_shifted_message_remainder_of_monic 1 0 Polynomial.monic_one
    Polynomial.natDegree_one bits

example (bits : List Bool) :
    Cslib.CodingTheory.CRC.encode (1 : Polynomial (ZMod 2)) (messagePoly bits)
      = messagePoly bits * Polynomial.X ^ 0
        + (finalRegister 0 ((1 : Polynomial (ZMod 2)).toBitVec 0) bits).toPolynomial :=
  encode_eq_messagePoly_shift_add_finalRegister 1 0 Polynomial.monic_one
    Polynomial.natDegree_one bits

/-- The CRC-3 taps word is the modulus `X^3 + X + 1`. -/
example : crc3Taps.monicModulus = Polynomial.X ^ 3 + Polynomial.X + 1 :=
  monicModulus_crc3Taps

end CSLibExtTest.Coding.UnreflectedSerialCRC
