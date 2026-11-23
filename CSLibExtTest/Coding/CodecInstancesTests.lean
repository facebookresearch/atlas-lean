/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.CodecInstances

/-!
# Tests: Hamming, CRC and Reed-Solomon codec instances
-/

@[expose] public section

open Polynomial
namespace CslibTest.CodingTheory

set_option autoImplicit false

open Cslib.CodingTheory

#print axioms Hamming74.encoding_decode_ofFn_encode_add
#print axioms CRC.encoding_decode_eq_none_of_isBurstLE
#print axioms CRC.encoding_decode_eq_none_of_single
#print axioms ReedSolomon.encoding_decode_ofFn_encode_add

/-- The Hamming(7,4) encoder on the standard example. -/
theorem hamming74_encoding_encode_example :
    Hamming74.encoding.encode ![1, 0, 1, 1] = [0, 1, 1, 0, 0, 1, 1] := by
  decide

/-- One flipped bit in a Hamming(7,4) codeword is corrected. -/
theorem hamming74_encoding_decode_example :
    Hamming74.encoding.decode [0, 1, 1, 0, 1, 1, 1] = some ![1, 0, 1, 1] := by
  decide

/-- A short word is rejected. -/
theorem hamming74_encoding_decode_short :
    Hamming74.encoding.decode [0, 1, 1] = none := by
  decide

/-- Every single-bit flip in a Hamming(7,4) codeword is corrected. -/
theorem hamming74_exhaustive_single_error :
    ∀ (m : Fin 4 → ZMod 2) (i : Fin 7),
      Hamming74.encoding.decode
        (List.ofFn (Hamming74.encode m + (fun j => if j = i then 1 else 0))) = some m := by
  decide

/-- Radius one is sharp: some weight-two error miscorrects. -/
theorem hamming74_weight_two_tightness :
    ∃ (m : Fin 4 → ZMod 2) (e : Fin 7 → ZMod 2),
      hammingNorm e = 2 ∧
        Hamming74.encoding.decode (List.ofFn (Hamming74.encode m + e)) ≠ some m := by
  decide

/-- The single-error hypothesis is satisfiable by a nonzero error. -/
theorem hamming74_single_error_satisfiable :
    ∃ e : Fin 7 → ZMod 2, e ≠ 0 ∧ hammingNorm e ≤ 1 :=
  ⟨(fun j => if j = 0 then 1 else 0), by decide, by decide⟩

/-- The `X ^ 3` coefficient of the CRC generator is `1`. -/
private theorem crc_gen_coeff_three : (X ^ 3 + X + 1 : (ZMod 2)[X]).coeff 3 = 1 := by
  rw [coeff_add, coeff_add, coeff_X_pow_self, coeff_X, coeff_one]
  simp

/-- The constant coefficient of the CRC generator is `1`. -/
private theorem crc_gen_coeff_zero : (X ^ 3 + X + 1 : (ZMod 2)[X]).coeff 0 = 1 := by
  rw [coeff_add, coeff_add, coeff_X_pow, coeff_X, coeff_one]
  simp

/-- The CRC generator `X^3 + X + 1` over `ZMod 2` is nonzero. -/
theorem crc_generator_ne_zero : (X ^ 3 + X + 1 : (ZMod 2)[X]) ≠ 0 := by
  have h3 := crc_gen_coeff_three
  intro hcon
  rw [hcon, coeff_zero] at h3
  exact zero_ne_one h3

/-- The CRC generator `X^3 + X + 1` is not divisible by `X`. -/
theorem crc_generator_not_divisible_by_X :
    ¬ (X : (ZMod 2)[X]) ∣ X ^ 3 + X + 1 := by
  rw [X_dvd_iff, crc_gen_coeff_zero]
  decide

/-- CRC round trip over `ZMod 2` with generator `X^3 + X + 1`. -/
theorem crc_roundtrip_example (hg : (X ^ 3 + X + 1 : (ZMod 2)[X]) ≠ 0) :
    (CRC.encoding (X ^ 3 + X + 1 : (ZMod 2)[X]) hg).decode
      ((CRC.encoding (X ^ 3 + X + 1 : (ZMod 2)[X]) hg).encode (X ^ 2 + 1)) =
      some (X ^ 2 + 1) :=
  (CRC.encoding _ hg).decode_encode _

/-- A burst error is detected by the CRC. -/
theorem crc_burst_detected_example
    (hg : (X ^ 3 + X + 1 : (ZMod 2)[X]) ≠ 0)
    (hX : ¬ (X : (ZMod 2)[X]) ∣ X ^ 3 + X + 1) :
    (CRC.encoding (X ^ 3 + X + 1 : (ZMod 2)[X]) hg).decode
      (CRC.encode (X ^ 3 + X + 1 : (ZMod 2)[X]) (X ^ 2 + 1) + (X + 1)).coeffList.reverse =
      none := by
  have hburst0 : (X + 1 : (ZMod 2)[X]).coeff 0 ≠ 0 := by
    have hc : (X + 1 : (ZMod 2)[X]).coeff 0 = 1 := by
      rw [coeff_add, coeff_X, coeff_one]
      simp
    rw [hc]
    decide
  have hburstdeg : (X + 1 : (ZMod 2)[X]).natDegree <
      (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree := by
    have h1 : (X + 1 : (ZMod 2)[X]).natDegree = 1 := by
      have h1c : (1 : (ZMod 2)[X]) = C 1 := C_1.symm
      rw [h1c, natDegree_X_add_C]
    have h3 : 3 ≤ (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree := by
      apply le_natDegree_of_ne_zero
      rw [crc_gen_coeff_three]
      decide
    omega
  exact CRC.encoding_decode_eq_none_of_isBurstLE hg hX _
    (⟨0, (X + 1 : (ZMod 2)[X]), by simp, hburst0, hburstdeg⟩ :
      CRC.IsBurstLE (X + 1 : (ZMod 2)[X]) (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree)

/-- A generator-multiple error is undetected (tightness). -/
theorem crc_undetected_example (hg : (X ^ 3 + X + 1 : (ZMod 2)[X]) ≠ 0) :
    (CRC.encoding (X ^ 3 + X + 1 : (ZMod 2)[X]) hg).decode
      (CRC.encode (X ^ 3 + X + 1 : (ZMod 2)[X]) (X ^ 2 + 1) +
        (X ^ 3 + X + 1)).coeffList.reverse ≠ none := by
  have hiff := CRC.encoding_decode_encode_add_eq_none_iff hg
    (X ^ 2 + 1 : (ZMod 2)[X]) (X ^ 3 + X + 1 : (ZMod 2)[X])
  exact mt hiff.mp (not_not_intro (dvd_refl (X ^ 3 + X + 1 : (ZMod 2)[X])))

/-- The single-error CRC hypotheses are satisfiable. -/
theorem crc_single_hypothesis_satisfiable :
    2 ≤ ((X ^ 3 + X + 1 : (ZMod 2)[X]).support.card) ∧ (1 : ZMod 2) ≠ 0 := by
  have h0 : 0 ∈ (X ^ 3 + X + 1 : (ZMod 2)[X]).support := by
    rw [mem_support_iff, crc_gen_coeff_zero]
    decide
  have h3 : 3 ∈ (X ^ 3 + X + 1 : (ZMod 2)[X]).support := by
    rw [mem_support_iff, crc_gen_coeff_three]
    decide
  have hcard : 1 < ((X ^ 3 + X + 1 : (ZMod 2)[X]).support.card) := by
    rw [Finset.one_lt_card]
    exact ⟨0, h0, 3, h3, by decide⟩
  exact ⟨hcard, by decide⟩

/-- A single-term error is detected by the CRC. -/
theorem crc_single_detected_example
    (hg : (X ^ 3 + X + 1 : (ZMod 2)[X]) ≠ 0)
    (h2 : 2 ≤ ((X ^ 3 + X + 1 : (ZMod 2)[X]).support.card)) :
    (CRC.encoding (X ^ 3 + X + 1 : (ZMod 2)[X]) hg).decode
      (CRC.encode (X ^ 3 + X + 1 : (ZMod 2)[X]) (X ^ 2 + 1) +
        C (1 : ZMod 2) * X ^ 0).coeffList.reverse = none :=
  CRC.encoding_decode_eq_none_of_single hg h2 _ (by decide) 0

/-- Prime fact for `Field (ZMod 5)` synthesis in the Reed-Solomon examples. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The Reed-Solomon evaluation points are injective. -/
theorem rs_injective_satisfiable :
    Function.Injective (![0, 1, 2, 3] : Fin 4 → ZMod 5) := by
  decide

/-- A degree bound for a concrete Reed-Solomon message. -/
theorem rs_degree_satisfiable : ((X + 1 : (ZMod 5)[X]).degree < 2) := by
  have h1 : (1 : (ZMod 5)[X]) = C 1 := C_1.symm
  rw [h1, degree_X_add_C]
  decide

/-- A key solver exists for the concrete Reed-Solomon parameters. -/
theorem rs_keysolver_exists
    (hα : Function.Injective (![0, 1, 2, 3] : Fin 4 → ZMod 5))
    (hkn : 2 ≤ 4) :
    Nonempty (ReedSolomon.KeySolver (![0, 1, 2, 3] : Fin 4 → ZMod 5) 2 ((4 - 2) / 2)) :=
  ⟨ReedSolomon.KeySolver.ofChoice (![0, 1, 2, 3] : Fin 4 → ZMod 5) 2 1⟩

/-- Reed-Solomon corrects one error over `ZMod 5`. -/
theorem rs_correct_one_error_example
    (hα : Function.Injective (![0, 1, 2, 3] : Fin 4 → ZMod 5))
    (hkn : 2 ≤ 4)
    (S : ReedSolomon.KeySolver (![0, 1, 2, 3] : Fin 4 → ZMod 5) 2 ((4 - 2) / 2))
    (hp : ((X + 1 : (ZMod 5)[X]).degree < 2)) :
    (ReedSolomon.encoding hα hkn S).decode
      (List.ofFn (ReedSolomon.encode (![0, 1, 2, 3] : Fin 4 → ZMod 5) (X + 1) +
        (fun j => if j = 0 then (1 : ZMod 5) else 0))) = some ⟨X + 1, hp⟩ :=
  ReedSolomon.encoding_decode_ofFn_encode_add hα hkn S
    (⟨X + 1, hp⟩ : { p : (ZMod 5)[X] // p.degree < 2 }) (by decide)

/-- Reed-Solomon rejects a beyond-radius word over `ZMod 5`. -/
theorem rs_reject_beyond_radius_example
    (hα : Function.Injective (![0, 1, 2, 3] : Fin 4 → ZMod 5))
    (hkn : 2 ≤ 4)
    (S : ReedSolomon.KeySolver (![0, 1, 2, 3] : Fin 4 → ZMod 5) 2 ((4 - 2) / 2)) :
    (ReedSolomon.encoding hα hkn S).decode
      (List.ofFn (![1, 1, 0, 0] : Fin 4 → ZMod 5)) = none := by
  rw [ReedSolomon.encoding_decode_ofFn_eq_none_iff]
  have hall : ∀ a b : ZMod 5, (4 - 2) / 2 <
      hammingDist (![1, 1, 0, 0] : Fin 4 → ZMod 5)
        (ReedSolomon.encode (![0, 1, 2, 3] : Fin 4 → ZMod 5) (C a + C b * X)) := by
    have heval : ∀ (a b : ZMod 5) (i : Fin 4),
        ReedSolomon.encode (![0, 1, 2, 3] : Fin 4 → ZMod 5) (C a + C b * X) i =
          a + b * ((![0, 1, 2, 3] : Fin 4 → ZMod 5) i) := by
      intro a b i
      show ((C a + C b * X : (ZMod 5)[X]).eval ((![0, 1, 2, 3] : Fin 4 → ZMod 5) i)) = _
      rw [eval_add, eval_C, eval_mul, eval_C, eval_X]
    simp only [hammingDist, heval]
    decide
  intro p hp
  have hnat : p.natDegree < 2 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · rw [natDegree_zero]
      decide
    · have hdeg := degree_eq_natDegree hp0
      rw [hdeg] at hp
      simpa using hp
  have hform : p = C (p.coeff 0) + C (p.coeff 1) * X := by
    ext i
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · by_cases hi1 : i = 1
      · subst hi1
        simp
      · have hi1' : 1 ≠ i := Ne.symm hi1
        have hi2 : 2 ≤ i := by omega
        have hz : p.coeff i = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hz, coeff_add, coeff_C_mul, coeff_C, coeff_X]
        simp [hi0, hi1']
  rw [hform]
  exact hall _ _

end CslibTest.CodingTheory
