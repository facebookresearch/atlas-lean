/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.SpectralConventions
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Data.Fin.VecNotation

/-!
# Symmetrical component coordinates

## i. Overview

The symmetrical components of a three-phase phasor are the
`1/3`-normalized discrete Fourier transform of the phase vector,
read at bins `(0, 2, 1)` for Mathlib's negative-exponent
`ZMod.dft`: the zero, positive and negative sequences. The
inverse transform recovers the phases, and power is preserved
up to the factor `3`. A balanced positive-sequence input has
only a positive sequence component; swapping two phases moves it
to the negative sequence.

## ii. Key results

- `sequenceVector_eq_normalizedDft_neg`: the sequence vector is
  the normalized DFT read in `(0, 2, 1)` order.
- `phaseVector_eq_dft_sequenceVector`: inversion.
- `sum_phase_mul_conj_eq_three_mul_sum_sequence`: the power
  identity.
- `balanced_positive_sequence_components`: the balanced
  positive-sequence case.

## iii. Table of contents

- A. Sequence coordinates as a DFT

## iv. References

- J. J. Grainger and W. D. Stevenson Jr., *Power System
  Analysis*, McGraw-Hill, 1994: symmetrical components of
  unbalanced systems.

## A. Sequence coordinates as a DFT
-/

@[expose] public section

namespace PhyslibExt.Circuits.SymmetricalComponentCoordinates

open ComplexConjugate
open MathlibExt.Analysis.Fourier.SpectralConventions

/-- The rotation operator `α = exp(2πi/3)`, a primitive cube root of unity. -/
noncomputable def alpha : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

/-- The abc phase quantities `(Va, Vb, Vc)` as an array on `ZMod 3`, index `0, 1, 2` for
phase `a, b, c`. -/
def phaseVector (Va Vb Vc : ℂ) : ZMod 3 → ℂ :=
  ![Va, Vb, Vc]

/-- Zero-sequence component `V0 = (Va + Vb + Vc) / 3`. -/
noncomputable def zeroSequence (Va Vb Vc : ℂ) : ℂ :=
  (Va + Vb + Vc) / 3

/-- Positive-sequence component `V1 = (Va + α Vb + α² Vc) / 3`. -/
noncomputable def positiveSequence (Va Vb Vc : ℂ) : ℂ :=
  (Va + alpha * Vb + alpha ^ 2 * Vc) / 3

/-- Negative-sequence component `V2 = (Va + α² Vb + α Vc) / 3`. -/
noncomputable def negativeSequence (Va Vb Vc : ℂ) : ℂ :=
  (Va + alpha ^ 2 * Vb + alpha * Vc) / 3

/-- The sequence components `(V0, V1, V2)` as an array on `ZMod 3`. -/
noncomputable def sequenceVector (Va Vb Vc : ℂ) : ZMod 3 → ℂ :=
  ![zeroSequence Va Vb Vc, positiveSequence Va Vb Vc, negativeSequence Va Vb Vc]

private theorem sum_ZMod3 (f : ZMod 3 → ℂ) :
    ∑ j, f j = f 0 + f 1 + f 2 := by
  rw [← (ZMod.finEquiv 3).sum_comp f, Fin.sum_univ_three]
  rfl

private theorem zmod3_cases (s : ZMod 3) : s = 0 ∨ s = 1 ∨ s = 2 := by
  have h : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  exact h s

/-- `α` is a primitive cube root of unity; in particular `α ≠ 1`. -/
lemma isPrimitiveRoot_alpha : IsPrimitiveRoot alpha 3 := by
  rw [show alpha = Complex.exp (2 * Real.pi * Complex.I / ((3 : ℕ) : ℂ)) from by
    simp [alpha]]
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- The cube roots of unity sum to zero: `1 + α + α² = 0`. -/
lemma one_add_alpha_add_alpha_sq : 1 + alpha + alpha ^ 2 = 0 := by
  have h := IsPrimitiveRoot.geom_sum_eq_zero isPrimitiveRoot_alpha (by norm_num : 1 < 3)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  exact h

private theorem conj_alpha_eq : conj alpha = alpha ^ 2 := by
  have hnorm : ‖alpha‖ = 1 := isPrimitiveRoot_alpha.norm'_eq_one (by norm_num)
  have h3 : alpha ^ 3 = 1 := isPrimitiveRoot_alpha.pow_eq_one
  have h1 : alpha * conj alpha = 1 := by
    rw [RCLike.mul_conj, hnorm]
    norm_num
  linear_combination (alpha ^ 2) * h1 - (conj alpha) * h3

private theorem conj_alpha_sq_eq : conj (alpha ^ 2) = alpha := by
  rw [map_pow, conj_alpha_eq]
  have h3 : alpha ^ 3 = 1 := isPrimitiveRoot_alpha.pow_eq_one
  linear_combination alpha * h3

/-- The DFT kernel on `ZMod 3` at `1` is `α`: `ZMod.stdAddChar 1 = α`. -/
lemma stdAddChar_one_eq_alpha : ZMod.stdAddChar (1 : ZMod 3) = alpha := by
  have h := ZMod.stdAddChar_coe (N := 3) (1 : ℤ)
  rw [Int.cast_one] at h
  unfold alpha
  rw [h]
  congr 1
  push_cast
  ring

private theorem stdAddChar_two : ZMod.stdAddChar (2 : ZMod 3) = alpha ^ 2 := by
  have h2 : (2 : ZMod 3) = 1 + 1 := by decide
  rw [h2, AddChar.map_add_eq_mul, stdAddChar_one_eq_alpha]
  ring

/-- `V0` is the `1/3`-normalized canonical DFT bin `0` of `(Va, Vb, Vc)`. -/
lemma zeroSequence_eq_normalizedDft_zero (Va Vb Vc : ℂ) :
    zeroSequence Va Vb Vc = normalizedDft (phaseVector Va Vb Vc) 0 := by
  simp only [normalizedDft, ZMod.dft_apply, sum_ZMod3]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, smul_eq_mul, one_mul,
    phaseVector]
  simp only [zeroSequence]
  push_cast
  ring

/-- `V1` is the `1/3`-normalized canonical DFT bin `2` of `(Va, Vb, Vc)`. -/
lemma positiveSequence_eq_normalizedDft_two (Va Vb Vc : ℂ) :
    positiveSequence Va Vb Vc = normalizedDft (phaseVector Va Vb Vc) 2 := by
  have e1 : (-(1 * 2) : ZMod 3) = 1 := by decide
  have e2 : (-(2 * 2) : ZMod 3) = 2 := by decide
  simp only [normalizedDft, ZMod.dft_apply, sum_ZMod3]
  simp only [zero_mul, neg_zero, e1, e2, AddChar.map_zero_eq_one,
    stdAddChar_one_eq_alpha, stdAddChar_two, smul_eq_mul, phaseVector]
  simp only [positiveSequence]
  push_cast
  ring

/-- `V2` is the `1/3`-normalized canonical DFT bin `1` of `(Va, Vb, Vc)`. -/
lemma negativeSequence_eq_normalizedDft_one (Va Vb Vc : ℂ) :
    negativeSequence Va Vb Vc = normalizedDft (phaseVector Va Vb Vc) 1 := by
  have e1 : (-(1 * 1) : ZMod 3) = 2 := by decide
  have e2 : (-(2 * 1) : ZMod 3) = 1 := by decide
  simp only [normalizedDft, ZMod.dft_apply, sum_ZMod3]
  simp only [zero_mul, neg_zero, e1, e2, AddChar.map_zero_eq_one,
    stdAddChar_one_eq_alpha, stdAddChar_two, smul_eq_mul, phaseVector]
  simp only [negativeSequence]
  push_cast
  ring

/-- **Sequence components are DFT coordinates.** The sequence array `(V0, V1, V2)` is the
`1/3`-normalized canonical length-three DFT read at bins `(0, 2, 1)`, i.e. at `-s`. -/
lemma sequenceVector_eq_normalizedDft_neg (Va Vb Vc : ℂ) :
    sequenceVector Va Vb Vc = fun s => normalizedDft (phaseVector Va Vb Vc) (-s) := by
  funext s
  rcases zmod3_cases s with rfl | rfl | rfl
  · have h0 : (-0 : ZMod 3) = 0 := neg_zero
    rw [h0]
    simpa [sequenceVector] using zeroSequence_eq_normalizedDft_zero Va Vb Vc
  · have h1 : (-1 : ZMod 3) = 2 := by decide
    rw [h1]
    simpa [sequenceVector] using positiveSequence_eq_normalizedDft_two Va Vb Vc
  · have h2 : (-2 : ZMod 3) = 1 := by decide
    rw [h2]
    simpa [sequenceVector] using negativeSequence_eq_normalizedDft_one Va Vb Vc

/-- Equivalently, the sequence array is the canonical inverse DFT of the phase array. -/
lemma sequenceVector_eq_invDFT (Va Vb Vc : ℂ) :
    sequenceVector Va Vb Vc = ZMod.dft.symm (phaseVector Va Vb Vc) := by
  rw [sequenceVector_eq_normalizedDft_neg Va Vb Vc]
  ext s
  simp [normalizedDft, ZMod.invDFT_apply', smul_eq_mul]

/-- **Inversion.** The phase array is the canonical DFT of the sequence array. -/
lemma phaseVector_eq_dft_sequenceVector (Va Vb Vc : ℂ) :
    phaseVector Va Vb Vc = ZMod.dft (sequenceVector Va Vb Vc) := by
  rw [sequenceVector_eq_invDFT]
  exact (ZMod.dft.apply_symm_apply _).symm

/-- Inversion, phase `a`: `Va = V0 + V1 + V2`. -/
lemma phaseA_eq (Va Vb Vc : ℂ) :
    Va = zeroSequence Va Vb Vc + positiveSequence Va Vb Vc + negativeSequence Va Vb Vc := by
  simp only [zeroSequence, positiveSequence, negativeSequence]
  linear_combination (-(Vb + Vc) / 3) * one_add_alpha_add_alpha_sq

/-- Inversion, phase `b`: `Vb = V0 + α² V1 + α V2`. -/
lemma phaseB_eq (Va Vb Vc : ℂ) :
    Vb = zeroSequence Va Vb Vc + alpha ^ 2 * positiveSequence Va Vb Vc +
      alpha * negativeSequence Va Vb Vc := by
  simp only [zeroSequence, positiveSequence, negativeSequence]
  linear_combination (-Va / 3) * one_add_alpha_add_alpha_sq +
    (-(2 / 3)) * (alpha - 1) * Vb * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * (alpha ^ 2 - alpha + 1) * Vc * one_add_alpha_add_alpha_sq

/-- Inversion, phase `c`: `Vc = V0 + α V1 + α² V2`. -/
lemma phaseC_eq (Va Vb Vc : ℂ) :
    Vc = zeroSequence Va Vb Vc + alpha * positiveSequence Va Vb Vc +
      alpha ^ 2 * negativeSequence Va Vb Vc := by
  simp only [zeroSequence, positiveSequence, negativeSequence]
  linear_combination (-Va / 3) * one_add_alpha_add_alpha_sq +
    (-(2 / 3)) * (alpha - 1) * Vc * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * (alpha ^ 2 - alpha + 1) * Vb * one_add_alpha_add_alpha_sq

/-- **Complex power in sequence coordinates.**
`Va conj Ia + Vb conj Ib + Vc conj Ic = 3 (V0 conj I0 + V1 conj I1 + V2 conj I2)`. -/
lemma sum_phase_mul_conj_eq_three_mul_sum_sequence (Va Vb Vc Ia Ib Ic : ℂ) :
    Va * conj Ia + Vb * conj Ib + Vc * conj Ic =
      3 * (zeroSequence Va Vb Vc * conj (zeroSequence Ia Ib Ic) +
        positiveSequence Va Vb Vc * conj (positiveSequence Ia Ib Ic) +
        negativeSequence Va Vb Vc * conj (negativeSequence Ia Ib Ic)) := by
  simp only [zeroSequence, positiveSequence, negativeSequence, map_add, map_mul,
    map_div₀, map_ofNat]
  rw [conj_alpha_eq, conj_alpha_sq_eq]
  linear_combination
    (-(1 / 3)) * Va * conj Ib * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * Va * conj Ic * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * Vb * conj Ia * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * Vc * conj Ia * one_add_alpha_add_alpha_sq +
    (-(2 / 3)) * (alpha - 1) * Vb * conj Ib * one_add_alpha_add_alpha_sq +
    (-(2 / 3)) * (alpha - 1) * Vc * conj Ic * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * (alpha ^ 2 - alpha + 1) * Vb * conj Ic * one_add_alpha_add_alpha_sq +
    (-(1 / 3)) * (alpha ^ 2 - alpha + 1) * Vc * conj Ib * one_add_alpha_add_alpha_sq

/-- The power identity as sums over `ZMod 3`. -/
lemma sum_phaseVector_mul_conj_eq (Va Vb Vc Ia Ib Ic : ℂ) :
    ∑ p : ZMod 3, phaseVector Va Vb Vc p * conj (phaseVector Ia Ib Ic p) =
      3 * ∑ s : ZMod 3, sequenceVector Va Vb Vc s * conj (sequenceVector Ia Ib Ic s) := by
  rw [sum_ZMod3, sum_ZMod3]
  simp only [phaseVector, sequenceVector]
  exact sum_phase_mul_conj_eq_three_mul_sum_sequence Va Vb Vc Ia Ib Ic

/-- Validation: the balanced positive-sequence set `(A, α² A, α A)` lands only in `V1`. -/
lemma balanced_positive_sequence_components (A : ℂ) :
    zeroSequence A (alpha ^ 2 * A) (alpha * A) = 0 ∧
      positiveSequence A (alpha ^ 2 * A) (alpha * A) = A ∧
      negativeSequence A (alpha ^ 2 * A) (alpha * A) = 0 := by
  have h3 : alpha ^ 3 = 1 := isPrimitiveRoot_alpha.pow_eq_one
  simp only [zeroSequence, positiveSequence, negativeSequence]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (A / 3) * one_add_alpha_add_alpha_sq
  · linear_combination (2 * A / 3) * h3
  · linear_combination (A / 3) * (alpha ^ 2 - alpha + 1) * one_add_alpha_add_alpha_sq

/-- Validation: the reversed phase order `(A, α A, α² A)` lands only in `V2`. -/
lemma balanced_negative_sequence_components (A : ℂ) :
    zeroSequence A (alpha * A) (alpha ^ 2 * A) = 0 ∧
      positiveSequence A (alpha * A) (alpha ^ 2 * A) = 0 ∧
      negativeSequence A (alpha * A) (alpha ^ 2 * A) = A := by
  have h3 : alpha ^ 3 = 1 := isPrimitiveRoot_alpha.pow_eq_one
  simp only [zeroSequence, positiveSequence, negativeSequence]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (A / 3) * one_add_alpha_add_alpha_sq
  · linear_combination (A / 3) * (alpha ^ 2 - alpha + 1) * one_add_alpha_add_alpha_sq
  · linear_combination (2 * A / 3) * h3

/-- Validation: reversing the phase order (`b ↔ c`) swaps `V1` and `V2`. -/
lemma positiveSequence_swap_bc (Va Vb Vc : ℂ) :
    positiveSequence Va Vc Vb = negativeSequence Va Vb Vc := by
  simp only [positiveSequence, negativeSequence]
  ring

/-- Validation: the unbalanced vector `(0, 1, 0)` has `V1 = α / 3`. -/
lemma positiveSequence_unbalanced : positiveSequence 0 1 0 = alpha / 3 := by
  simp only [positiveSequence]
  ring

/-- Validation (permutation error): the identity bin assignment `(0, 1, 2)` is wrong; on
`(0, 1, 0)`, `V1` differs from the normalized DFT bin `1`. -/
lemma positiveSequence_ne_normalizedDft_one :
    positiveSequence 0 1 0 ≠ normalizedDft (phaseVector 0 1 0) 1 := by
  rw [positiveSequence_unbalanced]
  have hRHS : normalizedDft (phaseVector 0 1 0) 1 = alpha ^ 2 / 3 := by
    have e1 : (-(1 * 1) : ZMod 3) = 2 := by decide
    have e2 : (-(2 * 1) : ZMod 3) = 1 := by decide
    simp only [normalizedDft, ZMod.dft_apply, sum_ZMod3]
    simp only [zero_mul, neg_zero, e1, e2, AddChar.map_zero_eq_one,
      stdAddChar_one_eq_alpha, stdAddChar_two, smul_eq_mul, phaseVector]
    push_cast
    ring
  rw [hRHS]
  intro h
  have h2 : alpha * (1 - alpha) = 0 := by linear_combination 3 * h
  rcases mul_eq_zero.mp h2 with h0 | h1
  · exact isPrimitiveRoot_alpha.ne_zero (by norm_num) h0
  · have hα1 : alpha = 1 := by linear_combination -h1
    exact isPrimitiveRoot_alpha.ne_one (by norm_num) hα1

end PhyslibExt.Circuits.SymmetricalComponentCoordinates
