/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Tactic.Linarith

/-!
# Purification overlap

The overlap of two purifications of finite distributions
is at most the Bhattacharyya coefficient, and the product
purifications attain it. Uhlmann's theorem for mixed
states is not included here.
-/

@[expose] public section

/-- Bhattacharyya coefficient of two finite distributions. -/
noncomputable def bhattC {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i * q i)

/-- Purification overlap bound (QCI-07 core, finite
amplitude form). If `A` and `B` are purifications of `p`
and `q` over a common environment `Fin m`, in the sense
that the row norms recover the distributions, then the
overlap is at most the Bhattacharyya coefficient. -/
theorem purification_overlap_le {n m : ℕ}
    (A B : Fin n → Fin m → ℂ) (p q : Fin n → ℝ)
    (hp : ∀ i, ∑ j, Complex.normSq (A i j) = p i)
    (hq : ∀ i, ∑ j, Complex.normSq (B i j) = q i)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) :
    ‖∑ i, ∑ j, (starRingEnd ℂ) (A i j) * B i j‖
      ≤ bhattC p q := by
  have key : ∀ i, ‖∑ j, (starRingEnd ℂ) (A i j) * B i j‖ ≤ Real.sqrt (p i * q i) := by
    intro i
    have htri : ‖∑ j, (starRingEnd ℂ) (A i j) * B i j‖ ≤ ∑ j, ‖A i j‖ * ‖B i j‖ := by
      calc ‖∑ j, (starRingEnd ℂ) (A i j) * B i j‖
          ≤ ∑ j, ‖(starRingEnd ℂ) (A i j) * B i j‖ :=
            norm_sum_le Finset.univ (fun j => (starRingEnd ℂ) (A i j) * B i j)
        _ = ∑ j, ‖A i j‖ * ‖B i j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [norm_mul, RCLike.norm_conj]
    have hA : (∑ j, ‖A i j‖ ^ 2) = p i := by
      rw [← hp i]
      apply Finset.sum_congr rfl
      intro j _
      exact (Complex.normSq_eq_norm_sq (A i j)).symm
    have hB : (∑ j, ‖B i j‖ ^ 2) = q i := by
      rw [← hq i]
      apply Finset.sum_congr rfl
      intro j _
      exact (Complex.normSq_eq_norm_sq (B i j)).symm
    have hcs : (∑ j, ‖A i j‖ * ‖B i j‖) ^ 2 ≤ p i * q i := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => ‖A i j‖) (fun j => ‖B i j‖)
      rw [hA, hB] at h
      exact h
    have hnonneg : 0 ≤ ∑ j, ‖A i j‖ * ‖B i j‖ :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc ‖∑ j, (starRingEnd ℂ) (A i j) * B i j‖
        ≤ ∑ j, ‖A i j‖ * ‖B i j‖ := htri
      _ = Real.sqrt ((∑ j, ‖A i j‖ * ‖B i j‖) ^ 2) := (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt (p i * q i) := Real.sqrt_le_sqrt hcs
  calc ‖∑ i, ∑ j, (starRingEnd ℂ) (A i j) * B i j‖
      ≤ ∑ i, ‖∑ j, (starRingEnd ℂ) (A i j) * B i j‖ :=
        norm_sum_le Finset.univ (fun i => ∑ j, (starRingEnd ℂ) (A i j) * B i j)
    _ ≤ ∑ i, Real.sqrt (p i * q i) := Finset.sum_le_sum (fun i _ => key i)
    _ = bhattC p q := rfl

/-- The bound is attained: the product purifications
`√(p i)` and `√(q i)` on a one-point environment achieve
overlap exactly `bhattC p q`. -/
theorem purification_overlap_eq {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) :
    (∑ i, ∑ _j : Fin 1, (starRingEnd ℂ)
        ((Real.sqrt (p i) : ℂ)) * (Real.sqrt (q i) : ℂ))
      = bhattC p q := by
  have per : ∀ i, (∑ _j : Fin 1, (starRingEnd ℂ) ((Real.sqrt (p i) : ℂ)) * (Real.sqrt (q i) : ℂ))
      = ((Real.sqrt (p i * q i) : ℝ) : ℂ) := by
    intro i
    rw [Fin.sum_univ_one, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (hp0 i)]
  unfold bhattC
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  exact per i

end
