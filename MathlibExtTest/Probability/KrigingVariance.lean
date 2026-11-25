/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import MathlibExt.Probability.KrigingVariance

/-!
# Kriging certificate checks

Focused checks for `MathlibExt.Probability.KrigingVariance`: a
two-point identity-covariance example with numeric variance gap
`1 / 2`, the optimality and uniqueness APIs at that witness,
and a singular all-ones covariance where two different
unit-sum weights give equal variance (uniqueness needs
definiteness).

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix
open MathlibExt.Probability.KrigingVariance

/-- The two-by-two identity matrix is positive definite. -/
private lemma posDef_one_fin_two :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos Matrix.isHermitian_one
    fun x hx => ?_
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h])
  rw [Matrix.one_mulVec]
  simp only [star_trivial, dotProduct, Fin.sum_univ_two]
  rcases hne with h0 | h1
  · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 1)]
  · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0)]

/-- Two-point identity-covariance variance gap identity. -/
example : krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun i => if i = 0 then 1 else 0)
      - krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun _ => 1 / 2)
    = ((fun i => if i = 0 then (1 : ℝ) else 0) - fun _ => 1 / 2)
      ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)
        *ᵥ ((fun i => if i = 0 then (1 : ℝ) else 0) - fun _ => 1 / 2)) :=
  kriging_variance_difference (lam := 3) (by simp [Matrix.IsSymm])
    (by
      ext i
      fin_cases i <;>
        simp <;> norm_num)
    (by simp)
    (by simp)

/-- The numeric gap is `1 / 2`. -/
example : krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun i => if i = 0 then 1 else 0)
      - krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun _ => 1 / 2)
    = 1 / 2 := by
  rw [kriging_variance_difference (lam := 3) (by simp [Matrix.IsSymm])
    (by
      ext i
      fin_cases i <;>
        simp <;> norm_num)
    (by simp)
    (by simp)]
  norm_num [dotProduct, Fin.sum_univ_two]

/-- Optimality at the identity-covariance witness. -/
example : krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun _ => 1 / 2)
      ≤ krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun i => if i = 0 then 1 else 0) :=
  krigingErrorVariance_le (lam := 3) posDef_one_fin_two.posSemidef
    (by
      ext i
      fin_cases i <;>
        simp <;> norm_num)
    (by simp)
    (by simp)

/-- Uniqueness at the identity-covariance witness: an
equal-variance competitor has the same weights. -/
example {v : Fin 2 → ℝ} (hv : ∑ i, v i = 1)
    (heq : krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) v
      = krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun _ => 1 / 2)) :
    v = fun _ => 1 / 2 :=
  kriging_weights_unique (lam := 3) posDef_one_fin_two
    (by
      ext i
      fin_cases i <;>
        simp <;> norm_num)
    (by simp) hv heq

/-- Singular boundary: for the all-ones covariance, the
different unit-sum weights `(1, 0)` and `(1/2, 1/2)` have
equal variance, so uniqueness fails without definiteness. -/
example : krigingErrorVariance (0 : ℝ)
        ((fun _ _ => (1 : ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 1) (fun i => if i = 0 then 1 else 0)
      = krigingErrorVariance (0 : ℝ)
        ((fun _ _ => (1 : ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 1) (fun _ => 1 / 2)
    ∧ (fun i => if i = 0 then (1 : ℝ) else 0) ≠ (fun _ => 1 / 2) := by
  have hdiff := kriging_variance_difference (lam := 0)
    (K := ((fun _ _ => (1 : ℝ)) : Matrix (Fin 2) (Fin 2) ℝ))
    (c := fun _ => 1) (σ := 0) (w := fun _ => 1 / 2)
    (v := fun i => if i = 0 then 1 else 0)
    (by ext i j; simp [Matrix.transpose])
    (by funext i; fin_cases i <;>
      simp [Matrix.mulVec, dotProduct])
    (by simp)
    (by simp)
  have h0 : ((fun i => if i = 0 then (1 : ℝ) else 0) - fun _ => 1 / 2)
        ⬝ᵥ (((fun _ _ => (1 : ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
          *ᵥ ((fun i => if i = 0 then (1 : ℝ) else 0)
            - fun _ => 1 / 2)) = 0 := by
    norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  refine ⟨sub_eq_zero.mp (hdiff.trans h0), ?_⟩
  intro hcon
  have hc := congrFun hcon 0
  norm_num at hc
