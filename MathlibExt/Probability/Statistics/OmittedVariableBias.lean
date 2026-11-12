/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sample omitted-variable formula

The long regression of `y` on `(1, x, z)` has coefficients `θ` solving its normal
equations. If `S_xx ≠ 0`, the short least-squares slope of `y` on `x` alone is
`θ 1 + θ 2 · olsSlope x z`: the long coefficient plus the omitted coefficient times the
slope of the auxiliary regression of `z` on `x`.

## Main results

* `MathlibExt.Probability.Statistics.OmittedVariableBias.olsSlope_eq_long_add_omitted`:
  slope form, `olsSlope x y = θ 1 + θ 2 * olsSlope x z`.
* `MathlibExt.Probability.Statistics.OmittedVariableBias.short_eq_long_add_omitted`: the
  same for any solution `φ` of the short normal equations (`normalEquations_iff`).

The statements reuse the finite-sample least-squares API of
`MathlibExt.Probability.FiniteProbability` (`sxy`, `olsSlope`, `designMatrix`). No rank
condition is imposed on the long design.

## References

Wooldridge, *Introductory Econometrics*, omitted-variable bias; MIT 14.32 Econometrics.
Atlas roadmap target ST01.T04.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.OmittedVariableBias

open MathlibExt.Probability.FiniteProbability

/-- Design matrix of the long regression `y i = b₀ + b₁ x i + b₂ z i + e i`, with row
`i` equal to `(1, x i, z i)` (source clause: "long regression of `y` on a constant,
`x` and `z`"). -/
noncomputable def longDesignMatrix {ι : Type*} (x z : ι → ℝ) : Matrix ι (Fin 3) ℝ :=
  Matrix.of fun i => ![1, x i, z i]

/-- `longDesignMatrix` applied to coefficients (analogue of Part A `designMatrix_mulVec`). -/
lemma longDesignMatrix_mulVec {ι : Type*} (x z : ι → ℝ) (β : Fin 3 → ℝ) :
    longDesignMatrix x z *ᵥ β = fun i => β 0 + β 1 * x i + β 2 * z i := by
  funext i
  simp [longDesignMatrix, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Rows of `Xᵀ *ᵥ v` for the long design matrix (analogue of Part A
`transpose_designMatrix_mulVec`). -/
lemma transpose_longDesignMatrix_mulVec {ι : Type*} [Fintype ι] (x z v : ι → ℝ) :
    (longDesignMatrix x z)ᵀ *ᵥ v = ![∑ i, v i, ∑ i, x i * v i, ∑ i, z i * v i] := by
  ext j
  fin_cases j <;> simp [longDesignMatrix, mulVec, dotProduct]

/-- Sample omitted-variable formula, slope form: if `θ` solves the normal equations of
the long regression of `y` on `(1, x, z)` and `S_xx ≠ 0`, the short least-squares
slope of `y` on `x` is the long coefficient `θ 1` plus the omitted coefficient `θ 2`
times the slope of the auxiliary regression of `z` on `x`. -/
theorem olsSlope_eq_long_add_omitted {ι : Type*} [Fintype ι] {x z y : ι → ℝ}
    {θ : Fin 3 → ℝ}
    (hθ : ((longDesignMatrix x z)ᵀ * longDesignMatrix x z) *ᵥ θ =
      (longDesignMatrix x z)ᵀ *ᵥ y)
    (hx : sxy x x ≠ 0) :
    olsSlope x y = θ 1 + θ 2 * olsSlope x z := by
  rw [← Matrix.mulVec_mulVec] at hθ
  have hsub : (longDesignMatrix x z)ᵀ *ᵥ (longDesignMatrix x z *ᵥ θ - y) = 0 := by
    rw [Matrix.mulVec_sub, hθ, sub_self]
  have e0 : ∑ i, ((θ 0 + θ 1 * x i + θ 2 * z i) - y i) = 0 := by
    have h := congrFun hsub 0
    simp only [transpose_longDesignMatrix_mulVec, longDesignMatrix_mulVec, Pi.sub_apply,
      Matrix.cons_val_zero, Pi.zero_apply] at h
    exact h
  have e1 : ∑ i, x i * ((θ 0 + θ 1 * x i + θ 2 * z i) - y i) = 0 := by
    have h := congrFun hsub 1
    simp only [transpose_longDesignMatrix_mulVec, longDesignMatrix_mulVec, Pi.sub_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h
    exact h
  have s0 : ∑ i, (y i - (θ 0 + θ 1 * x i + θ 2 * z i)) = 0 := by
    have hneg : (∑ i, (y i - (θ 0 + θ 1 * x i + θ 2 * z i)))
        = -∑ i, ((θ 0 + θ 1 * x i + θ 2 * z i) - y i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, e0, neg_zero]
  have s1 : ∑ i, x i * (y i - (θ 0 + θ 1 * x i + θ 2 * z i)) = 0 := by
    have hneg : (∑ i, x i * (y i - (θ 0 + θ 1 * x i + θ 2 * z i)))
        = -∑ i, x i * ((θ 0 + θ 1 * x i + θ 2 * z i) - y i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, e1, neg_zero]
  have h0' : (∑ i, y i) - (Fintype.card ι : ℝ) * θ 0 - θ 1 * (∑ i, x i)
      - θ 2 * (∑ i, z i) = 0 := by
    have per : ∀ i, y i - (θ 0 + θ 1 * x i + θ 2 * z i)
        = y i - θ 0 - θ 1 * x i - θ 2 * z i := fun i => by ring
    have h := s0
    simp only [per, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum] at h
    linarith
  have h1' : (∑ i, x i * y i) - θ 0 * (∑ i, x i) - θ 1 * (∑ i, x i * x i)
      - θ 2 * (∑ i, x i * z i) = 0 := by
    have per : ∀ i, x i * (y i - (θ 0 + θ 1 * x i + θ 2 * z i))
        = x i * y i - θ 0 * x i - θ 1 * (x i * x i) - θ 2 * (x i * z i) :=
      fun i => by ring
    have h := s1
    simp only [per, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    linarith
  have key : sxy x y = θ 1 * sxy x x + θ 2 * sxy x z := by
    have cx := card_mul_sampleMean x
    have cy := card_mul_sampleMean y
    have cz := card_mul_sampleMean z
    rw [sxy_eq_sum_mul_sub x y, sxy_eq_sum_mul_sub x x, sxy_eq_sum_mul_sub x z]
    have z : (∑ i, x i * y i) - (Fintype.card ι : ℝ) * sampleMean x * sampleMean y
          - (θ 1 * ((∑ i, x i * x i)
            - (Fintype.card ι : ℝ) * sampleMean x * sampleMean x)
            + θ 2 * ((∑ i, x i * z i)
            - (Fintype.card ι : ℝ) * sampleMean x * sampleMean z)) = 0 := by
      have e : (∑ i, x i * y i) - (Fintype.card ι : ℝ) * sampleMean x * sampleMean y
            - (θ 1 * ((∑ i, x i * x i)
              - (Fintype.card ι : ℝ) * sampleMean x * sampleMean x)
              + θ 2 * ((∑ i, x i * z i)
              - (Fintype.card ι : ℝ) * sampleMean x * sampleMean z))
          = ((∑ i, x i * y i) - θ 0 * (∑ i, x i) - θ 1 * (∑ i, x i * x i)
              - θ 2 * (∑ i, x i * z i))
            - sampleMean x * ((∑ i, y i) - (Fintype.card ι : ℝ) * θ 0
              - θ 1 * (∑ i, x i) - θ 2 * (∑ i, z i))
            - sampleMean x * ((Fintype.card ι : ℝ) * sampleMean y - (∑ i, y i))
            - θ 0 * ((Fintype.card ι : ℝ) * sampleMean x - (∑ i, x i))
            + θ 1 * sampleMean x
              * ((Fintype.card ι : ℝ) * sampleMean x - (∑ i, x i))
            + θ 2 * sampleMean x
              * ((Fintype.card ι : ℝ) * sampleMean z - (∑ i, z i)) := by ring
      rw [e, h1', h0', cy, cx, cz]
      ring
    linarith
  simp only [olsSlope, key]
  rw [div_eq_iff hx, add_mul]
  have hcancel : θ 2 * (sxy x z / sxy x x) * sxy x x = θ 2 * sxy x z := by
    rw [mul_assoc, div_mul_cancel₀ _ hx]
  rw [hcancel]

/-- Sample omitted-variable formula for any short least-squares fit: if `φ` solves the
normal equations of the short regression of `y` on `(1, x)` and `θ` those of the long
regression on `(1, x, z)`, with `S_xx ≠ 0`, then `φ 1 = θ 1 + θ 2 · olsSlope x z`
(Atlas roadmap ST01.T04). -/
theorem short_eq_long_add_omitted {ι : Type*} [Fintype ι] {x z y : ι → ℝ}
    {φ : Fin 2 → ℝ} {θ : Fin 3 → ℝ}
    (hφ : ((designMatrix x)ᵀ * designMatrix x) *ᵥ φ = (designMatrix x)ᵀ *ᵥ y)
    (hθ : ((longDesignMatrix x z)ᵀ * longDesignMatrix x z) *ᵥ θ =
      (longDesignMatrix x z)ᵀ *ᵥ y)
    (hx : sxy x x ≠ 0) :
    φ 1 = θ 1 + θ 2 * olsSlope x z := by
  rw [← Matrix.mulVec_mulVec] at hφ
  have hsub : (designMatrix x)ᵀ *ᵥ (designMatrix x *ᵥ φ - y) = 0 := by
    rw [Matrix.mulVec_sub, hφ, sub_self]
  have e0 : ∑ i, ((φ 0 + φ 1 * x i) - y i) = 0 := by
    have h := congrFun hsub 0
    simp only [transpose_designMatrix_mulVec, designMatrix_mulVec, Pi.sub_apply,
      Matrix.cons_val_zero, Pi.zero_apply] at h
    exact h
  have e1 : ∑ i, x i * ((φ 0 + φ 1 * x i) - y i) = 0 := by
    have h := congrFun hsub 1
    simp only [transpose_designMatrix_mulVec, designMatrix_mulVec, Pi.sub_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h
    exact h
  have s0 : ∑ i, (y i - (φ 0 + φ 1 * x i)) = 0 := by
    have hneg : (∑ i, (y i - (φ 0 + φ 1 * x i)))
        = -∑ i, ((φ 0 + φ 1 * x i) - y i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, e0, neg_zero]
  have s1 : ∑ i, x i * (y i - (φ 0 + φ 1 * x i)) = 0 := by
    have hneg : (∑ i, x i * (y i - (φ 0 + φ 1 * x i)))
        = -∑ i, x i * ((φ 0 + φ 1 * x i) - y i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, e1, neg_zero]
  obtain ⟨-, hφ1⟩ := (normalEquations_iff hx y (φ 0) (φ 1)).mp ⟨s0, s1⟩
  rw [hφ1]
  exact olsSlope_eq_long_add_omitted hθ hx

end MathlibExt.Probability.Statistics.OmittedVariableBias
