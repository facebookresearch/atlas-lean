/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype

/-!
# Rademacher average of a ball of linear predictors

For feature vectors `φ₁, …, φₙ` in a real inner product space, the Rademacher average of the
linear predictors `x ↦ ⟪θ, φ(x)⟫` with `‖θ‖ ≤ D` on the sample,
`E_ε sup_{‖θ‖ ≤ D} (1/n) ∑ᵢ εᵢ ⟪θ, φᵢ⟫`, is at most `(D / n) √(∑ᵢ ‖φᵢ‖²)`. When `‖φ(x)‖ ≤ R` this is
`D R / √n`, independent of the dimension, which covers balls of a reproducing kernel Hilbert space
(F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 4.5.3).

The average over the signs is written out explicitly, with the signs encoded as in
`MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype.rademacherSign`; the left-hand side is
the empirical Rademacher complexity of the ball of linear predictors on the sample.
-/

@[expose] public section

open Real
open scoped BigOperators RealInnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype (rademacherSign
  average_rademacher_norm_le)

namespace CSLibExt.MachineLearning.GeneralizationBounds

/-- **Rademacher average of a ball of linear predictors.** For vectors `φ₁, …, φₙ` of a real inner
product space and `D ≥ 0`, averaging over the `2ⁿ` sign patterns `ε`,
`E_ε sup_{‖θ‖ ≤ D} (1/n) ∑ᵢ εᵢ ⟪θ, φᵢ⟫ ≤ (D / n) √(∑ᵢ ‖φᵢ‖²)`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 4.5.3,
equation (4.16) (the computation `R_n(F) = (D / n) E‖Φ^⊤ ε‖₂ ≤ (D / n) √(E tr(Φ^⊤ Φ))`, here
conditionally on the data). Proof: Cauchy–Schwarz for the supremum over the ball, and
`E_ε ‖∑ᵢ εᵢ φᵢ‖ ≤ √(∑ᵢ ‖φᵢ‖²)`, which is
`MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype.average_rademacher_norm_le`. -/
theorem rademacher_average_linear_ball_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (φ : Fin n → E) {D : ℝ} (hD : 0 ≤ D) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        (⨆ θ : {θ : E // ‖θ‖ ≤ D}, (1 / n : ℝ) * ∑ i, rademacherSign ℝ σ i * ⟪(θ : E), φ i⟫) ≤
      D / n * √(∑ i, ‖φ i‖ ^ 2) := by
  set v : (Fin n → Bool) → E := fun σ => ∑ i, rademacherSign ℝ σ i • φ i with hv
  have : Nonempty {θ : E // ‖θ‖ ≤ D} := ⟨⟨0, by simp [hD]⟩⟩
  -- Each supremum is at most `(D / n) ‖v σ‖`.
  have hsup : ∀ σ : Fin n → Bool,
      (⨆ θ : {θ : E // ‖θ‖ ≤ D}, (1 / n : ℝ) * ∑ i, rademacherSign ℝ σ i * ⟪(θ : E), φ i⟫) ≤
        D / n * ‖v σ‖ := by
    intro σ
    refine ciSup_le fun ⟨θ, hθ⟩ => ?_
    have hinner : ∑ i, rademacherSign ℝ σ i * ⟪θ, φ i⟫ = ⟪θ, v σ⟫ := by
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right]
    simp only
    rw [hinner]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    calc (1 / n : ℝ) * ⟪θ, v σ⟫ ≤ (1 / n : ℝ) * (‖θ‖ * ‖v σ‖) :=
          mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by positivity)
      _ ≤ (1 / n : ℝ) * (D * ‖v σ‖) := by gcongr
      _ = D / n * ‖v σ‖ := by ring
  have hjensen : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, ‖v σ‖ ≤ √(∑ i, ‖φ i‖ ^ 2) :=
    average_rademacher_norm_le (𝕜 := ℝ) n φ
  calc _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, D / n * ‖v σ‖ := by
        gcongr with σ; exact hsup σ
    _ = D / n * (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, ‖v σ‖) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ D / n * √(∑ i, ‖φ i‖ ^ 2) := by gcongr

end CSLibExt.MachineLearning.GeneralizationBounds
