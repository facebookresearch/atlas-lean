/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.PowerIteration
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open scoped RealInnerProductSpace
open Filter Topology MathlibExt.Analysis.InnerProductSpace.PowerIteration

namespace MathlibExtTest.Analysis.InnerProductSpace.PowerIteration

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- With a strictly dominant eigenvalue (`μ < |λ_{i₀}|`) the rescaled power iterates converge to
the dominant eigenvector. -/
example {T : E →ₗ[ℝ] E} (b : OrthonormalBasis ι ℝ E) {lam : ι → ℝ}
    (hT : ∀ j, T (b j) = lam j • b j) {i₀ : ι} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ j, j ≠ i₀ → |lam j| ≤ μ) (hdom : μ < |lam i₀|) {v₀ : E} (hc : ⟪b i₀, v₀⟫ ≠ 0) :
    Tendsto (fun k => (⟪b i₀, v₀⟫ * lam i₀ ^ k)⁻¹ • (T ^ k) v₀) atTop (𝓝 (b i₀)) := by
  have hlam : lam i₀ ≠ 0 := abs_pos.1 (hμ0.trans_lt hdom)
  have hρ : Tendsto (fun k : ℕ => (μ / |lam i₀|) ^ k * (‖v₀‖ / |⟪b i₀, v₀⟫|)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one (hμ0.trans_lt hdom)).2 hdom)).mul_const (‖v₀‖ / |⟪b i₀, v₀⟫|)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => norm_smul_pow_apply_sub_le b hT hμ0 hμ hlam hc k) hρ

/-- The Rayleigh-quotient identity for the identity operator: both sides vanish. -/
example (q v : E) :
    ⟪v, (LinearMap.id : E →ₗ[ℝ] E) v⟫ - 1 * ‖v‖ ^ 2 =
      ⟪v - q, (LinearMap.id : E →ₗ[ℝ] E) (v - q) - (1 : ℝ) • (v - q)⟫ :=
  inner_apply_sub_eq_of_eigen (fun _ _ => rfl) (by simp) v

/-- Boundary of the normalization lemma: for `y = 0` the normalized vector is `0`. -/
example (q : E) (hq : ‖q‖ = 1) : ‖‖(0 : E)‖⁻¹ • (0 : E) - q‖ ≤ 2 * ‖(0 : E) - q‖ :=
  norm_normalize_sub_le hq

end MathlibExtTest.Analysis.InnerProductSpace.PowerIteration
