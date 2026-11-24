/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition

@[expose] public section

open MathlibExt.Analysis.InnerProductSpace.ExactRecoveryCondition
open scoped InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.ExactRecoveryCondition

/-- Non-vacuity of the ERC step: a nonoptimal atom orthogonal to the optimal span has ERC
coefficients `0`, so every nonzero residual in the span is strictly more correlated with some
optimal atom. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : Fin 2 → E) (ψ : E)
    (hψ : ψ ∈ (Submodule.span ℝ (Set.range φ))ᗮ) {r : E}
    (hr : r ∈ Submodule.span ℝ (Set.range φ)) (hr0 : r ≠ 0) :
    ‖⟪ψ, r⟫_ℝ‖ < Finset.univ.sup' Finset.univ_nonempty (fun i => ‖⟪φ i, r⟫_ℝ‖) := by
  refine norm_inner_lt_sup'_of_erc φ ψ 0 ?_ (by simp) hr hr0
  rw [(Submodule.starProjection_apply_eq_zero_iff _).mpr hψ]
  simp

/-- The residual of a signal in the optimal span, after projecting onto the span of a subfamily,
is again in the optimal span and orthogonal to that subfamily. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : Fin 3 → E) (s : E)
    (hs : s ∈ Submodule.span ℝ (Set.range φ)) :
    s - (Submodule.span ℝ {φ 0}).starProjection s ∈ Submodule.span ℝ (Set.range φ) ∧
      ⟪φ 0, s - (Submodule.span ℝ {φ 0}).starProjection s⟫_ℝ = 0 :=
  ⟨sub_starProjection_mem (Submodule.span_mono (by simp)) hs,
    inner_sub_starProjection_eq_zero _ s (Submodule.mem_span_singleton_self _)⟩

end MathlibExtTest.Analysis.InnerProductSpace.ExactRecoveryCondition
