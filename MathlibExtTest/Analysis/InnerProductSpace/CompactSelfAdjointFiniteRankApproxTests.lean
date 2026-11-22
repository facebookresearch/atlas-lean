/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApprox

/-!
# Tests for finite-rank approximation of compact self-adjoint operators

* On `ℝ`, the scalar operator `2 • 1` is approximated within `1 / 2` by a
  nonzero self-adjoint finite-rank operator `F` with `‖F‖ ≥ 3 / 2`.
* On `ℂ`, the scalar operator `3 • 1` is approximated within `1` by a
  self-adjoint finite-rank operator `F` with `‖F‖ ≥ 2`.
* The zero operator on `ℝ` is approximated within `1` by a self-adjoint
  finite-rank operator `F` with `‖F‖ ≤ 1`.
-/

open ContinuousLinearMap InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApprox

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApproxTests

/-- On `ℝ`, the scalar operator `2 • 1` has a nonzero self-adjoint
finite-rank approximant within `1 / 2`, of norm at least `3 / 2`. -/
example : ∃ F : ℝ →L[ℝ] ℝ, IsSelfAdjoint F ∧
    FiniteDimensional ℝ ↥(LinearMap.range (F : ℝ →ₗ[ℝ] ℝ)) ∧
    ‖((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) - F‖ ≤ 1 / 2 ∧ F ≠ 0 ∧ 3 / 2 ≤ ‖F‖ := by
  obtain ⟨F, hFsa, hFfin, hFnorm⟩ :=
    exists_finiteRank_approx (T := (2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))
      (by simp [IsSelfAdjoint])
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (show (0 : ℝ) < 1 / 2 by norm_num)
  have hTnorm : ‖((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))‖ = 2 := by simp
  have hFne : F ≠ 0 := by
    intro hF0
    rw [hF0, sub_zero, hTnorm] at hFnorm
    norm_num at hFnorm
  refine ⟨F, hFsa, hFfin, hFnorm, hFne, ?_⟩
  have htri : ‖((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))‖ ≤
      ‖((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) - F‖ + ‖F‖ := by
    conv_lhs => rw [← sub_add_cancel ((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) F]
    exact norm_add_le _ _
  rw [hTnorm] at htri
  linarith

/-- On `ℂ`, the scalar operator `3 • 1` has a self-adjoint finite-rank
approximant within `1`, of norm at least `2`. -/
example : ∃ F : ℂ →L[ℂ] ℂ, IsSelfAdjoint F ∧
    FiniteDimensional ℂ ↥(LinearMap.range (F : ℂ →ₗ[ℂ] ℂ)) ∧
    ‖((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) - F‖ ≤ 1 ∧ 2 ≤ ‖F‖ := by
  obtain ⟨F, hFsa, hFfin, hFnorm⟩ :=
    exists_finiteRank_approx (T := (3 : ℂ) • (1 : ℂ →L[ℂ] ℂ))
      (by simp [IsSelfAdjoint])
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (show (0 : ℝ) < 1 by norm_num)
  have hTnorm : ‖((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ = 3 := by simp
  refine ⟨F, hFsa, hFfin, hFnorm, ?_⟩
  have htri : ‖((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ ≤
      ‖((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) - F‖ + ‖F‖ := by
    conv_lhs => rw [← sub_add_cancel ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) F]
    exact norm_add_le _ _
  rw [hTnorm] at htri
  linarith

/-- The zero operator on `ℝ` has a self-adjoint finite-rank approximant
within `1`, of norm at most `1`. -/
example : ∃ F : ℝ →L[ℝ] ℝ, IsSelfAdjoint F ∧
    FiniteDimensional ℝ ↥(LinearMap.range (F : ℝ →ₗ[ℝ] ℝ)) ∧
    ‖(0 : ℝ →L[ℝ] ℝ) - F‖ ≤ 1 ∧ ‖F‖ ≤ 1 := by
  obtain ⟨F, hFsa, hFfin, hFnorm⟩ :=
    exists_finiteRank_approx (T := (0 : ℝ →L[ℝ] ℝ))
      (by simp [IsSelfAdjoint])
      (isCompactOperator_of_locallyCompactSpace_dom _)
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨F, hFsa, hFfin, hFnorm, ?_⟩
  rw [zero_sub, norm_neg] at hFnorm
  exact hFnorm

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFiniteRankApproxTests
