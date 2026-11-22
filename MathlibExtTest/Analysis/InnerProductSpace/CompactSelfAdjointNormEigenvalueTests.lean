/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue

/-!
# Tests for the norm-attained eigenvalue of a compact self-adjoint operator

* On `ℝ`, the scalar operator `2 • 1` has a unit eigenvector with real
  eigenvalue exactly `2`.
* On `ℝ`, the scalar operator `(-3) • 1` has eigenvalue exactly `-3`
  (via the `HasEigenvalue` form).
* On `ℂ`, the scalar operator `3 • 1` has a unit eigenvector with real
  eigenvalue exactly `3`.
-/

open ContinuousLinearMap
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalue

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalueTests

/-- The operator `2 • 1` on `ℝ` is nonzero. -/
private theorem two_smul_one_ne_zero : (2 • (1 : ℝ →L[ℝ] ℝ)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun S : ℝ →L[ℝ] ℝ => S 1) h
  simp at h1

/-- The operator `(-3) • 1` on `ℝ` is nonzero. -/
private theorem neg_three_smul_one_ne_zero : ((-3) • (1 : ℝ →L[ℝ] ℝ)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun S : ℝ →L[ℝ] ℝ => S 1) h
  simp at h1

/-- The operator `3 • 1` on `ℂ` is nonzero. -/
private theorem three_smul_one_ne_zero : ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun S : ℂ →L[ℂ] ℂ => S 1) h
  simp at h1

/-- On `ℝ`, the scalar operator `2 • 1` has a unit eigenvector with
real eigenvalue exactly `2`. -/
example : ∃ r : ℝ, ∃ u : ℝ, ‖u‖ = 1 ∧ (2 • (1 : ℝ →L[ℝ] ℝ)) u = (r : ℝ) • u ∧
    r = 2 := by
  obtain ⟨r, u, hu1, hTu, _hr⟩ := exists_unit_eigenvector_real_eigenvalue
    (2 • (1 : ℝ →L[ℝ] ℝ)) (by simp [IsSelfAdjoint])
    (isCompactOperator_of_locallyCompactSpace_dom (2 • (1 : ℝ →L[ℝ] ℝ)))
    two_smul_one_ne_zero
  have hTapply : (2 • (1 : ℝ →L[ℝ] ℝ)) u = (2 : ℝ) • u := by simp
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, norm_zero] at hu1
    exact one_ne_zero hu1.symm
  have h1 : (r : ℝ) • u = (2 : ℝ) • u := hTu.symm.trans hTapply
  have hdiff : ((r : ℝ) - 2) • u = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp hdiff with h | h
  · have hr2 : r = 2 := sub_eq_zero.mp h
    exact ⟨r, u, hu1, by rw [hr2]; exact hTapply, hr2⟩
  · exact absurd h hu0

/-- On `ℝ`, the scalar operator `(-3) • 1` has eigenvalue exactly `-3`. -/
example : ∃ μ : ℝ, Module.End.HasEigenvalue
    (((-3) • (1 : ℝ →L[ℝ] ℝ)) : Module.End ℝ ℝ) μ ∧ μ = -3 := by
  obtain ⟨μ, _hμ0, _hnorm, heig⟩ := exists_hasEigenvalue_norm_eq
    ((-3) • (1 : ℝ →L[ℝ] ℝ)) (by simp [IsSelfAdjoint])
    (isCompactOperator_of_locallyCompactSpace_dom ((-3) • (1 : ℝ →L[ℝ] ℝ)))
    neg_three_smul_one_ne_zero
  refine ⟨μ, heig, ?_⟩
  obtain ⟨u, humem, hune⟩ := heig.exists_hasEigenvector
  have huT : ((-3) • (1 : ℝ →L[ℝ] ℝ)) u = μ • u :=
    Module.End.mem_eigenspace_iff.mp humem
  have hTapply : ((-3) • (1 : ℝ →L[ℝ] ℝ)) u = (-3 : ℝ) • u := by simp
  have hdiff : (μ - (-3 : ℝ)) • u = 0 := by
    rw [sub_smul, ← huT, hTapply, sub_self]
  rcases smul_eq_zero.mp hdiff with h | h
  · have hμ : μ = -3 := by
      have := sub_eq_zero.mp h
      linarith
    exact hμ
  · exact absurd h hune

/-- On `ℂ`, the scalar operator `3 • 1` has a unit eigenvector with
real eigenvalue exactly `3`. -/
example : ∃ r : ℝ, ∃ u : ℂ, ‖u‖ = 1 ∧
    ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) u = (r : ℂ) • u ∧ r = 3 := by
  obtain ⟨r, u, hu1, hTu, _hr⟩ := exists_unit_eigenvector_real_eigenvalue
    ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (by simp [IsSelfAdjoint])
    (isCompactOperator_of_locallyCompactSpace_dom ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)))
    three_smul_one_ne_zero
  have hTapply : ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) u = (3 : ℂ) • u := by simp
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, norm_zero] at hu1
    exact one_ne_zero hu1.symm
  have h1 : (r : ℂ) • u = (3 : ℂ) • u := hTu.symm.trans hTapply
  have hdiff : ((r : ℂ) - 3) • u = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp hdiff with h | h
  · have hr3 : r = 3 := by
      have h5 : (r : ℂ) = 3 := sub_eq_zero.mp h
      exact_mod_cast h5
    exact ⟨r, u, hu1, by rw [hr3]; exact hTapply, hr3⟩
  · exact absurd h hu0

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointNormEigenvalueTests
