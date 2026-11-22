/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues

/-!
# Tests for finiteness of eigenvalues bounded away from zero

* The scalar operator `2 • 1` on `ℝ` has eigenvalue `2` with
  `‖2‖ ≤ ‖2 • 1‖` (the eigenvalue-norm bound).
* The scalar operator `2 • 1` on `ℝ` has exactly one eigenvalue `μ` with
  `1 ≤ ‖μ‖`, namely `μ = 2`; in particular that set is finite.
* The zero operator on `ℝ` has no eigenvalue `μ` with `1 ≤ ‖μ‖`.
* The finiteness theorem applies to the scalar operator `3 • 1` on `ℂ`.
-/

open Function Set Filter Topology
open Module End
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvalues

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvaluesTests

/-- `2` is an eigenvalue of the scalar operator `2 • 1` on `ℝ`. -/
private theorem hasEigenvalue_two_smul_one :
    Module.End.HasEigenvalue
      (((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) 2 := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  exact ⟨1, by simp, one_ne_zero⟩

/-- The eigenvalue-norm bound at the scalar operator `2 • 1` on `ℝ`. -/
example : ‖(2 : ℝ)‖ ≤ ‖((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ)‖ :=
  norm_hasEigenvalue_le hasEigenvalue_two_smul_one

/-- The scalar operator `2 • 1` on `ℝ` has exactly one eigenvalue `μ` with
`1 ≤ ‖μ‖`, namely `μ = 2`. -/
example : {μ : ℝ | Module.End.HasEigenvalue
      (((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) μ ∧ (1 : ℝ) ≤ ‖μ‖}
    = {2} := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hμ, _h1⟩
    obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
    have hxT : ((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) x = μ • x :=
      Module.End.mem_eigenspace_iff.mp hx_mem
    have h2 : (2 : ℝ) • x = μ • x := by simpa using hxT
    have hsub : ((2 : ℝ) - μ) • x = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hx_ne
  · intro h
    subst h
    exact ⟨hasEigenvalue_two_smul_one, by norm_num⟩

/-- The zero operator on `ℝ` has no eigenvalue `μ` with `1 ≤ ‖μ‖`. -/
example : {μ : ℝ | Module.End.HasEigenvalue
      ((0 : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) μ ∧ (1 : ℝ) ≤ ‖μ‖} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro μ ⟨hμ, h1⟩
  have hle := norm_hasEigenvalue_le (T := (0 : ℝ →L[ℝ] ℝ)) hμ
  simp only [norm_zero, norm_le_zero_iff] at hle
  rw [hle] at h1
  norm_num at h1

/-- The finiteness theorem applies to the scalar operator `3 • 1` on `ℂ`. -/
example : Set.Finite {μ : ℂ | Module.End.HasEigenvalue
      (((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) μ ∧
      (1 / 2 : ℝ) ≤ ‖μ‖} :=
  finite_eigenvalues_of_ge (T := ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)))
    (by simp [IsSelfAdjoint]) (isCompactOperator_of_locallyCompactSpace_dom _)
    (by norm_num)

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointFiniteEigenvaluesTests
