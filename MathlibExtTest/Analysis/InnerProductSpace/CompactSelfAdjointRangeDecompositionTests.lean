/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecomposition

/-!
# Tests for the spectral theorem range decomposition

* On `ℝ`, the scalar operator `2 • 1` has dense range: the closure of its
  range is `⊤`, since the eigenspace for the eigenvalue `2` is already `⊤`.
* On `ℝ`, the zero operator has no nonzero eigenspaces: the span of its
  eigenspaces for nonzero eigenvalues is `⊥`.
* On `ℂ`, the scalar operator `3 • 1` satisfies all three conclusions of
  the spectral theorem range decomposition.
-/

open Function Set Filter Topology
open Module End
open MathlibExt.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecomposition

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecompositionTests

/-- The scalar operator `2 • 1` on `ℝ` is self-adjoint. -/
private theorem selfAdjoint_two_smul_one :
    IsSelfAdjoint (2 • (1 : ℝ →L[ℝ] ℝ)) := by
  simp [IsSelfAdjoint]

/-- The scalar operator `2 • 1` on `ℝ` is compact (its domain is
finite-dimensional). -/
private theorem compact_two_smul_one :
    IsCompactOperator ((2 • (1 : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ)) :=
  isCompactOperator_of_locallyCompactSpace_dom _

/-- On `ℝ`, the scalar operator `2 • 1` has dense range: the closure of
its range is `⊤`. -/
example : (LinearMap.range (2 • (1 : ℝ →L[ℝ] ℝ)).toLinearMap).topologicalClosure
    = ⊤ := by
  have heig : Module.End.eigenspace
      (((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) 2 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    simp
  have htop : (⨆ (μ : ℝ) (_ : μ ≠ 0),
      (Module.End.eigenspace
        (((2 • (1 : ℝ →L[ℝ] ℝ)) : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) μ :
        Submodule ℝ ℝ)) = ⊤ :=
    eq_top_iff.mpr (le_iSup_of_le 2 (le_iSup_of_le two_ne_zero (le_of_eq heig.symm)))
  obtain ⟨h1, _, _⟩ := spectral_theorem_range_decomposition
    (T := (2 • (1 : ℝ →L[ℝ] ℝ))) selfAdjoint_two_smul_one compact_two_smul_one
  rw [← h1, htop]
  simp

/-- On `ℝ`, the zero operator has no nonzero eigenspaces. -/
example : (⨆ (μ : ℝ) (_ : μ ≠ 0),
    (Module.End.eigenspace ((0 : ℝ →L[ℝ] ℝ) : Module.End ℝ ℝ) μ :
      Submodule ℝ ℝ)) = ⊥ := by
  have horth := orthogonal_iSup_eigenspaces_ne_zero_eq_ker
    (T := (0 : ℝ →L[ℝ] ℝ)) (by simp [IsSelfAdjoint])
    (isCompactOperator_of_locallyCompactSpace_dom (0 : ℝ →L[ℝ] ℝ))
  rw [show LinearMap.ker ((0 : ℝ →L[ℝ] ℝ).toLinearMap) = ⊤ by simp] at horth
  exact (Submodule.orthogonal_eq_top_iff _).mp horth

/-- On `ℂ`, the scalar operator `3 • 1` satisfies all three conclusions
of the spectral theorem range decomposition. -/
example :
    (⨆ (μ : ℂ) (_ : μ ≠ 0),
      (Module.End.eigenspace
        (((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) μ :
        Submodule ℂ ℂ)).topologicalClosure =
      (LinearMap.range ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).toLinearMap).topologicalClosure ∧
    IsCompl (LinearMap.range ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).toLinearMap).topologicalClosure
      (LinearMap.ker ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ)).toLinearMap) ∧
    OrthogonalFamily ℂ
      (fun μ : ℂ => Module.End.eigenspace
        (((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) μ)
      (fun μ => (Module.End.eigenspace
        (((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ) : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) μ).subtypeₗᵢ) :=
  spectral_theorem_range_decomposition
    (T := ((3 : ℂ) • (1 : ℂ →L[ℂ] ℂ))) (by simp [IsSelfAdjoint])
    (isCompactOperator_of_locallyCompactSpace_dom _)

end MathlibExtTest.Analysis.InnerProductSpace.CompactSelfAdjointRangeDecompositionTests
