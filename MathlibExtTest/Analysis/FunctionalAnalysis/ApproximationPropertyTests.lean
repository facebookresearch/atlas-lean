/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.ApproximationProperty
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.NormNum

/-!
# Tests for the approximation property

* `ℝ` and `Fin 2 → ℝ` have the approximation property (finite-dimensional
  case).
* `ℓ²(ℕ, ℂ)` has the approximation property, both via its Hilbert basis and
  via the associated Schauder basis.
* `PiLp 2 (Fin 2 → ℝ)` has the approximation property by transfer along the
  continuous linear equivalence with `Fin 2 → ℝ`.
* The range of the coordinate projection `(x, y) ↦ (x, 0)` on `ℝ × ℝ` has
  the approximation property (complemented-subspace case).
* Unpacking the definition: on the compact set `{0} ⊆ ℝ`, the identity
  itself is a finite-rank approximant.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ApproximationPropertyTests

open MathlibExt.Analysis.FunctionalAnalysis.ApproximationProperty

open scoped lp

/-- `ℝ` has the approximation property (finite-dimensional case). -/
example : HasApproximationProperty ℝ ℝ :=
  hasApproximationProperty_of_finiteDimensional ℝ

/-- `Fin 2 → ℝ` has the approximation property (finite-dimensional case). -/
example : HasApproximationProperty ℝ (Fin 2 → ℝ) :=
  hasApproximationProperty_of_finiteDimensional (Fin 2 → ℝ)

/-- `ℓ²(ℕ, ℂ)` has the approximation property via its Hilbert basis. -/
example : HasApproximationProperty ℂ (ℓ²(ℕ, ℂ)) :=
  hasApproximationProperty_of_hilbertBasis
    (default : HilbertBasis ℕ ℂ (ℓ²(ℕ, ℂ)))

/-- `ℓ²(ℕ, ℂ)` has the approximation property via the Schauder basis
associated to its Hilbert basis. -/
example : HasApproximationProperty ℂ (ℓ²(ℕ, ℂ)) :=
  hasApproximationProperty_of_schauderBasis
    (default : HilbertBasis ℕ ℂ (ℓ²(ℕ, ℂ))).toSchauderBasis

/-- `PiLp 2 (Fin 2 → ℝ)` has the approximation property by transfer along the
continuous linear equivalence with `Fin 2 → ℝ`. -/
example : HasApproximationProperty ℝ (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
  (hasApproximationProperty_of_finiteDimensional (Fin 2 → ℝ)).of_continuousLinearEquiv
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

/-- The coordinate projection `(x, y) ↦ (x, 0)` on `ℝ × ℝ` is idempotent. -/
example : ∀ x : ℝ × ℝ,
    (ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ)
      ((ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ) x)
      = (ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  rintro ⟨x, y⟩
  simp [ContinuousLinearMap.comp_apply]

/-- The range of the coordinate projection `(x, y) ↦ (x, 0)` on `ℝ × ℝ` has
the approximation property (complemented-subspace case). -/
example : HasApproximationProperty ℝ ↥(LinearMap.range
    (ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap) :=
  (hasApproximationProperty_of_finiteDimensional (ℝ × ℝ)).of_complemented
    (ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ)
    (by
      rintro ⟨x, y⟩
      simp [ContinuousLinearMap.comp_apply])
    rfl

/-- Unpacking the definition: on the compact set `{0} ⊆ ℝ`, the identity
operator is a finite-rank approximant. -/
example : ∃ T : ℝ →L[ℝ] ℝ, FiniteDimensional ℝ ↥(LinearMap.range T.toLinearMap) ∧
    ∀ x ∈ ({0} : Set ℝ), ‖T x - x‖ < 1 :=
  hasApproximationProperty_of_finiteDimensional ℝ {0} isCompact_singleton 1 one_pos

end MathlibExtTest.Analysis.FunctionalAnalysis.ApproximationPropertyTests
