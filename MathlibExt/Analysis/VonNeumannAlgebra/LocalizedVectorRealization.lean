/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalizedEvaluationRangeBounded
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Hilbert vector representing a projection-localized functional

Let `ψ` be a positive bounded functional on `M`, `p` a star projection, and `ξ∈H` dominate `Re
ψ` on the positive interval `0≤b≤p` by `Re ⟨ξ,bξ⟩`.

There is a vector `η∈H` with `ψ(ap)=⟨η,apξ⟩` for all `a∈M`. The construction uses a bounded
functional on the vector evaluation range and Hilbert Riesz representation. Normality of `ψ` and
a pre-supplied representing vector are not assumptions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Representing vector for a projection-localized positive functional.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M →
ℂ` be a positive bounded complex-linear functional for the spectral orders. Let `p ∈ M` be
a star projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`.
`localizedFunctionalVector M ψ p ξ` returns `η∈H` satisfying `ψ(ap)=⟨η,(ap)ξ⟩` for every
`a∈M`. The input vector need not satisfy `pξ=ξ`. -/
def localizedFunctionalVector (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (p : M) → IsStarProjection p → (ξ : H) →
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      {η : H // ∀ a : M, ψ.toContinuousLinearMap (a * p) =
        ⟪η, ((a * p : M) : H →L[ℂ] H) ξ⟫_ℂ} := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal
  let A := (localizedOperatorEvaluation M p ξ).toLinearMap
  let g := localizedEvaluationRangeBoundedFunctional M ψ p hp ξ hlocal
  let extensionExists := exists_extension_norm_eq (LinearMap.range A) g.val
  let extension : StrongDual ℂ H := Classical.choose extensionExists
  have hextension := Classical.choose_spec extensionExists
  let η : H := (InnerProductSpace.toDual ℂ H).symm extension
  refine ⟨η, ?_⟩
  intro a
  calc
    ψ.toContinuousLinearMap (a * p) = g.val (A.rangeRestrict a) := (g.property.1 a).symm
    _ = extension (A a) := (hextension.1 (A.rangeRestrict a)).symm
    _ = ⟪η, A a⟫_ℂ := (InnerProductSpace.toDual_symm_apply).symm
    _ = ⟪η, ((a * p : M) : H →L[ℂ] H) ξ⟫_ℂ := rfl

end

end VonNeumannAlgebra
