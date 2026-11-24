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
# Realize the original localized functional by an actual Hilbert vector

The bounded functional on the actual evaluation range has a stock
Hahn--Banach extension. Riesz duality applied to that internally obtained
extension constructs a vector with the exact original localized coefficient
values. Neither an extension, a norm certificate nor normal membership is
an input. The global order-normal criterion is a separate remaining step.
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

/-- Construct a genuine Riesz vector representing the original localized functional values. -/
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
