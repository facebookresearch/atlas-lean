/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerObjectLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallColimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Presentable.Finite

/-!
# The SAME original object forgetful functor preserves colimits and its point is compact

The existing actual codiscrete adjunction makes original object forgetting
a genuine left adjoint. The literal original point Hom readback is its
whole coyoneda functor, preserving every original object map. This proves
finite presentability of the SAME original point without a global model.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.BergnerObjects

/-- The existing actual original object-forgetting/codiscrete adjunction supplies its genuine left-adjoint structure. -/
instance forgetObjects_isLeftAdjoint : forgetObjects.{u}.IsLeftAdjoint :=
  CodiscreteEnrichment.adjunction.isLeftAdjoint

/-- The SAME complete original point Hom functor is the actual original object-forgetting functor. -/
def pointCoyonedaIso : coyoneda.obj (op point.{u}) ≅ forgetObjects.{u} :=
  NatIso.ofComponents (fun C => (pointHomEquiv C).toIso) (by
    intro C D F
    ext G
    rfl)

/-- The SAME original point is finitely presentable in the full original varying-object enriched category. -/
instance point_isFinitelyPresentable : IsFinitelyPresentable.{u} point.{u} := by
  apply isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr
  refine ⟨fun J _ _ => ?_⟩
  have : PreservesColimitsOfShape J forgetObjects.{u} := inferInstance
  exact preservesColimitsOfShape_of_natIso pointCoyonedaIso.symm

end CategoryTheory.SimplicialEnrichment.BergnerObjects
