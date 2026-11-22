/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceDayAction
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightSphereLaws

/-!
# Original native external right sphere module laws

The exact original sphere unit, tensorator, block braiding, full source
composition and restriction give the complete native external unit and
associativity laws. These are the literal coefficient laws used by the
canonical Day module construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory

/-- The original native epsilon and source right unitor give the entire module identity. -/
theorem sphereAction_unit
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n : OrthogonalIndex) :
    letI := OrthogonalIndex.category.{u, v}
    letI := OrthogonalIndex.monoidalCategory.{u, v}
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ◁
      orthogonalSphereMonoidalData.{u, v}.epsilon) ≫ sphereAction.{u, v} F n (𝟙_ OrthogonalIndex) ≫
        ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
      (ρ_ (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))).hom :=
  Enriched.SphereOperator.rightSphereAction_unit
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} F n

/-- Every whole native right sphere action has the exact original external associativity. -/
theorem sphereAction_assoc
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a b : OrthogonalIndex) :
    letI := OrthogonalIndex.category.{u, v}
    letI := OrthogonalIndex.monoidalCategory.{u, v}
    letI := OrthogonalIndex.symmetricCategory.{u, v}
    (α_ (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
      (PointedCGWH.orthogonalSphere.{u, v} a) (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
        (sphereAction.{u, v} F n a ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
          sphereAction.{u, v} F (n + a) b =
      (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ◁
        orthogonalSphereMonoidalData.{u, v}.mu a b) ≫ sphereAction.{u, v} F n (a + b) ≫
          ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
            (α_ n a b).inv :=
  Enriched.SphereOperator.rightSphereAction_assoc
    OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} orthogonalSphereBraidedData.{u, v} F n a b

end CategoryTheory.Spectra.OrthogonalSourceRightModule
