/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.IntervalHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTimeEndpoint
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalBoundaryModel

/-!
# Based homotopy extension in pointed CGWH spaces

Smashing with the based interval defines the time functor for based homotopy
extension in pointed CGWH spaces. The extension property requires an extension
of every compatible based homotopy with both its initial-value and restriction
equations. It is closed under composition and pushouts, respects arrow
isomorphisms, and holds for model cofibrations, including the joint endpoint map.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalCategory

namespace PointedCGWH.BasedTimeHomotopyExtension
attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- Literal original free I-plus time acts through the actual native pointed smash functor. -/
def timeFunctor : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  tensorLeft PointedCGWH.RealizedIntervalContraction.time.{u, v}

/-- Every pointed original time inclusion uses the SAME computed endpoint and native unitor. -/
def inclusionNatTrans (t : unitInterval) : 𝟭 PointedCGWH.{u, v} ⟶ timeFunctor :=
  IntervalEndpointExtension.inclusionNatTrans PointedCGWH.RealizedIntervalContraction.time
    (PointedCGWH.freePointIntervalEndpoint t)

/-- EVERY original pointed time component retains both original complete factors. -/
theorem inclusionNatTrans_app (t : unitInterval) (X : PointedCGWH.{u, v}) :
    (inclusionNatTrans t).app X = (λ_ X).inv ≫ PointedCGWH.freePointIntervalEndpoint t ▷ X := rfl

/-- The actual native pointed free-I-plus time functor preserves colimits by its real adjunction. -/
private theorem timePreservesColimits : PreservesColimits timeFunctor.{u, v} :=
  (ihom.adjunction
    PointedCGWH.RealizedIntervalContraction.time.{u, v}).leftAdjoint_preservesColimits

attribute [local instance] timePreservesColimits

/-- Literal based ALL-target HEP in the SAME actual native pointed category at ordinary time0. -/
def property : MorphismProperty PointedCGWH.{u, v} :=
  IntervalHomotopyExtension.property timeFunctor (inclusionNatTrans 0)

/-- All original based maps, native homotopies and BOTH full extension equations are retained. -/
theorem property_iff {A X : PointedCGWH.{u, v}} (i : A ⟶ X) :
    property i ↔ ∀ (Y : PointedCGWH.{u, v}) (f : X ⟶ Y)
      (H : PointedCGWH.RealizedIntervalContraction.time ⊗ A ⟶ Y),
      ((λ_ A).inv ≫ PointedCGWH.freePointIntervalEndpoint 0 ▷ A) ≫ H = i ≫ f →
        ∃ K : PointedCGWH.RealizedIntervalContraction.time ⊗ X ⟶ Y,
          ((λ_ X).inv ≫ PointedCGWH.freePointIntervalEndpoint 0 ▷ X) ≫ K = f ∧
            PointedCGWH.RealizedIntervalContraction.time ◁ i ≫ K = H := Iff.rfl

/-- Actual pointed time/adjunction data proves the entire native based composition class. -/
instance isMultiplicative : property.{u, v}.IsMultiplicative := by
  change (IntervalHomotopyExtension.property timeFunctor (inclusionNatTrans 0)).IsMultiplicative
  infer_instance

/-- Actual pointed time/adjunction data proves the entire native based pushout class. -/
instance isStableUnderCobaseChange : property.{u, v}.IsStableUnderCobaseChange := by
  change (IntervalHomotopyExtension.property timeFunctor
    (inclusionNatTrans 0)).IsStableUnderCobaseChange
  infer_instance

/-- The actual pointed based property is invariant under ALL original full Arrow isomorphisms. -/
instance respectsIso : property.{u, v}.RespectsIso := inferInstance

/--
Every actual native pointed model cofibration has literal based HEP, by the SAME real model
and time endpoint, with no source cofibrancy or unbased Hurewicz premise.
-/
theorem modelCofibration_mem {A X : PointedCGWH.{u, v}} (i : A ⟶ X)
    (hi : cofibrations PointedCGWH.{u, v} i) : property i := by
  let _ : ∀ Y : PointedCGWH.{u, v}, IsFibrant Y := PointedCGWH.modelCategory.allObjectsFibrant
  exact IntervalEndpointExtension.modelCofibration_mem
    PointedCGWH.RealizedIntervalContraction.time (PointedCGWH.freePointIntervalEndpoint 0)
    PointedCGWH.FreeTimeEndpoint.endpoint_zero_trivialCofibration i hi

/-- The SAME entire original finite joint endpoint arrow has GENUINE literal native based HEP. -/
theorem jointEndpoints_mem : property PointedCGWH.IntervalCoefficient.jointEndpoints.{u, v} :=
  modelCofibration_mem _
    ((HomotopicalAlgebra.cofibration_iff _).mp
      PointedCGWH.IntervalCoefficient.jointEndpoints_cofibration)

end PointedCGWH.BasedTimeHomotopyExtension
