/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# The actual literal free-point time-zero map is a native trivial cofibration

The SAME original delta-one endpoint gives its genuine inherited pointed
model classes. Its underlying freely added-point map retracts onto the
original native CGWH endpoint through actual coproduct sections and folds.
The original interval comparison and the SAME chosen terminal-unit Iso
prove the literal native time-zero class. The actual costar Quillen functor
and computed original free-point monoidal unit then prove its pointed time
endpoint trivial. No HEP, stage cofibrancy, source model or group law is an
input. This is a coefficient prerequisite for actual based extension.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v uC vC
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace CategoryTheory.PointArrowCoproduct
variable {C : Type uC} [Category.{vC} C] [HasBinaryCoproducts C]

/-- The ENTIRE original point-source Arrow retract under freely added coproduct points. -/
private def fullRetract (P : C) {X : C} (f : P ⟶ X) :
    RetractArrow f (coprod.map (𝟙 P) f) where
  i := Arrow.homMk (coprod.inr : P ⟶ P ⨿ P) (coprod.inr : X ⟶ P ⨿ X) (by simp)
  r := Arrow.homMk (coprod.desc (𝟙 P) (𝟙 P)) (coprod.desc f (𝟙 X)) (by
    apply coprod.hom_ext <;> simp)
  retract := by
    apply Arrow.hom_ext <;> simp

/-- The full source section is the original second coproprojection. -/
private theorem fullRetract_i_left (P : C) {X : C} (f : P ⟶ X) :
    (fullRetract P f).i.left = (coprod.inr : P ⟶ P ⨿ P) := rfl

/-- The full target section is the original second coproprojection. -/
private theorem fullRetract_i_right (P : C) {X : C} (f : P ⟶ X) :
    (fullRetract P f).i.right = (coprod.inr : X ⟶ P ⨿ X) := rfl

/-- The full source retraction is the original fold of both point copies. -/
private theorem fullRetract_r_left (P : C) {X : C} (f : P ⟶ X) :
    (fullRetract P f).r.left = coprod.desc (𝟙 P) (𝟙 P) := rfl

/-- The full target retraction retains the original endpoint and the target identity. -/
private theorem fullRetract_r_right (P : C) {X : C} (f : P ⟶ X) :
    (fullRetract P f).r.right = coprod.desc f (𝟙 X) := rfl

/-- Both entire original Arrow maps compose to the SAME original Arrow identity. -/
private theorem fullRetract_identity (P : C) {X : C} (f : P ⟶ X) :
    (fullRetract P f).i ≫ (fullRetract P f).r = 𝟙 (Arrow.mk f) :=
  (fullRetract P f).retract

end CategoryTheory.PointArrowCoproduct

namespace CGWH.TimeEndpoint

/-- The original chosen native time-zero endpoint is an actual native CGWH trivial cofibration. -/
theorem intervalZero_trivialCofibration :
    trivialCofibrations CGWH.{u, v} CGWH.intervalZero.{u, v} := by
  let F := Under.costar CGWH.point.{u, v}
  let f := CGWH.intervalZero.{u, v}
  let g := F.map f
  have hPointed : trivialCofibrations PointedCGWH.{u, v} g := by
    have h := PointedCGWH.IntervalCoefficient.endpoint_trivialCofibration.{u, v} 1
    rw [PointedCGWH.RealizedIntervalContraction.endpoint_one_eq] at h
    exact h
  have hc : Cofibration g.right := (PointedCGWH.cofibration_iff g).mp
    ((HomotopicalAlgebra.cofibration_iff g).mpr hPointed.1)
  have hw : WeakEquivalence g.right := (PointedCGWH.weakEquivalence_iff g).mp
    ((HomotopicalAlgebra.weakEquivalence_iff g).mpr hPointed.2)
  have hRight : trivialCofibrations CGWH.{u, v} (coprod.map (𝟙 CGWH.point) f) := by
    change trivialCofibrations CGWH.{u, v} g.right
    exact ⟨(HomotopicalAlgebra.cofibration_iff _).mp hc,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp hw⟩
  exact MorphismProperty.of_retract (PointArrowCoproduct.fullRetract CGWH.point f) hRight

/-- The SAME literal native time-zero endpoint retains the actual original model class. -/
theorem endpoint_zero_trivialCofibration :
    trivialCofibrations CGWH.{u, v} (CGWH.homotopyIntervalEndpoint.{u, v} 0) := by
  let p := CGWH.point_isTerminal.{u, v}.from (𝟙_ CGWH.{u, v})
  have hp : p = CGWH.RealizedIntervalContraction.pointToUnit.{u, v}.inv :=
    CGWH.point_isTerminal.hom_ext _ _
  let _ : IsIso p := by rw [hp]; infer_instance
  have hPoint : trivialCofibrations CGWH.{u, v} p :=
    ⟨(HomotopicalAlgebra.cofibration_iff _).mp inferInstance,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance⟩
  have h : trivialCofibrations CGWH.{u, v}
      (CGWH.homotopyIntervalEndpoint.{u, v} 0 ≫
        CGWH.homotopyIntervalIsoInterval.{u, v}.hom) := by
    rw [CGWH.homotopyIntervalIsoInterval_zero]
    exact (trivialCofibrations CGWH.{u, v}).comp_mem _ _ hPoint
      intervalZero_trivialCofibration
  exact ((trivialCofibrations CGWH.{u, v}).cancel_right_of_respectsIso _ _).mp h

end CGWH.TimeEndpoint

namespace PointedCGWH.FreeTimeEndpoint

/--
The EXACT computed original free-point time-zero endpoint is a trivial cofibration in the
SAME actual native pointed model.
-/
theorem endpoint_zero_trivialCofibration :
    trivialCofibrations PointedCGWH.{u, v} (PointedCGWH.freePointIntervalEndpoint.{u, v} 0) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  change trivialCofibrations PointedCGWH.{u, v}
    (hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint.{u, v} 0))
  have hUnit : trivialCofibrations PointedCGWH.{u, v} hF.εIso.hom :=
    ⟨(HomotopicalAlgebra.cofibration_iff _).mp inferInstance,
      (HomotopicalAlgebra.weakEquivalence_iff _).mp inferInstance⟩
  have hTime : trivialCofibrations PointedCGWH.{u, v}
      (F.map (CGWH.homotopyIntervalEndpoint.{u, v} 0)) :=
    (Under.costarAdjForget_isQuillenAdjunction CGWH.point.{u, v}).preservesTrivialCofibrations
      _ CGWH.TimeEndpoint.endpoint_zero_trivialCofibration
  exact (trivialCofibrations PointedCGWH.{u, v}).comp_mem _ _ hUnit hTime

/-- The full original literal time endpoint has its SAME actual model cofibration class. -/
theorem endpoint_zero_cofibration : Cofibration (PointedCGWH.freePointIntervalEndpoint.{u, v} 0) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr endpoint_zero_trivialCofibration.1

/-- The full original literal time endpoint has its SAME actual model weak-equivalence class. -/
theorem endpoint_zero_weakEquivalence :
    WeakEquivalence (PointedCGWH.freePointIntervalEndpoint.{u, v} 0) :=
  (HomotopicalAlgebra.weakEquivalence_iff _).mpr endpoint_zero_trivialCofibration.2

end PointedCGWH.FreeTimeEndpoint
