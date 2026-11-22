/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.RealizedIntervalContraction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Interval

/-!
# The full SAME original interval contraction on actual native diagrams

The computed original coefficient contraction acts on every original scalar
interval cylinder through the SAME actual scalar associator and coefficient
action. Its full functor, all original input maps, zero/one endpoints and
relative fixed-source equation are proved before mapping-cylinder pushouts.
No source cofibrancy, model/SDR dictionary or colimit law is supplied.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.MonoidalCategory.IntervalContraction
universe uV vV
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/--
Tensoring an actual interval action is natural in every complete original coefficient-factor
map.
-/
private theorem tensorIntervalMap_naturality {T J X Y : V} (H : T ⊗ J ⟶ J) (f : X ⟶ Y) :
    T ◁ J ◁ f ≫ tensorIntervalMap H Y = tensorIntervalMap H X ≫ J ◁ f := by
  rw [tensorIntervalMap, tensorIntervalMap, tensorHom_id, tensorHom_id]
  calc
    T ◁ J ◁ f ≫ (α_ T J Y).inv ≫ H ▷ Y =
        (α_ T J X).inv ≫ (T ⊗ J) ◁ f ≫ H ▷ Y := by
      rw [← Category.assoc, associator_inv_naturality_right, Category.assoc]
    _ = (α_ T J X).inv ≫ H ▷ X ≫ J ◁ f := by rw [whisker_exchange]
    _ = ((α_ T J X).inv ≫ H ▷ X) ≫ J ◁ f := (Category.assoc _ _ _).symm

/--
The full original fixed-subspace tensor equation is retained after the selected inverse unit
map.
-/
private theorem tensorIntervalMap_fixed_unitor {T J X : V}
    (H : T ⊗ J ⟶ J) (e : 𝟙_ V ⟶ J) (c : T ⟶ 𝟙_ V)
    (h : (𝟙 T ⊗ₘ e) ≫ H = (c ⊗ₘ 𝟙 (𝟙_ V)) ≫ (λ_ (𝟙_ V)).hom ≫ e) :
    T ◁ ((λ_ X).inv ≫ e ▷ X) ≫ tensorIntervalMap H X =
      (c ▷ X ≫ (λ_ X).hom) ≫ (λ_ X).inv ≫ e ▷ X := by
  have hFix : T ◁ (e ▷ X) ≫ tensorIntervalMap H X =
      c ▷ ((𝟙_ V) ⊗ X) ≫ (λ_ ((𝟙_ V) ⊗ X)).hom ≫ e ▷ X := by
    simpa only [id_tensorHom, tensorHom_id] using tensorIntervalMap_fix H e c h X
  rw [whiskerLeft_comp, Category.assoc, hFix, ← Category.assoc, whisker_exchange,
    Category.assoc, leftUnitor_naturality_assoc]
  simp only [Category.assoc]

end CategoryTheory.MonoidalCategory.IntervalContraction

namespace PointedCGWH.RealizedIntervalContraction

/-- Every actual literal free-point time endpoint is a section of the SAME computed collapse. -/
theorem timeEndpoint_collapse (t : unitInterval) :
    PointedCGWH.freePointIntervalEndpoint.{u, v} t ≫
      PointedCGWH.freePointIntervalCollapse.{u, v} = 𝟙 (𝟙_ PointedCGWH.{u, v}) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let F : CGWH.{u, v} ⥤ PointedCGWH.{u, v} := Under.costar CGWH.point
  let hF : F.CoreMonoidal :=
    CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal
  change (hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint.{u, v} t)) ≫
      (F.map (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v}) ≫
        hF.εIso.inv) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (F.map (CGWH.homotopyIntervalEndpoint.{u, v} t))
    (F.map (CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v})) hF.εIso.inv,
    ← F.map_comp,
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext
      (CGWH.homotopyIntervalEndpoint.{u, v} t ≫
        CartesianMonoidalCategory.toUnit CGWH.homotopyInterval.{u, v}) (𝟙 _),
    F.map_id, Category.id_comp, Iso.hom_inv_id]

end PointedCGWH.RealizedIntervalContraction

namespace PointedCGWH.EnrichedIntervalContraction
attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The literal time tensor uses the actual freely based native time coefficient. -/
abbrev timeObject (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  tensorLeftObject PointedCGWH.RealizedIntervalContraction.time.{u, v} X

/-- The full time action is the genuine original scalar diagram functor. -/
def timeFunctor : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
    EnrichedFunctorCat PointedCGWH.{u, v} I :=
  EnrichedFunctorCat.tensorLeft PointedCGWH.RealizedIntervalContraction.time.{u, v}

/--
Each time endpoint uses the SAME original scalar inverse unitor and the actual coefficient
time endpoint.
-/
def timeInclusion (t : unitInterval) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    X ⟶ timeObject X :=
  (scalarUnitIso X).inv ≫ scalarTensorMap (PointedCGWH.freePointIntervalEndpoint.{u, v} t) X

/-- The full time projection uses the SAME original scalar unitor and actual time collapse. -/
def timeProjection (X : EnrichedFunctorCat PointedCGWH.{u, v} I) : timeObject X ⟶ X :=
  scalarTensorMap PointedCGWH.freePointIntervalCollapse.{u, v} X ≫ (scalarUnitIso X).hom

/--
Every actual time endpoint component retains the entire original scalar unitor and coefficient
map.
-/
theorem timeInclusion_component (t : unitInterval)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component (timeInclusion t X) a = (λ_ (X.toEnrichedFunctor.obj a)).inv ≫
      PointedCGWH.freePointIntervalEndpoint.{u, v} t ▷ X.toEnrichedFunctor.obj a := by
  rw [timeInclusion, component_comp, scalarUnitIso_inv_component, scalarTensorMap_component]
  rfl

/-- Every time projection component retains the actual collapse and whole original unitor. -/
theorem timeProjection_component (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component (timeProjection X) a =
      PointedCGWH.freePointIntervalCollapse.{u, v} ▷ X.toEnrichedFunctor.obj a ≫
        (λ_ (X.toEnrichedFunctor.obj a)).hom := by
  rw [timeProjection, component_comp, scalarTensorMap_component, scalarUnitIso_hom_component]
  rfl

/-- The full original time inclusion is natural in every complete native diagram morphism. -/
@[reassoc]
theorem timeInclusion_naturality (t : unitInterval)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    timeInclusion t X ≫ tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f =
      f ≫ timeInclusion t Y := by
  have hUnit : (scalarUnitIso X).inv ≫ tensorLeftMap (𝟙_ PointedCGWH.{u, v}) f =
      f ≫ (scalarUnitIso Y).inv := by
    apply (cancel_mono (scalarUnitIso Y).hom).1
    rw [Category.assoc, scalarUnitIso_naturality, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [timeInclusion, timeInclusion, Category.assoc, ← scalarTensorMap_diagram_naturality,
    ← Category.assoc, hUnit, Category.assoc]

/-- The actual full time projection is natural in every original native diagram morphism. -/
@[reassoc]
theorem timeProjection_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v} f ≫ timeProjection Y =
      timeProjection X ≫ f := by
  rw [timeProjection, timeProjection, ← Category.assoc, scalarTensorMap_diagram_naturality,
    Category.assoc, scalarUnitIso_naturality, ← Category.assoc]

/-- Every full time endpoint retracts through the SAME original actual time projection. -/
@[reassoc]
theorem timeInclusion_projection (t : unitInterval)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion t X ≫ timeProjection X = 𝟙 X := by
  rw [timeInclusion, timeProjection, Category.assoc,
    ← Category.assoc (scalarTensorMap (PointedCGWH.freePointIntervalEndpoint.{u, v} t) X)
      (scalarTensorMap PointedCGWH.freePointIntervalCollapse.{u, v} X) (scalarUnitIso X).hom,
    ← scalarTensorMap_comp, PointedCGWH.RealizedIntervalContraction.timeEndpoint_collapse,
    scalarTensorMap_id, Category.id_comp, Iso.inv_hom_id]

/--
All complete time endpoints form actual natural transformations on the whole original native
category.
-/
def timeInclusionNatTrans (t : unitInterval) :
    𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ timeFunctor where
  app X := timeInclusion t X
  naturality _ _ f := (timeInclusion_naturality t f).symm

/-- The whole actual time projection is a genuine native natural transformation. -/
def timeProjectionNatTrans : timeFunctor ⟶ 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  app X := timeProjection X
  naturality _ _ f := timeProjection_naturality f

/--
Every full original time endpoint retracts as an equality of entire native natural
transformations.
-/
theorem timeInclusion_projection_natTrans (t : unitInterval) :
    timeInclusionNatTrans (I := I) t ≫ timeProjectionNatTrans =
      𝟙 (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)) := by
  apply NatTrans.ext
  funext X
  exact timeInclusion_projection t X

/--
The contraction on the SAME original scalar cylinder is its actual inverse scalar associator
followed by the computed original coefficient action.
-/
def action (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeObject (PointedCGWH.EnrichedIntervalCylinder.object X) ⟶
      PointedCGWH.EnrichedIntervalCylinder.object X :=
  (scalarAssociatorIso PointedCGWH.RealizedIntervalContraction.time.{u, v}
    PointedCGWH.IntervalCoefficient.interval.{u, v} X).inv ≫
      scalarTensorMap PointedCGWH.RealizedIntervalContraction.action.{u, v} X

/--
Every component is the ENTIRE genuine tensor of the SAME computed original coefficient
contraction.
-/
theorem action_component (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    component (action X) a =
      tensorIntervalMap PointedCGWH.RealizedIntervalContraction.action.{u, v}
        (X.toEnrichedFunctor.obj a) := by
  rw [action, component_comp, scalarAssociatorIso_inv_component, scalarTensorMap_component,
    tensorIntervalMap, tensorHom_id]
  rfl

/--
The complete scalar contraction retains naturality in EVERY whole original native input
morphism.
-/
@[reassoc]
theorem action_naturality {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v}
      (tensorLeftMap PointedCGWH.IntervalCoefficient.interval.{u, v} f) ≫ action Y =
      action X ≫ tensorLeftMap PointedCGWH.IntervalCoefficient.interval.{u, v} f := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component, tensorLeftMap_component, action_component,
    component_comp, action_component, tensorLeftMap_component]
  exact CategoryTheory.MonoidalCategory.IntervalContraction.tensorIntervalMap_naturality
    PointedCGWH.RealizedIntervalContraction.action.{u, v} (component f a)

/--
The whole original scalar contraction is the identity at literal time zero on every original
diagram.
-/
theorem action_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 0 (PointedCGWH.EnrichedIntervalCylinder.object X) ≫ action X = 𝟙 _ := by
  apply hom_ext
  intro a
  rw [component_comp, timeInclusion_component, action_component, component_id]
  have h := tensorIntervalMap_endpoint PointedCGWH.RealizedIntervalContraction.action.{u, v}
    (PointedCGWH.freePointIntervalEndpoint.{u, v} 0) (X.toEnrichedFunctor.obj a)
  rw [PointedCGWH.RealizedIntervalContraction.action_zero, id_tensorHom_id] at h
  simpa only [tensorHom_id, PointedCGWH.EnrichedIntervalCylinder.object,
    tensorLeftObject_obj, EnrichedFunctor.tensorLeft_obj, Category.assoc] using h

/--
At literal time one, the whole scalar action is the SAME original projection followed by its
ORIGINAL first endpoint.
-/
theorem action_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 1 (PointedCGWH.EnrichedIntervalCylinder.object X) ≫ action X =
      PointedCGWH.EnrichedIntervalCylinder.projection X ≫
        PointedCGWH.EnrichedIntervalCylinder.inclusion 0 X := by
  apply hom_ext
  intro a
  rw [component_comp, timeInclusion_component, action_component, component_comp,
    PointedCGWH.EnrichedIntervalCylinder.projection_component,
    PointedCGWH.EnrichedIntervalCylinder.inclusion_component]
  have h := tensorIntervalMap_endpoint PointedCGWH.RealizedIntervalContraction.action.{u, v}
    (PointedCGWH.freePointIntervalEndpoint.{u, v} 1) (X.toEnrichedFunctor.obj a)
  rw [PointedCGWH.RealizedIntervalContraction.action_one] at h
  simpa only [tensorHom_id, comp_whiskerRight, PointedCGWH.EnrichedIntervalCylinder.object,
    tensorLeftObject_obj, EnrichedFunctor.tensorLeft_obj, Category.assoc,
    Iso.hom_inv_id_assoc] using h

/--
The full actual contraction fixes the ORIGINAL first inclusion throughout its full native time
object.
-/
theorem action_fixed (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    tensorLeftMap PointedCGWH.RealizedIntervalContraction.time.{u, v}
        (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 X) ≫ action X =
      timeProjection X ≫ PointedCGWH.EnrichedIntervalCylinder.inclusion 0 X := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component,
    PointedCGWH.EnrichedIntervalCylinder.inclusion_component, action_component,
    component_comp, timeProjection_component,
    PointedCGWH.EnrichedIntervalCylinder.inclusion_component]
  simpa only [PointedCGWH.EnrichedIntervalCylinder.object, tensorLeftObject_obj,
    EnrichedFunctor.tensorLeft_obj] using
    CategoryTheory.MonoidalCategory.IntervalContraction.tensorIntervalMap_fixed_unitor
      PointedCGWH.RealizedIntervalContraction.action.{u, v}
      (PointedCGWH.IntervalCoefficient.endpoint 0)
      PointedCGWH.freePointIntervalCollapse.{u, v}
      PointedCGWH.RealizedIntervalContraction.action_fixed.{u, v}
      (X := X.toEnrichedFunctor.obj a)

/--
The computed original contraction is a whole natural transformation on the SAME full scalar
cylinders.
-/
def actionNatTrans : PointedCGWH.EnrichedIntervalCylinder.functor ⋙ timeFunctor (I := I) ⟶
    PointedCGWH.EnrichedIntervalCylinder.functor where
  app X := action X
  naturality _ _ f := action_naturality f

end PointedCGWH.EnrichedIntervalContraction
