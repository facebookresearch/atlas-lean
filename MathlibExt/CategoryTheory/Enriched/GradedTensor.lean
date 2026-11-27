/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarTensor
public import MathlibExt.CategoryTheory.Enriched.GradeNaturality
public import MathlibExt.CategoryTheory.Enriched.GradedComponentActions

/-!
# Graded transformations and pointwise tensor Hom correspondences

The full Center grade and its half-braiding give inverse correspondences
between graded natural transformations and morphisms out of pointwise tensors.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the original full-Hom grade conversion.
/-- A central-graded transformation gives the actual parameter-tensored transform. -/
@[no_expose]
def gradedTensorToUnit (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) :
    tensorLeftObject Γ.1 F ⟶ G :=
  GradedNatTrans.unitOfComponents (GradedNatTrans.gradeFirstComponent Γ t) (by
    intro a b
    have hAction := tensorLeftObject_map_uncurry Γ.1 F a b
    calc
      _ = ((α_ Γ.1 (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          Γ.1 ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫
          GradedNatTrans.gradeFirstComponent Γ t b :=
        congrArg (fun q => q ≫ GradedNatTrans.gradeFirstComponent Γ t b) hAction
      _ = (α_ Γ.1 (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          Γ.1 ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫
          GradedNatTrans.gradeFirstComponent Γ t b :=
        Category.assoc _ _ _
      _ = (GradedNatTrans.gradeFirstComponent Γ t a ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) :=
        GradedNatTrans.gradeFirstComponent_naturality Γ t a b
      _ = _ := congrArg (fun q => q ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b))
        (tensorHom_id (GradedNatTrans.gradeFirstComponent Γ t a) (a ⟶[V] b)).symm)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual parameter component.
/-- The parameterized ordinary component is the original grade-first component. -/
theorem gradedTensorToUnit_component (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor) (a : A) :
    component (gradedTensorToUnit Γ t) a = GradedNatTrans.gradeFirstComponent Γ t a :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for reconstructing the complete central grade.
/-- The actual parameter-tensored transform reconstructs its raw central grade. -/
@[no_expose]
def gradedTensorOfUnit (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : tensorLeftObject Γ.1 F ⟶ G) :
    GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor :=
  GradedNatTrans.ofGradeFirstComponents Γ (component t) (by
    intro a b
    have h := t.uncurriedNaturality a b
    rw [tensorHom_id] at h
    change MonoidalClosed.uncurry
        (MonoidalClosed.curry ((α_ Γ.1 (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          Γ.1 ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))) ≫ component t b =
      (component t a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) at h
    rw [MonoidalClosed.uncurry_curry] at h
    exact (Category.assoc
      (α_ Γ.1 (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom
      (Γ.1 ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))
      (component t b)).symm.trans h)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the reconstructed parameter component.
/-- Reconstruction retains every actual grade-first component. -/
theorem gradedTensorOfUnit_gradeFirstComponent (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : tensorLeftObject Γ.1 F ⟶ G) (a : A) :
    GradedNatTrans.gradeFirstComponent Γ (gradedTensorOfUnit Γ t) a = component t a :=
  GradedNatTrans.ofGradeFirstComponents_gradeFirstComponent _ _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the complete raw inverse component.
/-- The inverse tensor correspondence retains the original half-braiding and component. -/
theorem gradedTensorOfUnit_app (Γ : Center V) {F G : EnrichedFunctorCat V A}
    (t : tensorLeftObject Γ.1 F ⟶ G) (a : A) :
    (gradedTensorOfUnit Γ t).app a =
      MonoidalClosed.curry
        ((Γ.2.β (F.toEnrichedFunctor.obj a)).inv ≫ component t a) := by
  unfold gradedTensorOfUnit
  exact GradedNatTrans.ofGradeFirstComponents_app _ _ _ _

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for both original component reconstruction laws.
/-- Raw central grading and actual fixed-left tensoring give inverse Hom correspondences. -/
def gradedTensorHomEquiv (Γ : Center V) (F G : EnrichedFunctorCat V A) :
    GradedNatTrans Γ F.toEnrichedFunctor G.toEnrichedFunctor ≃
      (tensorLeftObject Γ.1 F ⟶ G) where
  toFun := gradedTensorToUnit Γ
  invFun := gradedTensorOfUnit Γ
  left_inv t := by
    apply GradedNatTrans.gradeFirstComponent_ext Γ
    intro a
    rw [gradedTensorOfUnit_gradeFirstComponent, gradedTensorToUnit_component]
  right_inv t := by
    apply hom_ext
    intro a
    rw [gradedTensorToUnit_component, gradedTensorOfUnit_gradeFirstComponent]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for contravariant central-grade naturality.
/-- Grade reparameterization is the actual scalar tensor transformation. -/
theorem gradedTensorToUnit_regrade {Γ Γ' : Center V} (u : Γ ⟶ Γ')
    {F G : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ' F.toEnrichedFunctor G.toEnrichedFunctor) :
    gradedTensorToUnit Γ (GradedNatTrans.regrade u t) =
      scalarTensorMap u.f F ≫ gradedTensorToUnit Γ' t := by
  apply hom_ext
  intro a
  rw [gradedTensorToUnit_component, component_comp, scalarTensorMap_component,
    gradedTensorToUnit_component, GradedNatTrans.gradeFirstComponent_regrade]
  rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual tensor-unit grade comparison.
set_option backward.isDefEq.respectTransparency false in
/-- Grade-first coordinates in the tensor-unit grade retain the ordinary component. -/
theorem gradeFirstUnit_component {F G : EnrichedFunctorCat V A} (t : F ⟶ G) (a : A) :
    GradedNatTrans.gradeFirstComponent ((Center.ofBraided V).obj (𝟙_ V)) t a =
      (λ_ (F.toEnrichedFunctor.obj a)).hom ≫ component t a := by
  change (β_ (𝟙_ V) (F.toEnrichedFunctor.obj a)).hom ≫ MonoidalClosed.uncurry (t.app a) =
    (λ_ (F.toEnrichedFunctor.obj a)).hom ≫
      ((ρ_ (F.toEnrichedFunctor.obj a)).inv ≫ MonoidalClosed.uncurry (t.app a))
  rw [braiding_tensorUnit_left]
  exact Category.assoc _ _ _



/-- Reconstructing the actual tensor source composite retains every full central-grade component. -/
theorem gradedTensorOfUnit_precomp (Γ : Center V) {F' F G : EnrichedFunctorCat V A}
    (p : F' ⟶ F) (t : tensorLeftObject Γ.1 F ⟶ G) :
    gradedTensorOfUnit Γ (tensorLeftMap Γ.1 p ≫ t) =
      gradedPrecomp Γ p (gradedTensorOfUnit Γ t) := by
  apply GradedNatTrans.gradeFirstComponent_ext Γ
  intro a
  rw [gradedTensorOfUnit_gradeFirstComponent, component_comp, tensorLeftMap_component,
    gradeFirstComponent_gradedPrecomp, gradedTensorOfUnit_gradeFirstComponent]
  rfl

/-- Reconstructing the actual tensor target composite retains every full central-grade component. -/
theorem gradedTensorOfUnit_postcomp (Γ : Center V) {F G H : EnrichedFunctorCat V A}
    (t : tensorLeftObject Γ.1 F ⟶ G) (q : G ⟶ H) :
    gradedTensorOfUnit Γ (t ≫ q) = gradedPostcomp Γ (gradedTensorOfUnit Γ t) q := by
  apply GradedNatTrans.gradeFirstComponent_ext Γ
  intro a
  rw [gradedTensorOfUnit_gradeFirstComponent, component_comp,
    gradeFirstComponent_gradedPostcomp, gradedTensorOfUnit_gradeFirstComponent]
  rfl

end CategoryTheory.EnrichedFunctorCat
