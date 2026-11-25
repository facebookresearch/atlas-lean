/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# Fixed-left tensoring of genuine enriched diagrams

The objects are `M ⊗ F(a)` and the full Hom action is the original F action
whiskered by M after the actual associator. The construction uses only the
closed self-enrichment of V and the given plain enriched source.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual full-Hom functor laws.
/-- Fixed-left tensoring retains the original full enriched Hom action. -/
def tensorLeft (M : V) (F : EnrichedFunctor V A V) : EnrichedFunctor V A V where
  obj a := M ⊗ F.obj a
  map a b := MonoidalClosed.curry
    ((α_ M (F.obj a) (a ⟶[V] b)).hom ≫ M ◁ MonoidalClosed.uncurry (F.map a b))
  map_id a := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
      MonoidalClosed.uncurry_curry]
    have h := congrArg MonoidalClosed.uncurry (F.map_id a)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.enrichedCategorySelf_id,
      MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, h]
    exact (rightUnitor_tensor_hom M (F.obj a)).symm
  map_comp a b c := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_eComp, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry]
    have h := congrArg MonoidalClosed.uncurry (F.map_comp a b c)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_eComp] at h
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, h]
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    symm
    rw [associator_naturality_middle_assoc, pentagon_inv_hom_hom_hom_inv_assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the original object characteristic.
/-- Tensoring keeps the literal object `M ⊗ F(a)`. -/
@[simp]
theorem tensorLeft_obj (M : V) (F : EnrichedFunctor V A V) (a : A) :
    (tensorLeft M F).obj a = M ⊗ F.obj a := rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full action characteristic.
/-- The complete Hom map uses the original F action and associator. -/
theorem tensorLeft_map (M : V) (F : EnrichedFunctor V A V) (a b : A) :
    (tensorLeft M F).map a b =
      MonoidalClosed.curry
        ((α_ M (F.obj a) (a ⟶[V] b)).hom ≫ M ◁ MonoidalClosed.uncurry (F.map a b)) := rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the uncurried action characteristic.
/-- The actual full-Hom uncurried action is left tensor of the original action. -/
theorem tensorLeft_map_uncurry (M : V) (F : EnrichedFunctor V A V) (a b : A) :
    MonoidalClosed.uncurry ((tensorLeft M F).map a b) =
      (α_ M (F.obj a) (a ⟶[V] b)).hom ≫ M ◁ MonoidalClosed.uncurry (F.map a b) := by
  exact MonoidalClosed.uncurry_curry
    ((α_ M (F.obj a) (a ⟶[V] b)).hom ≫ M ◁ MonoidalClosed.uncurry (F.map a b))

end CategoryTheory.EnrichedFunctor

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual tensor diagram.
/-- The original enriched diagram, with every value left tensored by M. -/
abbrev tensorLeftObject (M : V) (F : EnrichedFunctorCat V A) : EnrichedFunctorCat V A :=
  ⟨EnrichedFunctor.tensorLeft M F.toEnrichedFunctor⟩

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the literal object characteristic.
omit [BraidedCategory V] in
/-- Left tensoring keeps the original diagram object at the same index. -/
@[simp]
theorem tensorLeftObject_obj (M : V) (F : EnrichedFunctorCat V A) (a : A) :
    (tensorLeftObject M F).toEnrichedFunctor.obj a = M ⊗ F.toEnrichedFunctor.obj a := rfl

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the full action characteristic.
omit [BraidedCategory V] in
/-- The full action is the original action whiskered by M. -/
theorem tensorLeftObject_map_uncurry (M : V) (F : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorLeftObject M F).toEnrichedFunctor.map a b) =
      (α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) :=
  EnrichedFunctor.tensorLeft_map_uncurry M F.toEnrichedFunctor a b

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for full-Hom transformation naturality.
private theorem tensorLeftMap_naturality (M : V)
    {F G : EnrichedFunctorCat V A} (f : F ⟶ G) (a b : A) :
    MonoidalClosed.uncurry ((tensorLeftObject M F).toEnrichedFunctor.map a b) ≫
        M ◁ component f b =
      ((M ◁ component f a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((tensorLeftObject M G).toEnrichedFunctor.map a b) := by
  have h := f.uncurriedNaturality a b
  rw [tensorHom_id] at h
  rw [tensorHom_id]
  change MonoidalClosed.uncurry
      (MonoidalClosed.curry ((α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))) ≫ M ◁ component f b =
    ((M ◁ component f a) ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry
      (MonoidalClosed.curry ((α_ M (G.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b)))
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, h, whiskerLeft_comp, associator_naturality_middle_assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual tensor transformation.
/-- Left tensoring acts on actual unit-graded transformations. -/
@[no_expose]
def tensorLeftMap (M : V) {F G : EnrichedFunctorCat V A} (f : F ⟶ G) :
    tensorLeftObject M F ⟶ tensorLeftObject M G :=
  GradedNatTrans.unitOfComponents
    (fun a => M ◁ component f a) (tensorLeftMap_naturality M f)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the component characteristic.
/-- A tensored transformation has the original component whiskered by M. -/
theorem tensorLeftMap_component (M : V) {F G : EnrichedFunctorCat V A}
    (f : F ⟶ G) (a : A) :
    component (tensorLeftMap M f) a = M ◁ component f a :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for both actual functor laws.
/-- Fixed-left tensoring is a functor on genuine enriched diagrams. -/
def tensorLeft (M : V) : EnrichedFunctorCat V A ⥤ EnrichedFunctorCat V A where
  obj := tensorLeftObject M
  map := tensorLeftMap M
  map_id F := by
    apply hom_ext
    intro a
    rw [tensorLeftMap_component, component_id, component_id]
    exact whiskerLeft_id M (F.toEnrichedFunctor.obj a)
  map_comp f g := by
    apply hom_ext
    intro a
    rw [tensorLeftMap_component, component_comp, component_comp,
      tensorLeftMap_component, tensorLeftMap_component]
    exact whiskerLeft_comp M (component f a) (component g a)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the scalar full-Hom equation.
omit [BraidedCategory V] in
private theorem scalarTensorMap_naturality {M N : V} (h : M ⟶ N)
    (F : EnrichedFunctorCat V A) (a b : A) :
    MonoidalClosed.uncurry ((tensorLeftObject M F).toEnrichedFunctor.map a b) ≫
        h ▷ F.toEnrichedFunctor.obj b =
      ((h ▷ F.toEnrichedFunctor.obj a) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((tensorLeftObject N F).toEnrichedFunctor.map a b) := by
  rw [tensorHom_id]
  change MonoidalClosed.uncurry
      (MonoidalClosed.curry ((α_ M (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))) ≫
        h ▷ F.toEnrichedFunctor.obj b =
    ((h ▷ F.toEnrichedFunctor.obj a) ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry
      (MonoidalClosed.curry ((α_ N (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        N ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)))
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  simp only [Category.assoc]
  rw [whisker_exchange, associator_naturality_left_assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual scalar transformation.
/-- An actual base morphism changes the tensor parameter on the same diagram. -/
@[no_expose]
def scalarTensorMap {M N : V} (h : M ⟶ N) (F : EnrichedFunctorCat V A) :
    tensorLeftObject M F ⟶ tensorLeftObject N F :=
  GradedNatTrans.unitOfComponents
    (fun a => h ▷ F.toEnrichedFunctor.obj a) (scalarTensorMap_naturality h F)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the original scalar component.
/-- Scalar change retains the original parameter morphism and diagram object. -/
theorem scalarTensorMap_component {M N : V} (h : M ⟶ N)
    (F : EnrichedFunctorCat V A) (a : A) :
    component (scalarTensorMap h F) a = h ▷ F.toEnrichedFunctor.obj a :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the identity scalar law.
/-- The identity scalar gives the identity tensor transformation. -/
theorem scalarTensorMap_id (M : V) (F : EnrichedFunctorCat V A) :
    scalarTensorMap (𝟙 M) F = 𝟙 (tensorLeftObject M F) := by
  apply hom_ext
  intro a
  rw [scalarTensorMap_component, component_id]
  exact id_whiskerRight M (F.toEnrichedFunctor.obj a)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for source-first scalar composition.
/-- Scalar changes compose on the original tensored diagram. -/
theorem scalarTensorMap_comp {M N P : V} (h : M ⟶ N) (k : N ⟶ P)
    (F : EnrichedFunctorCat V A) :
    scalarTensorMap (h ≫ k) F = scalarTensorMap h F ≫ scalarTensorMap k F := by
  apply hom_ext
  intro a
  rw [scalarTensorMap_component, component_comp,
    scalarTensorMap_component, scalarTensorMap_component]
  exact comp_whiskerRight h k (F.toEnrichedFunctor.obj a)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for simultaneous parameter/input naturality.
/-- Scalar and genuine diagram transformations commute by tensor interchange. -/
theorem scalarTensorMap_diagram_naturality {M N : V} (h : M ⟶ N)
    {F G : EnrichedFunctorCat V A} (f : F ⟶ G) :
    tensorLeftMap M f ≫ scalarTensorMap h G =
      scalarTensorMap h F ≫ tensorLeftMap N f := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component, scalarTensorMap_component,
    component_comp, scalarTensorMap_component, tensorLeftMap_component]
  exact whisker_exchange h (component f a)

end CategoryTheory.EnrichedFunctorCat

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the exact restricted full action.
omit [BraidedCategory V] in
/-- Restriction and left tensoring retain the same complete A-Hom action. -/
theorem tensorLeftRestriction_map_uncurry (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (a b : A) :
    MonoidalClosed.uncurry
        ((tensorLeftObject M (restrictionObject j Y)).toEnrichedFunctor.map a b) =
      MonoidalClosed.uncurry
        ((restrictionObject j (tensorLeftObject M Y)).toEnrichedFunctor.map a b) := by
  change MonoidalClosed.uncurry
      (MonoidalClosed.curry ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry
          (j.map a b ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj b)))) =
    MonoidalClosed.uncurry
      (j.map a b ≫ MonoidalClosed.curry
        ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (j.obj a ⟶[V] j.obj b)).hom ≫
          M ◁ MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) (j.obj b))))
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  simp only [whiskerLeft_comp]
  rw [associator_naturality_right_assoc]

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the complete forward comparison.
private def tensorLeftRestrictionHom (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) :
    tensorLeftObject M (restrictionObject j Y) ⟶ restrictionObject j (tensorLeftObject M Y) :=
  GradedNatTrans.unitOfComponents
    (fun a => 𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a))) (by
      intro a b
      change MonoidalClosed.uncurry
          (MonoidalClosed.curry ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (a ⟶[V] b)).hom ≫
            M ◁ MonoidalClosed.uncurry
              (j.map a b ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj b)))) ≫
          𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj b)) =
        (𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry
            (j.map a b ≫ MonoidalClosed.curry
              ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (j.obj a ⟶[V] j.obj b)).hom ≫
                M ◁ MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) (j.obj b))))
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      exact tensorLeftRestriction_map_uncurry M j Y a b)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the forward component calculation.
private theorem tensorLeftRestrictionHom_component (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionHom M j Y) a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the complete inverse comparison.
private def tensorLeftRestrictionInv (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) :
    restrictionObject j (tensorLeftObject M Y) ⟶ tensorLeftObject M (restrictionObject j Y) :=
  GradedNatTrans.unitOfComponents
    (fun a => 𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a))) (by
      intro a b
      change MonoidalClosed.uncurry
          (j.map a b ≫ MonoidalClosed.curry
            ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (j.obj a ⟶[V] j.obj b)).hom ≫
              M ◁ MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) (j.obj b)))) ≫
          𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj b)) =
        (𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry
            (MonoidalClosed.curry ((α_ M (Y.toEnrichedFunctor.obj (j.obj a)) (a ⟶[V] b)).hom ≫
              M ◁ MonoidalClosed.uncurry
                (j.map a b ≫ Y.toEnrichedFunctor.map (j.obj a) (j.obj b))))
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      exact (tensorLeftRestriction_map_uncurry M j Y a b).symm)

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the inverse component calculation.
private theorem tensorLeftRestrictionInv_component (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionInv M j Y) a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  GradedNatTrans.unitOfComponents_component _ _ a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for both original identity comparisons.
/-- Restriction commutes with scalar tensoring through the original full actions. -/
@[no_expose]
def tensorLeftRestrictionIso (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) :
    tensorLeftObject M (restrictionObject j Y) ≅ restrictionObject j (tensorLeftObject M Y) where
  hom := tensorLeftRestrictionHom M j Y
  inv := tensorLeftRestrictionInv M j Y
  hom_inv_id := by
    apply hom_ext
    intro a
    rw [component_comp, tensorLeftRestrictionHom_component,
      tensorLeftRestrictionInv_component, component_id]
    exact Category.id_comp (𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)))
  inv_hom_id := by
    apply hom_ext
    intro a
    rw [component_comp, tensorLeftRestrictionInv_component,
      tensorLeftRestrictionHom_component, component_id]
    exact Category.id_comp (𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)))

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the original forward component.
/-- The restriction comparison forward map is identity on each original value. -/
theorem tensorLeftRestrictionIso_hom_component (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionIso M j Y).hom a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  tensorLeftRestrictionHom_component M j Y a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the original inverse component.
/-- The restriction comparison inverse map is identity on each original value. -/
theorem tensorLeftRestrictionIso_inv_component (M : V) (j : EnrichedFunctor V A B)
    (Y : EnrichedFunctorCat V B) (a : A) :
    component (tensorLeftRestrictionIso M j Y).inv a =
      𝟙 (M ⊗ Y.toEnrichedFunctor.obj (j.obj a)) :=
  tensorLeftRestrictionInv_component M j Y a

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for full diagram-input naturality.
/-- The exact restriction comparison is natural in every genuine transformation. -/
theorem tensorLeftRestrictionIso_naturality (M : V) (j : EnrichedFunctor V A B)
    {Y Y' : EnrichedFunctorCat V B} (f : Y ⟶ Y') :
    tensorLeftMap M (restrictionMap j f) ≫ (tensorLeftRestrictionIso M j Y').hom =
      (tensorLeftRestrictionIso M j Y).hom ≫ restrictionMap j (tensorLeftMap M f) := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component, restrictionMap_component,
    tensorLeftRestrictionIso_hom_component, component_comp,
    tensorLeftRestrictionIso_hom_component, restrictionMap_component,
    tensorLeftMap_component]
  exact (Category.comp_id (M ◁ component f (j.obj a))).trans
    (Category.id_comp (M ◁ component f (j.obj a))).symm

set_option maxHeartbeats 200000 in
-- Preserve the project proof budget for the actual scalar-input naturality.
/-- The exact restriction comparison is natural in every scalar morphism. -/
theorem tensorLeftRestrictionIso_scalar_naturality {M N : V} (h : M ⟶ N)
    (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) :
    scalarTensorMap h (restrictionObject j Y) ≫ (tensorLeftRestrictionIso N j Y).hom =
      (tensorLeftRestrictionIso M j Y).hom ≫ restrictionMap j (scalarTensorMap h Y) := by
  apply hom_ext
  intro a
  rw [component_comp, scalarTensorMap_component,
    tensorLeftRestrictionIso_hom_component, component_comp,
    tensorLeftRestrictionIso_hom_component, restrictionMap_component,
    scalarTensorMap_component]
  exact (Category.comp_id (h ▷ Y.toEnrichedFunctor.obj (j.obj a))).trans
    (Category.id_comp (h ▷ Y.toEnrichedFunctor.obj (j.obj a))).symm

end CategoryTheory.EnrichedFunctorCat
