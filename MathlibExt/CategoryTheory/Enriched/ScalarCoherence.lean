/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarTensor

/-!
# Unit and associator for actual scalar tensoring

The genuine scalar action on enriched diagrams has the original ambient
unit and associator at every component. Full enriched-Hom naturality,
both actual inverse maps and the action unit/pentagon equations are proved
without a monoidal structure on the indexing category.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

omit [BraidedCategory V] in
private theorem pointwiseIso_inv_naturality (F G : EnrichedFunctorCat V I)
    (e : ∀ a : I, F.toEnrichedFunctor.obj a ≅ G.toEnrichedFunctor.obj a)
    (h : ∀ a b : I, MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ (e b).hom =
      ((e a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b))
    (a b : I) :
    MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b) ≫ (e b).inv =
      ((e a).inv ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  rw [tensorHom_id]
  have hForward := h a b
  rw [tensorHom_id] at hForward
  apply (cancel_epi ((e a).hom ▷ (a ⟶[V] b))).1
  have hPost := congrArg (fun q => q ≫ (e b).inv) hForward.symm
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp] using hPost

private def pointwiseIso (F G : EnrichedFunctorCat V I)
    (e : ∀ a : I, F.toEnrichedFunctor.obj a ≅ G.toEnrichedFunctor.obj a)
    (h : ∀ a b : I, MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ (e b).hom =
      ((e a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b)) :
    F ≅ G where
  hom := GradedNatTrans.unitOfComponents (fun a => (e a).hom) h
  inv := GradedNatTrans.unitOfComponents (fun a => (e a).inv)
    (pointwiseIso_inv_naturality F G e h)
  hom_inv_id := by
    apply hom_ext
    intro a
    rw [component_comp, component_id]
    dsimp only [component]
    rw [GradedNatTrans.unitOfComponents_component,
      GradedNatTrans.unitOfComponents_component, Iso.hom_inv_id]
  inv_hom_id := by
    apply hom_ext
    intro a
    rw [component_comp, component_id]
    dsimp only [component]
    rw [GradedNatTrans.unitOfComponents_component,
      GradedNatTrans.unitOfComponents_component, Iso.inv_hom_id]

private theorem pointwiseIso_hom_component (F G : EnrichedFunctorCat V I)
    (e : ∀ a : I, F.toEnrichedFunctor.obj a ≅ G.toEnrichedFunctor.obj a)
    (h : ∀ a b : I, MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ (e b).hom =
      ((e a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b))
    (a : I) : component (pointwiseIso F G e h).hom a = (e a).hom :=
  GradedNatTrans.unitOfComponents_component _ _ a

private theorem pointwiseIso_inv_component (F G : EnrichedFunctorCat V I)
    (e : ∀ a : I, F.toEnrichedFunctor.obj a ≅ G.toEnrichedFunctor.obj a)
    (h : ∀ a b : I, MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ (e b).hom =
      ((e a).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map a b))
    (a : I) : component (pointwiseIso F G e h).inv a = (e a).inv :=
  GradedNatTrans.unitOfComponents_component _ _ a

omit [BraidedCategory V] in
private theorem scalarUnit_naturality (F : EnrichedFunctorCat V I) (a b : I) :
    MonoidalClosed.uncurry ((tensorLeftObject (𝟙_ V) F).toEnrichedFunctor.map a b) ≫
        (λ_ (F.toEnrichedFunctor.obj b)).hom =
      ((λ_ (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  rw [tensorLeftObject_map_uncurry]
  change ((α_ (𝟙_ V) (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
    (𝟙_ V ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b))) ≫
      (λ_ (F.toEnrichedFunctor.obj b)).hom =
    ((λ_ (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
  rw [tensorHom_id, Category.assoc,
    leftUnitor_naturality, ← Category.assoc, ← leftUnitor_whiskerRight]

/-- The actual scalar action unit has the original ambient unitor at every source object. -/
@[no_expose]
def scalarUnitIso (F : EnrichedFunctorCat V I) : tensorLeftObject (𝟙_ V) F ≅ F :=
  pointwiseIso _ _ (fun a => λ_ (F.toEnrichedFunctor.obj a)) (scalarUnit_naturality F)

/-- The chosen scalar unit map retains the original ambient unitor. -/
theorem scalarUnitIso_hom_component (F : EnrichedFunctorCat V I) (a : I) :
    component (scalarUnitIso F).hom a = (λ_ (F.toEnrichedFunctor.obj a)).hom :=
  pointwiseIso_hom_component _ _ _ _ a

/-- The chosen scalar unit inverse retains the original ambient inverse unitor. -/
theorem scalarUnitIso_inv_component (F : EnrichedFunctorCat V I) (a : I) :
    component (scalarUnitIso F).inv a = (λ_ (F.toEnrichedFunctor.obj a)).inv :=
  pointwiseIso_inv_component _ _ _ _ a

/-- Scalar action unit maps are natural in the full genuine diagram transformation. -/
theorem scalarUnitIso_naturality {F G : EnrichedFunctorCat V I} (f : F ⟶ G) :
    tensorLeftMap (𝟙_ V) f ≫ (scalarUnitIso G).hom = (scalarUnitIso F).hom ≫ f := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component, scalarUnitIso_hom_component,
    component_comp, scalarUnitIso_hom_component]
  exact leftUnitor_naturality (component f a)

set_option backward.isDefEq.respectTransparency false in
omit [BraidedCategory V] in
private theorem scalarAssociator_naturality (M N : V) (F : EnrichedFunctorCat V I)
    (a b : I) :
    MonoidalClosed.uncurry ((tensorLeftObject (M ⊗ N) F).toEnrichedFunctor.map a b) ≫
        (α_ M N (F.toEnrichedFunctor.obj b)).hom =
      ((α_ M N (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry
          ((tensorLeftObject M (tensorLeftObject N F)).toEnrichedFunctor.map a b) := by
  rw [tensorLeftObject_map_uncurry]
  change ((α_ (M ⊗ N) (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
    (M ⊗ N) ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫
      (α_ M N (F.toEnrichedFunctor.obj b)).hom =
    ((α_ M N (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry
        ((tensorLeftObject M (tensorLeftObject N F)).toEnrichedFunctor.map a b)
  rw [tensorLeftObject_map_uncurry]
  change ((α_ (M ⊗ N) (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
    (M ⊗ N) ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)) ≫
      (α_ M N (F.toEnrichedFunctor.obj b)).hom =
    ((α_ M N (F.toEnrichedFunctor.obj a)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      ((α_ M (N ⊗ F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ MonoidalClosed.uncurry ((tensorLeftObject N F).toEnrichedFunctor.map a b))
  rw [tensorLeftObject_map_uncurry, tensorHom_id, whiskerLeft_comp]
  simp only [Category.assoc]
  change (α_ (M ⊗ N) (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
    (M ⊗ N) ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫
      (α_ M N (F.toEnrichedFunctor.obj b)).hom =
    ((α_ M N (F.toEnrichedFunctor.obj a)).hom ▷ (a ⟶[V] b)) ≫
      (α_ M (N ⊗ F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
        M ◁ (α_ N (F.toEnrichedFunctor.obj a) (a ⟶[V] b)).hom ≫
          M ◁ N ◁ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
  rw [associator_naturality_right]
  rw [reassoc_of% (pentagon M N (F.toEnrichedFunctor.obj a) (a ⟶[V] b))]

/-- The actual scalar action associator retains the original ambient associator everywhere. -/
@[no_expose]
def scalarAssociatorIso (M N : V) (F : EnrichedFunctorCat V I) :
    tensorLeftObject (M ⊗ N) F ≅ tensorLeftObject M (tensorLeftObject N F) :=
  pointwiseIso _ _ (fun a => α_ M N (F.toEnrichedFunctor.obj a))
    (scalarAssociator_naturality M N F)

/-- The chosen scalar associator map is the original ambient associator on every value. -/
theorem scalarAssociatorIso_hom_component (M N : V) (F : EnrichedFunctorCat V I) (a : I) :
    component (scalarAssociatorIso M N F).hom a = (α_ M N (F.toEnrichedFunctor.obj a)).hom :=
  pointwiseIso_hom_component _ _ _ _ a

/-- The chosen scalar associator inverse is the original ambient inverse on every value. -/
theorem scalarAssociatorIso_inv_component (M N : V) (F : EnrichedFunctorCat V I) (a : I) :
    component (scalarAssociatorIso M N F).inv a = (α_ M N (F.toEnrichedFunctor.obj a)).inv :=
  pointwiseIso_inv_component _ _ _ _ a

/-- Scalar associators commute with every genuine diagram transformation. -/
theorem scalarAssociatorIso_naturality (M N : V)
    {F G : EnrichedFunctorCat V I} (f : F ⟶ G) :
    tensorLeftMap (M ⊗ N) f ≫ (scalarAssociatorIso M N G).hom =
      (scalarAssociatorIso M N F).hom ≫ tensorLeftMap M (tensorLeftMap N f) := by
  apply hom_ext
  intro a
  rw [component_comp, tensorLeftMap_component, scalarAssociatorIso_hom_component,
    component_comp, scalarAssociatorIso_hom_component,
    tensorLeftMap_component, tensorLeftMap_component]
  exact associator_naturality_right M N (component f a)

/-- Scalar associators retain naturality in the original first parameter arrow. -/
theorem scalarAssociatorIso_scalar_left {M M' : V} (h : M ⟶ M')
    (N : V) (F : EnrichedFunctorCat V I) :
    scalarTensorMap (h ▷ N) F ≫ (scalarAssociatorIso M' N F).hom =
      (scalarAssociatorIso M N F).hom ≫ scalarTensorMap h (tensorLeftObject N F) := by
  apply hom_ext
  intro a
  rw [component_comp, scalarTensorMap_component, scalarAssociatorIso_hom_component,
    component_comp, scalarAssociatorIso_hom_component, scalarTensorMap_component]
  exact associator_naturality_left h N (F.toEnrichedFunctor.obj a)

/-- Scalar associators retain naturality in the original second parameter arrow. -/
theorem scalarAssociatorIso_scalar_right (M : V) {N N' : V} (k : N ⟶ N')
    (F : EnrichedFunctorCat V I) :
    scalarTensorMap (M ◁ k) F ≫ (scalarAssociatorIso M N' F).hom =
      (scalarAssociatorIso M N F).hom ≫ tensorLeftMap M (scalarTensorMap k F) := by
  apply hom_ext
  intro a
  rw [component_comp, scalarTensorMap_component, scalarAssociatorIso_hom_component,
    component_comp, scalarAssociatorIso_hom_component,
    tensorLeftMap_component, scalarTensorMap_component]
  exact associator_naturality_middle M k (F.toEnrichedFunctor.obj a)

/-- The full scalar action retains the ambient right-unit coherence equation. -/
theorem scalarAssociatorIso_unit_right (M : V) (F : EnrichedFunctorCat V I) :
    (scalarAssociatorIso M (𝟙_ V) F).hom ≫ tensorLeftMap M (scalarUnitIso F).hom =
      scalarTensorMap (ρ_ M).hom F := by
  apply hom_ext
  intro a
  rw [component_comp, scalarAssociatorIso_hom_component,
    tensorLeftMap_component, scalarUnitIso_hom_component, scalarTensorMap_component]
  exact triangle M (F.toEnrichedFunctor.obj a)

/-- The full scalar action retains the ambient left-unit coherence equation. -/
theorem scalarAssociatorIso_unit_left (M : V) (F : EnrichedFunctorCat V I) :
    (scalarAssociatorIso (𝟙_ V) M F).hom ≫ (scalarUnitIso (tensorLeftObject M F)).hom =
      scalarTensorMap (λ_ M).hom F := by
  apply hom_ext
  intro a
  rw [component_comp, scalarAssociatorIso_hom_component,
    scalarUnitIso_hom_component, scalarTensorMap_component]
  exact (leftUnitor_whiskerRight M (F.toEnrichedFunctor.obj a)).symm

/-- The complete genuine scalar action satisfies the ambient pentagon at every full source Hom. -/
theorem scalarAssociatorIso_pentagon (L M N : V) (F : EnrichedFunctorCat V I) :
    (scalarAssociatorIso (L ⊗ M) N F).hom ≫
        (scalarAssociatorIso L M (tensorLeftObject N F)).hom =
      scalarTensorMap (α_ L M N).hom F ≫ (scalarAssociatorIso L (M ⊗ N) F).hom ≫
        tensorLeftMap L (scalarAssociatorIso M N F).hom := by
  apply hom_ext
  intro a
  rw [component_comp, scalarAssociatorIso_hom_component, scalarAssociatorIso_hom_component,
    component_comp, scalarTensorMap_component, component_comp,
    scalarAssociatorIso_hom_component, tensorLeftMap_component,
    scalarAssociatorIso_hom_component]
  exact (pentagon L M N (F.toEnrichedFunctor.obj a)).symm

end CategoryTheory.EnrichedFunctorCat
