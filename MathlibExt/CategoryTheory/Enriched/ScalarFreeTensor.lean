/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Actual scalar tensoring of free enriched diagrams

Free_a X has object X tensor Hom(a,b). The complete scalar/free
comparison is therefore the original inverse ambient associator.
The plain enriched index carries no monoidal structure. Equality with
the actual scalar representable reuses the proved full scalar coherence.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA uV vV

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.Free

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The actual complete representable, retaining every enriched Hom map. -/
abbrev representableObject (a : A) : EnrichedFunctorCat V A :=
  ⟨GradedYoneda.representable a⟩

omit [BraidedCategory V] in
/-- Free coefficient tensoring is the actual scalar representable,
as equality of its complete enriched functor and full Hom maps. -/
theorem object_eq_scalarRepresentable (a : A) (X : V) :
    object a X = tensorLeftObject X (representableObject a) := by
  apply congrArg EnrichedFunctorCat.mk
  apply EnrichedFunctor.ext V
    (F := (object a X).toEnrichedFunctor)
    (G := (tensorLeftObject X (representableObject a)).toEnrichedFunctor) (fun b => rfl)
  intro b c
  change (object a X).toEnrichedFunctor.map b c ≫ 𝟙 _ =
    (tensorLeftObject X (representableObject a)).toEnrichedFunctor.map b c
  rw [Category.comp_id]
  apply MonoidalClosed.uncurry_injective
  have hF := object_uncurry_map a b c X
  have hG := tensorLeftObject_map_uncurry X (representableObject a) b c
  have hR := GradedYoneda.representable_uncurry (V := V) a b c
  have hG' := hG.trans (congrArg
    (fun q : (a ⟶[V] b) ⊗ (b ⟶[V] c) ⟶ (a ⟶[V] c) =>
      (α_ X (a ⟶[V] b) (b ⟶[V] c)).hom ≫ X ◁ q) hR)
  exact hF.trans hG'.symm

/-- The actual scalar/free isomorphism reuses the full original scalar
associator and the proved whole functor equalities. -/
@[no_expose]
def scalarFreeIso (M X : V) (a : A) :
    tensorLeftObject M (object a X) ≅ object a (M ⊗ X) :=
  eqToIso (congrArg (tensorLeftObject M) (object_eq_scalarRepresentable a X)) ≪≫
    (scalarAssociatorIso M X (representableObject a)).symm ≪≫
      (eqToIso (object_eq_scalarRepresentable a (M ⊗ X))).symm

private theorem component_eqToHom {F G : EnrichedFunctorCat V A} (e : F = G) (b : A) :
    component (eqToHom e) b =
      eqToHom (congrArg (fun F : EnrichedFunctorCat V A => F.toEnrichedFunctor.obj b) e) := by
  cases e
  exact component_id F b

/-- Every forward component is the original inverse associator,
including its actual coefficient/source object types. -/
theorem scalarFreeIso_hom_component (M X : V) (a b : A) :
    component (scalarFreeIso M X a).hom b = (α_ M X (a ⟶[V] b)).inv := by
  unfold scalarFreeIso
  rw [Iso.trans_hom, Iso.trans_hom, component_comp, component_comp]
  change component (eqToHom
      (congrArg (tensorLeftObject M) (object_eq_scalarRepresentable a X))) b ≫
    component (scalarAssociatorIso M X (representableObject a)).inv b ≫
      component (eqToHom (object_eq_scalarRepresentable a (M ⊗ X)).symm) b = _
  rw [component_eqToHom, component_eqToHom, scalarAssociatorIso_inv_component]
  change (𝟙 (M ⊗ (X ⊗ (a ⟶[V] b)))) ≫
    (α_ M X (a ⟶[V] b)).inv ≫ 𝟙 ((M ⊗ X) ⊗ (a ⟶[V] b)) =
      (α_ M X (a ⟶[V] b)).inv
  rw [Category.id_comp, Category.comp_id]

/-- Every inverse component is the actual original associator. -/
theorem scalarFreeIso_inv_component (M X : V) (a b : A) :
    component (scalarFreeIso M X a).inv b = (α_ M X (a ⟶[V] b)).hom := by
  unfold scalarFreeIso
  rw [Iso.trans_inv, Iso.trans_inv, component_comp, component_comp]
  change (component (eqToHom (object_eq_scalarRepresentable a (M ⊗ X))) b ≫
    component (scalarAssociatorIso M X (representableObject a)).hom b) ≫
      component (eqToHom
        (congrArg (tensorLeftObject M) (object_eq_scalarRepresentable a X)).symm) b = _
  rw [component_eqToHom, component_eqToHom, scalarAssociatorIso_hom_component]
  change (𝟙 ((M ⊗ X) ⊗ (a ⟶[V] b)) ≫
    (α_ M X (a ⟶[V] b)).hom) ≫ 𝟙 (M ⊗ (X ⊗ (a ⟶[V] b))) =
      (α_ M X (a ⟶[V] b)).hom
  rw [Category.id_comp, Category.comp_id]

/-- Forward naturality retains the entire original enriched Hom object. -/
theorem scalarFreeIso_hom_fullHom (M X : V) (a b c : A) :
    MonoidalClosed.uncurry
        ((tensorLeftObject M (object a X)).toEnrichedFunctor.map b c) ≫
      (α_ M X (a ⟶[V] c)).inv =
    ((α_ M X (a ⟶[V] b)).inv ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((object a (M ⊗ X)).toEnrichedFunctor.map b c) := by
  have h := (scalarFreeIso M X a).hom.uncurriedNaturality b c
  change MonoidalClosed.uncurry
      ((tensorLeftObject M (object a X)).toEnrichedFunctor.map b c) ≫
      component (scalarFreeIso M X a).hom c =
    (component (scalarFreeIso M X a).hom b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((object a (M ⊗ X)).toEnrichedFunctor.map b c) at h
  rw [scalarFreeIso_hom_component, scalarFreeIso_hom_component] at h
  exact h

/-- Inverse naturality retains the same full enriched Hom action. -/
theorem scalarFreeIso_inv_fullHom (M X : V) (a b c : A) :
    MonoidalClosed.uncurry ((object a (M ⊗ X)).toEnrichedFunctor.map b c) ≫
      (α_ M X (a ⟶[V] c)).hom =
    ((α_ M X (a ⟶[V] b)).hom ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry
        ((tensorLeftObject M (object a X)).toEnrichedFunctor.map b c) := by
  have h := (scalarFreeIso M X a).inv.uncurriedNaturality b c
  change MonoidalClosed.uncurry ((object a (M ⊗ X)).toEnrichedFunctor.map b c) ≫
      component (scalarFreeIso M X a).inv c =
    (component (scalarFreeIso M X a).inv b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry
        ((tensorLeftObject M (object a X)).toEnrichedFunctor.map b c) at h
  rw [scalarFreeIso_inv_component, scalarFreeIso_inv_component] at h
  exact h

/-- All actual source coefficient maps commute with the complete forward comparison. -/
theorem scalarFreeIso_coefficient (M : V) (a : A) {X Y : V} (f : X ⟶ Y) :
    tensorLeftMap M (coefficientMap a f) ≫ (scalarFreeIso M Y a).hom =
      (scalarFreeIso M X a).hom ≫ coefficientMap a (M ◁ f) := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, tensorLeftMap_component, coefficientMap_component,
    scalarFreeIso_hom_component, component_comp, scalarFreeIso_hom_component,
    coefficientMap_component]
  exact associator_inv_naturality_middle M f (a ⟶[V] b)

/-- All scalar coefficient maps commute with the complete forward comparison. -/
theorem scalarFreeIso_scalar {M N : V} (h : M ⟶ N) (X : V) (a : A) :
    scalarTensorMap h (object a X) ≫ (scalarFreeIso N X a).hom =
      (scalarFreeIso M X a).hom ≫ coefficientMap a (h ▷ X) := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, scalarTensorMap_component, scalarFreeIso_hom_component,
    component_comp, scalarFreeIso_hom_component, coefficientMap_component]
  exact associator_inv_naturality_left h X (a ⟶[V] b)

/-- The complete scalar/free comparison is natural as a functor of X. -/
@[no_expose]
def scalarFreeNatIso (M : V) (a : A) :
    functor a ⋙ EnrichedFunctorCat.tensorLeft M ≅ MonoidalCategory.tensorLeft M ⋙ functor a :=
  NatIso.ofComponents (fun X => scalarFreeIso M X a)
    (fun f => scalarFreeIso_coefficient M a f)

/-- The original full Hom object precomposition selected by a source
unit point. The enriched index has no additional ordinary category. -/
def sourceHomMap {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (b : A) :
    (a' ⟶[V] b) ⟶ (a ⟶[V] b) :=
  (λ_ (a' ⟶[V] b)).inv ≫ (e ▷ (a' ⟶[V] b)) ≫ eComp V a a' b

/-- The actual contravariant source map extends the original enriched
identity-slot coefficient map through the full original free action. -/
def sourceMap {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    object a' X ⟶ object a X :=
  extend a' X (object a X) ((ρ_ X).inv ≫ X ◁ e)

omit [BraidedCategory V] [MonoidalClosed V] in
private theorem sourceUnitTensor (X H : V) :
    ((ρ_ X).inv ▷ H) ≫ (α_ X (𝟙_ V) H).hom = X ◁ (λ_ H).inv := by
  apply (cancel_mono (X ◁ (λ_ H).hom)).1
  rw [Category.assoc, triangle]
  rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight,
    ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]

/-- Source maps retain the original full Hom precomposition at every
component, with the same coefficient X. -/
theorem sourceMap_component {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) (b : A) :
    component (sourceMap e X) b = X ◁ sourceHomMap e b := by
  rw [sourceMap, extend_component]
  unfold extensionComponent
  rw [tensorHom_id, object_uncurry_map]
  change (((ρ_ X).inv ≫ X ◁ e) ▷ (a' ⟶[V] b)) ≫ action a X a' b =
    X ◁ sourceHomMap e b
  rw [comp_whiskerRight]
  dsimp only [action, sourceHomMap]
  rw [Category.assoc, associator_naturality_middle_assoc,
    ← Category.assoc, sourceUnitTensor]
  rw [whiskerLeft_comp, whiskerLeft_comp]

/-- Precomposition in the enriched source is natural in the coefficient. -/
theorem sourceMap_naturality {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a'))
    {X Y : V} (f : X ⟶ Y) :
    coefficientMap a' f ≫ sourceMap e Y = sourceMap e X ≫ coefficientMap a f := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, coefficientMap_component, sourceMap_component,
    component_comp, sourceMap_component, coefficientMap_component]
  exact (whisker_exchange f (sourceHomMap e b)).symm

/-- An enriched source point induces a natural transformation between free functors. -/
@[no_expose]
def sourceNatTrans {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) :
    functor (V := V) a' ⟶ functor (V := V) a where
  app X := sourceMap e X
  naturality _ _ f := sourceMap_naturality e f

/-- The source transformation has the original source map at every coefficient. -/
theorem sourceNatTrans_app {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    (sourceNatTrans e).app X = sourceMap e X := by
  unfold sourceNatTrans
  rfl

/-- Identity evaluation of source precomposition keeps its enriched source point. -/
theorem evaluate_sourceMap {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V)
    (F : EnrichedFunctorCat V A) (t : object a X ⟶ F) :
    evaluate a' X F (sourceMap e X ≫ t) =
      (ρ_ X).inv ≫ X ◁ e ≫ component t a' := by
  rw [sourceMap, evaluate_postcomp, evaluate_extend]
  change ((ρ_ X).inv ≫ X ◁ e) ≫ component t a' = _
  exact Category.assoc _ _ _

/-- Source precomposition of an extension is the extension of its full source action. -/
theorem sourceMap_comp_extend {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V)
    (F : EnrichedFunctorCat V A) (f : X ⟶ F.toEnrichedFunctor.obj a) :
    sourceMap e X ≫ extend a X F f =
      extend a' X F ((ρ_ X).inv ≫ X ◁ e ≫ (f ▷ (a ⟶[V] a')) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a a')) := by
  apply (homEquiv a' X F).injective
  change evaluate a' X F (sourceMap e X ≫ extend a X F f) =
    evaluate a' X F (extend a' X F _)
  rw [evaluate_sourceMap, evaluate_extend, extend_component]
  simp only [extensionComponent, tensorHom_id]

/-- The forward scalar/free comparison commutes with every original
source-index map while preserving all full Hom objects. -/
theorem scalarFreeIso_source (M X : V) {a a' : A}
    (e : 𝟙_ V ⟶ (a ⟶[V] a')) :
    tensorLeftMap M (sourceMap e X) ≫ (scalarFreeIso M X a).hom =
      (scalarFreeIso M X a').hom ≫ sourceMap e (M ⊗ X) := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, tensorLeftMap_component, sourceMap_component,
    scalarFreeIso_hom_component, component_comp, scalarFreeIso_hom_component,
    sourceMap_component]
  exact associator_inv_naturality_right M X (sourceHomMap e b)

/-- The inverse comparison preserves the same original source map. -/
theorem scalarFreeIso_inv_source (M X : V) {a a' : A}
    (e : 𝟙_ V ⟶ (a ⟶[V] a')) :
    sourceMap e (M ⊗ X) ≫ (scalarFreeIso M X a).inv =
      (scalarFreeIso M X a').inv ≫ tensorLeftMap M (sourceMap e X) := by
  apply EnrichedFunctorCat.hom_ext
  intro b
  rw [component_comp, sourceMap_component, scalarFreeIso_inv_component,
    component_comp, scalarFreeIso_inv_component, tensorLeftMap_component,
    sourceMap_component]
  exact associator_naturality_right M X (sourceHomMap e b)

/-- Every full source action intertwines the source change with the
original free enriched composition, rather than only object evaluations. -/
theorem sourceMap_fullHom {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a'))
    (X : V) (b c : A) :
    action a' X b c ≫ (X ◁ sourceHomMap e c) =
      ((X ◁ sourceHomMap e b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫ action a X b c := by
  have h := (sourceMap e X).uncurriedNaturality b c
  change MonoidalClosed.uncurry ((object a' X).toEnrichedFunctor.map b c) ≫
      component (sourceMap e X) c =
    (component (sourceMap e X) b ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry ((object a X).toEnrichedFunctor.map b c) at h
  rw [sourceMap_component, sourceMap_component, object_uncurry_map,
    object_uncurry_map] at h
  exact h

end CategoryTheory.EnrichedFunctorCat.Free
