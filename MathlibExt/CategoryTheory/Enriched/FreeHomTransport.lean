/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.Restriction

/-!
# Full Hom transport of free enriched diagrams

An enriched functor induces the canonical map from a free diagram into the
restriction of its target free diagram. Its components are the actual full
Hom maps, tensored with the coefficient. Composition and identity
preservation prove naturality and the extension/evaluation equations.
When those Hom maps are isomorphisms, their actual inverses give an Iso of
the two free diagrams. No equivalence of ordinary carriers or adjunction
comparison is supplied as a premise.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeHomTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (G : EnrichedFunctor V B A)

/-- Restrict the actual target free diagram along the complete enriched functor. -/
abbrev restrictedFree (a : B) (X : V) : EnrichedFunctorCat V B :=
  restrictionObject G (Free.object (G.obj a) X)

omit [BraidedCategory V] in
/-- The original full source and target composition equations imply free Hom-map naturality. -/
theorem map_natural (a : B) (X : V) (b c : B) :
    MonoidalClosed.uncurry ((Free.object a X).toEnrichedFunctor.map b c) ≫
        (X ◁ G.map a c) =
      ((X ◁ G.map a b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry ((restrictedFree G a X).toEnrichedFunctor.map b c) := by
  change MonoidalClosed.uncurry
        (MonoidalClosed.curry ((α_ X (a ⟶[V] b) (b ⟶[V] c)).hom ≫ X ◁ eComp V a b c)) ≫
      (X ◁ G.map a c) =
    ((X ◁ G.map a b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
      MonoidalClosed.uncurry
        (G.map b c ≫ MonoidalClosed.curry
          ((α_ X (G.obj a ⟶[V] G.obj b) (G.obj b ⟶[V] G.obj c)).hom ≫
            X ◁ eComp V (G.obj a) (G.obj b) (G.obj c)))
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  simp only [Category.assoc]
  rw [tensorHom_id, associator_naturality_right_assoc, associator_naturality_middle_assoc,
    ← whiskerLeft_comp, G.map_comp]
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]

/-- The canonical free map is a genuine unit-graded transformation on the full Hom objects. -/
@[no_expose]
def map (a : B) (X : V) : Free.object a X ⟶ restrictedFree G a X :=
  GradedNatTrans.unitOfComponents (fun b => X ◁ G.map a b) (map_natural G a X)

/-- Every original ordinary component is the actual coefficient-tensored full Hom map. -/
theorem map_component (a : B) (X : V) (b : B) :
    component (map G a X) b = X ◁ G.map a b :=
  GradedNatTrans.unitOfComponents_component _ (map_natural G a X) b

omit [BraidedCategory V] in
/-- Extension uses the entire actual Hom map, before any invertibility assumption. -/
theorem map_extension_component (a b : B) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj (G.obj a)) :
    (X ◁ G.map a b) ≫ Free.extensionComponent (G.obj a) X F f (G.obj b) =
      Free.extensionComponent a X (restrictionObject G F) f b := by
  change (X ◁ G.map a b) ≫ (f ⊗ₘ 𝟙 (G.obj a ⟶[V] G.obj b)) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map (G.obj a) (G.obj b)) =
    (f ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry (G.map a b ≫ F.toEnrichedFunctor.map (G.obj a) (G.obj b))
  rw [MonoidalClosed.uncurry_natural_left, tensorHom_id, tensorHom_id, whisker_exchange_assoc]

/-- The genuine canonical free map commutes with the original full extension transformation. -/
theorem map_extend (a : B) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj (G.obj a)) :
    map G a X ≫ restrictionMap G (Free.extend (G.obj a) X F f) =
      Free.extend a X (restrictionObject G F) f := by
  apply hom_ext
  intro b
  rw [component_comp, map_component, restrictionMap_component]
  change (X ◁ G.map a b) ≫ component (Free.extend (G.obj a) X F f) (G.obj b) =
    component (Free.extend a X (restrictionObject G F) f) b
  exact (congrArg (fun e => (X ◁ G.map a b) ≫ e)
    (Free.extend_component (G.obj a) X F f (G.obj b))).trans
      ((map_extension_component G a b X F f).trans
        (Free.extend_component a X (restrictionObject G F) f b).symm)

/-- Identity evaluation retains the original coefficient map and the full enriched identity. -/
theorem evaluate_map (a : B) (X : V) (F : EnrichedFunctorCat V A)
    (q : Free.object (G.obj a) X ⟶ F) :
    Free.evaluate a X (restrictionObject G F) (map G a X ≫ restrictionMap G q) =
      Free.evaluate (G.obj a) X F q := by
  rw [Free.evaluate, Free.evaluate, component_comp, map_component, restrictionMap_component]
  let q' : X ⊗ (G.obj a ⟶[V] G.obj a) ⟶ F.toEnrichedFunctor.obj (G.obj a) :=
    component q (G.obj a)
  change (ρ_ X).inv ≫ X ◁ eId V a ≫ X ◁ G.map a a ≫ q' =
    (ρ_ X).inv ≫ X ◁ eId V (G.obj a) ≫ q'
  rw [← whiskerLeft_comp_assoc, G.map_id]

/-- The original chosen free-adjunction units commute with the actual full Hom map. -/
theorem unit_map (a : B) (X : V) :
    (Free.adjunction (V := V) a).unit.app X ≫ component (map G a X) a =
      (Free.adjunction (V := V) (G.obj a)).unit.app X := by
  have hs : (Free.adjunction (V := V) a).unit.app X = (ρ_ X).inv ≫ X ◁ eId V a := by
    have h := (Free.adjunction (V := V) a).homEquiv_id X
    rw [Free.adjunction_homEquiv] at h
    change (ρ_ X).inv ≫ X ◁ eId V a ≫ component (𝟙 (Free.object a X)) a = _ at h
    rw [component_id, Category.comp_id] at h
    exact h.symm
  have ht : (Free.adjunction (V := V) (G.obj a)).unit.app X =
      (ρ_ X).inv ≫ X ◁ eId V (G.obj a) := by
    have h := (Free.adjunction (V := V) (G.obj a)).homEquiv_id X
    rw [Free.adjunction_homEquiv] at h
    change (ρ_ X).inv ≫ X ◁ eId V (G.obj a) ≫
      component (𝟙 (Free.object (G.obj a) X)) (G.obj a) = _ at h
    rw [component_id, Category.comp_id] at h
    exact h.symm
  rw [hs, ht, map_component]
  change ((ρ_ X).inv ≫ X ◁ eId V a) ≫ X ◁ G.map a a =
    (ρ_ X).inv ≫ X ◁ eId V (G.obj a)
  rw [Category.assoc, ← whiskerLeft_comp, G.map_id]

/-- The original target free unit extends to the whole canonical free Hom map. -/
theorem extend_unit_eq_map (a : B) (X : V) :
    Free.extend a X (restrictedFree G a X)
      ((Free.adjunction (V := V) (G.obj a)).unit.app X) = map G a X := by
  let F := Free.object (G.obj a) X
  let u := (Free.adjunction (V := V) (G.obj a)).unit.app X
  have hu := (Free.adjunction (V := V) (G.obj a)).homEquiv_id X
  rw [Free.adjunction_homEquiv] at hu
  have he : Free.extend (G.obj a) X F u = 𝟙 F :=
    (congrArg (Free.extend (G.obj a) X F) hu).symm.trans
      (Free.extend_evaluate (G.obj a) X F (𝟙 F))
  have h := map_extend G a X F u
  have hi : restrictionMap G (𝟙 F) = 𝟙 (restrictionObject G F) :=
    (restriction G).map_id F
  have hc := congrArg (fun f => map G a X ≫ restrictionMap G f) he
  have hid := congrArg (fun f => map G a X ≫ f) hi
  exact h.symm.trans (hc.trans (hid.trans (Category.comp_id (map G a X))))

variable [∀ a b : B, IsIso (G.map a b)]

/-- The actual full Hom inverses give the coefficient-first comparison of free values. -/
def componentIso (a : B) (X : V) (b : B) :
    (restrictedFree G a X).toEnrichedFunctor.obj b ≅ (Free.object a X).toEnrichedFunctor.obj b :=
  tensorIso (Iso.refl X) (asIso (G.map a b)).symm

omit [BraidedCategory V] in
/-- The forward value comparison uses the actual inverse of the entire enriched Hom map. -/
theorem componentIso_hom (a : B) (X : V) (b : B) :
    (componentIso G a X b).hom = X ◁ inv (G.map a b) := by
  change 𝟙 X ⊗ₘ inv (G.map a b) = _
  exact id_tensorHom _ _

omit [BraidedCategory V] in
/-- The inverse value comparison uses the original entire enriched Hom map. -/
theorem componentIso_inv (a : B) (X : V) (b : B) :
    (componentIso G a X b).inv = X ◁ G.map a b := by
  change 𝟙 X ⊗ₘ G.map a b = _
  exact id_tensorHom _ _

omit [BraidedCategory V] in
/-- The actual inverse Hom maps satisfy full free naturality by the two Iso cancellation laws. -/
theorem inverse_natural (a : B) (X : V) (b c : B) :
    MonoidalClosed.uncurry ((restrictedFree G a X).toEnrichedFunctor.map b c) ≫
        (componentIso G a X c).hom =
      ((componentIso G a X b).hom ⊗ₘ 𝟙 (b ⟶[V] c)) ≫
        MonoidalClosed.uncurry ((Free.object a X).toEnrichedFunctor.map b c) := by
  let P := (restrictedFree G a X).toEnrichedFunctor.obj b
  let Q := (restrictedFree G a X).toEnrichedFunctor.obj c
  let R := (Free.object a X).toEnrichedFunctor.obj b
  let S := (Free.object a X).toEnrichedFunctor.obj c
  let H := b ⟶[V] c
  let p : P ⊗ H ⟶ Q := MonoidalClosed.uncurry ((restrictedFree G a X).toEnrichedFunctor.map b c)
  let q : R ⊗ H ⟶ S := MonoidalClosed.uncurry ((Free.object a X).toEnrichedFunctor.map b c)
  let f : P ≅ R := componentIso G a X b
  let g : Q ≅ S := componentIso G a X c
  have hn : q ≫ g.inv = (f.inv ⊗ₘ 𝟙 H) ≫ p := by
    have hf : f.inv = X ◁ G.map a b := componentIso_inv G a X b
    have hg : g.inv = X ◁ G.map a c := componentIso_inv G a X c
    exact (congrArg (fun t => q ≫ t) hg).trans
      ((map_natural G a X b c).trans
        (congrArg (fun t => (t ⊗ₘ 𝟙 H) ≫ p) hf).symm)
  change p ≫ g.hom = (f.hom ⊗ₘ 𝟙 H) ≫ q
  apply (cancel_mono g.inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc, hn,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Category.id_comp, id_tensorHom_id,
    Category.id_comp]

/-- The full inverse Hom family is a genuine enriched free comparison. -/
@[no_expose]
def inverse (a : B) (X : V) : restrictedFree G a X ⟶ Free.object a X :=
  GradedNatTrans.unitOfComponents (fun b => (componentIso G a X b).hom) (inverse_natural G a X)

/-- Each inverse transformation component is its actual complete Hom inverse. -/
theorem inverse_component (a : B) (X : V) (b : B) :
    component (inverse G a X) b = (componentIso G a X b).hom :=
  GradedNatTrans.unitOfComponents_component _ (inverse_natural G a X) b

/-- The actual free comparison, with both genuine inverse transformations and all coefficients. -/
def iso (a : B) (X : V) : restrictedFree G a X ≅ Free.object a X where
  hom := inverse G a X
  inv := map G a X
  hom_inv_id := by
    apply hom_ext
    intro b
    rw [component_comp, component_id, inverse_component, map_component, ← componentIso_inv]
    exact (componentIso G a X b).hom_inv_id
  inv_hom_id := by
    apply hom_ext
    intro b
    rw [component_comp, component_id, inverse_component, map_component, ← componentIso_inv]
    exact (componentIso G a X b).inv_hom_id

/-- The forward genuine free Iso retains the actual full Hom inverse at every index. -/
theorem iso_hom_component (a : B) (X : V) (b : B) :
    component (iso G a X).hom b = X ◁ inv (G.map a b) :=
  (inverse_component G a X b).trans (componentIso_hom G a X b)

/-- The inverse genuine free Iso retains the actual full Hom map at every index. -/
theorem iso_inv_component (a : B) (X : V) (b : B) :
    component (iso G a X).inv b = X ◁ G.map a b := map_component G a X b

/-- Extension agrees under the actual free Iso and actual enriched restriction. -/
theorem iso_extend (a : B) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj (G.obj a)) :
    (iso G a X).inv ≫ restrictionMap G (Free.extend (G.obj a) X F f) =
      Free.extend a X (restrictionObject G F) f := map_extend G a X F f

/-- Evaluation agrees under the same complete free Iso, with the source identity retained. -/
theorem iso_evaluate (a : B) (X : V) (F : EnrichedFunctorCat V A)
    (q : Free.object (G.obj a) X ⟶ F) :
    Free.evaluate a X (restrictionObject G F) ((iso G a X).inv ≫ restrictionMap G q) =
      Free.evaluate (G.obj a) X F q := evaluate_map G a X F q

/-- The same original free units commute with the actual full Hom inverse. -/
theorem iso_unit (a : B) (X : V) :
    (Free.adjunction (V := V) (G.obj a)).unit.app X ≫ component (iso G a X).hom a =
      (Free.adjunction (V := V) a).unit.app X := by
  let e : (restrictedFree G a X).toEnrichedFunctor.obj a ≅
      (Free.object a X).toEnrichedFunctor.obj a := componentIso G a X a
  let ua : X ⟶ (Free.object a X).toEnrichedFunctor.obj a :=
    (Free.adjunction (V := V) a).unit.app X
  let ub : X ⟶ (restrictedFree G a X).toEnrichedFunctor.obj a :=
    (Free.adjunction (V := V) (G.obj a)).unit.app X
  have h : ua ≫ e.inv = ub :=
    (congrArg (fun f => ua ≫ f)
      ((componentIso_inv G a X a).trans (map_component G a X a).symm)).trans (unit_map G a X)
  rw [iso_hom_component, ← componentIso_hom]
  change ub ≫ e.hom = ua
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every coefficient morphism commutes with the same entire free Hom-inverse comparison. -/
theorem coefficient_natural (a : B) {X Y : V} (f : X ⟶ Y) :
    restrictionMap G (Free.coefficientMap (G.obj a) f) ≫ (iso G a Y).hom =
      (iso G a X).hom ≫ Free.coefficientMap a f := by
  apply hom_ext
  intro b
  rw [component_comp, component_comp, restrictionMap_component, iso_hom_component,
    iso_hom_component]
  have hX := Free.coefficientMap_component a f b
  have hY := Free.coefficientMap_component (G.obj a) f (G.obj b)
  have h : (f ▷ (G.obj a ⟶[V] G.obj b)) ≫ Y ◁ inv (G.map a b) =
      (X ◁ inv (G.map a b)) ≫ (f ▷ (a ⟶[V] b)) :=
    (whisker_exchange f (inv (G.map a b))).symm
  change component (Free.coefficientMap (G.obj a) f) (G.obj b) ≫ Y ◁ inv (G.map a b) =
    (X ◁ inv (G.map a b)) ≫ component (Free.coefficientMap a f) b
  exact (congrArg (fun q => q ≫ Y ◁ inv (G.map a b)) hY).trans
    (h.trans
      (congrArg (fun q => (X ◁ inv (G.map a b)) ≫ q) hX).symm)

/-- The actual free Hom comparisons are natural in every coefficient object and morphism. -/
def functorIso (a : B) : Free.functor (V := V) (G.obj a) ⋙ restriction G ≅
    Free.functor (V := V) a :=
  NatIso.ofComponents (iso G a) (fun f => coefficient_natural G a f)

/-- The coefficient-natural free Iso uses the same original comparison at every coefficient. -/
theorem functorIso_hom_app (a : B) (X : V) :
    (functorIso G a).hom.app X = (iso G a X).hom := rfl

/-- The inverse coefficient-natural Iso uses the same original full Hom map. -/
theorem functorIso_inv_app (a : B) (X : V) :
    (functorIso G a).inv.app X = (iso G a X).inv := rfl

end CategoryTheory.EnrichedFunctorCat.FreeHomTransport
