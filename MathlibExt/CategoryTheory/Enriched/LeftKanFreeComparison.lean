/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.CategoryTheory.Enriched.FreeHomTransport
public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension
public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor

/-!
# The actual enriched left Kan extension of a free diagram

The forward map is the original Kan transpose of the complete enriched
Hom map. The inverse is the original free extension of the Kan unit
evaluated at the source identity. The two original adjunctions prove that
these maps are inverse. Their characteristic equations retain every
weighted coend generator and every enriched Hom coefficient.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uA uB

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]

/-- The original weighted-coend Kan object, on the original free diagram. -/
abbrev object (a : A) (X : V) : EnrichedFunctorCat V B :=
  leftKanObject j (Free.object a X)

/-- The two actual Hom correspondences, with the same original identity evaluation. -/
def homEquiv (a : A) (X : V) (Y : EnrichedFunctorCat V B) :
    (object j a X ⟶ Y) ≃ (X ⟶ Y.toEnrichedFunctor.obj (j.obj a)) :=
  (leftKanHomEquiv j (Free.object a X) Y).trans
    (Free.homEquiv a X (restrictionObject j Y))

/-- The complete forward correspondence uses the original restricted Kan unit. -/
theorem homEquiv_apply (a : A) (X : V) (Y : EnrichedFunctorCat V B)
    (f : object j a X ⟶ Y) :
    homEquiv j a X Y f =
      Free.evaluate a X (restrictionObject j Y)
        (leftKanUnit j (Free.object a X) ≫ restrictionMap j f) := by
  change Free.evaluate a X (restrictionObject j Y)
    (leftKanHomEquiv j (Free.object a X) Y f) = _
  rw [leftKanHomEquiv_apply]
  rfl

/-- Actual target transformations preserve the whole composed Hom correspondence. -/
theorem homEquiv_postcomp (a : A) (X : V)
    {Y Z : EnrichedFunctorCat V B} (f : object j a X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv j a X Z (f ≫ g) = homEquiv j a X Y f ≫ component g (j.obj a) := by
  change Free.evaluate a X (restrictionObject j Z)
      (leftKanHomEquiv j (Free.object a X) Z (f ≫ g)) = _
  rw [leftKanHomEquiv_naturality_right, Free.evaluate_postcomp]
  rw [evaluation_map, restrictionMap_component]
  rfl

/-- The original full enriched Hom map is transposed through the genuine Kan adjunction. -/
def hom (a : A) (X : V) : object j a X ⟶ Free.object (j.obj a) X :=
  (leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)).symm
    (FreeHomTransport.map j a X)

/-- The inverse extends the original identity evaluation of the actual Kan unit. -/
def inv (a : A) (X : V) : Free.object (j.obj a) X ⟶ object j a X :=
  Free.extend (j.obj a) X (object j a X)
    (homEquiv j a X (object j a X) (𝟙 (object j a X)))

/-- The forward map has the entire original restricted-unit characteristic. -/
theorem hom_unit (a : A) (X : V) :
    leftKanUnit j (Free.object a X) ≫ restrictionMap j (hom j a X) =
      FreeHomTransport.map j a X := by
  have h := (leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)).apply_symm_apply
    (FreeHomTransport.map j a X)
  rw [leftKanHomEquiv_apply] at h
  exact h

/-- Every source component of the characteristic is the actual coefficient-tensored Hom map. -/
theorem hom_unit_component (a : A) (X : V) (c : A) :
    leftKanUnitComponent j (Free.object a X) c ≫ component (hom j a X) (j.obj c) =
      X ◁ j.map a c := by
  have h := congrArg (fun f => component f c) (hom_unit j a X)
  rw [component_comp, leftKanUnit_component, restrictionMap_component,
    FreeHomTransport.map_component] at h
  exact h

/-- Evaluating the forward transpose retains the original target free identity. -/
theorem homEquiv_hom (a : A) (X : V) :
    homEquiv j a X (Free.object (j.obj a) X) (hom j a X) =
      Free.evaluate (j.obj a) X (Free.object (j.obj a) X) (𝟙 (Free.object (j.obj a) X)) := by
  change Free.evaluate a X (restrictionObject j (Free.object (j.obj a) X))
      ((leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X))
        ((leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)).symm
          (FreeHomTransport.map j a X))) = _
  rw [Equiv.apply_symm_apply]
  have h := FreeHomTransport.evaluate_map j a X (Free.object (j.obj a) X)
      (𝟙 (Free.object (j.obj a) X))
  have hi : restrictionMap j (𝟙 (Free.object (j.obj a) X)) =
      𝟙 (restrictionObject j (Free.object (j.obj a) X)) :=
    (restriction j).map_id (Free.object (j.obj a) X)
  rw [hi, Category.comp_id] at h
  exact h

/-- Evaluating the inverse recovers the same original Kan-unit coefficient. -/
theorem evaluate_inv (a : A) (X : V) :
    Free.evaluate (j.obj a) X (object j a X) (inv j a X) =
      homEquiv j a X (object j a X) (𝟙 (object j a X)) :=
  Free.evaluate_extend (j.obj a) X (object j a X) _

/-- The full weighted-coend object is recovered by the two actual maps. -/
theorem hom_inv_id (a : A) (X : V) :
    hom j a X ≫ inv j a X = 𝟙 (object j a X) := by
  apply (homEquiv j a X (object j a X)).injective
  rw [homEquiv_postcomp, homEquiv_hom]
  have h := Free.evaluate_postcomp (j.obj a) X
    (𝟙 (Free.object (j.obj a) X)) (inv j a X)
  rw [Category.id_comp, evaluate_inv] at h
  exact h.symm

/-- The complete target free object is recovered by the same two actual maps. -/
theorem inv_hom_id (a : A) (X : V) :
    inv j a X ≫ hom j a X = 𝟙 (Free.object (j.obj a) X) := by
  apply (Free.homEquiv (j.obj a) X (Free.object (j.obj a) X)).injective
  change Free.evaluate (j.obj a) X (Free.object (j.obj a) X)
      (inv j a X ≫ hom j a X) = _
  calc
    _ = Free.evaluate (j.obj a) X (object j a X) (inv j a X) ≫
        component (hom j a X) (j.obj a) :=
      Free.evaluate_postcomp (j.obj a) X (inv j a X) (hom j a X)
    _ = homEquiv j a X (object j a X) (𝟙 (object j a X)) ≫
        component (hom j a X) (j.obj a) := by rw [evaluate_inv]
    _ = homEquiv j a X (Free.object (j.obj a) X)
        (𝟙 (object j a X) ≫ hom j a X) :=
      (homEquiv_postcomp j a X (𝟙 (object j a X)) (hom j a X)).symm
    _ = _ := by rw [Category.id_comp, homEquiv_hom]; rfl

/-- The original Kan and free adjunctions construct the isomorphism of genuine enriched diagrams. -/
def iso (a : A) (X : V) : object j a X ≅ Free.object (j.obj a) X where
  hom := hom j a X
  inv := inv j a X
  hom_inv_id := hom_inv_id j a X
  inv_hom_id := inv_hom_id j a X

/-- The full forward map remains the original Kan transpose. -/
theorem iso_hom (a : A) (X : V) : (iso j a X).hom = hom j a X := rfl

/-- The full inverse remains the original free extension of the evaluated Kan unit. -/
theorem iso_inv (a : A) (X : V) : (iso j a X).inv = inv j a X := rfl

/-- Every original weighted coend coefficient has its literal Hom-map contraction. -/
theorem hom_ι (a : A) (X : V) (b : B) (c : A) :
    Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a X).toEnrichedFunctor c ≫
        component (hom j a X) b =
      ((j.obj c ⟶[V] b) ◁ (X ◁ j.map a c)) ≫
        (β_ (j.obj c ⟶[V] b) (X ⊗ (j.obj a ⟶[V] j.obj c))).hom ≫
        (α_ X (j.obj a ⟶[V] j.obj c) (j.obj c ⟶[V] b)).hom ≫
        (X ◁ eComp V (j.obj a) (j.obj c) b) := by
  have h := leftKanHomEquiv_symm_ι j (Free.object a X) (Free.object (j.obj a) X)
    (FreeHomTransport.map j a X) b c
  have hmap := FreeHomTransport.map_component j a X c
  have ht : (𝟙 (j.obj c ⟶[V] b) ⊗ₘ component (FreeHomTransport.map j a X) c) =
      (j.obj c ⟶[V] b) ◁ (X ◁ j.map a c) :=
    (congrArg (fun f => 𝟙 (j.obj c ⟶[V] b) ⊗ₘ f) hmap).trans (id_tensorHom _ _)
  have ha := Free.object_uncurry_map (j.obj a) (j.obj c) b X
  have hp := congrArg₂
    (fun p q => p ≫
      (β_ (j.obj c ⟶[V] b) (X ⊗ (j.obj a ⟶[V] j.obj c))).hom ≫ q) ht ha
  exact h.trans hp

/-- The inverse component is the original free extension on every complete target Hom object. -/
theorem inv_component (a : A) (X : V) (b : B) :
    component (inv j a X) b =
      (homEquiv j a X (object j a X) (𝟙 (object j a X)) ⊗ₘ
        𝟙 (j.obj a ⟶[V] b)) ≫
          MonoidalClosed.uncurry ((object j a X).toEnrichedFunctor.map (j.obj a) b) :=
  Free.extend_component (j.obj a) X (object j a X) _ b

/-- The evaluated inverse coefficient uses the original source identity and original Kan unit. -/
theorem inv_coefficient (a : A) (X : V) :
    homEquiv j a X (object j a X) (𝟙 (object j a X)) =
      (ρ_ X).inv ≫ (X ◁ eId V a) ≫ leftKanUnitComponent j (Free.object a X) a := by
  rw [homEquiv_apply]
  have hi : restrictionMap j (𝟙 (object j a X)) =
      𝟙 (restrictionObject j (object j a X)) := (restriction j).map_id (object j a X)
  rw [hi, Category.comp_id, Free.evaluate, leftKanUnit_component]
  rfl

/-- The complete forward map is the original Kan functor map followed by its actual counit. -/
theorem hom_counit (a : A) (X : V) :
    hom j a X = (leftKan j).map (FreeHomTransport.map j a X) ≫
      (leftKanRestrictionAdjunction j).counit.app (Free.object (j.obj a) X) := by
  have h := (leftKanRestrictionAdjunction j).homEquiv_counit
    (g := FreeHomTransport.map j a X)
  rw [leftKanRestrictionAdjunction_homEquiv] at h
  exact h

/-- The entire inverse is the original free functor map followed by the original free counit. -/
theorem inv_counit (a : A) (X : V) :
    inv j a X = (Free.functor (j.obj a)).map
        (homEquiv j a X (object j a X) (𝟙 (object j a X))) ≫
      (Free.adjunction (j.obj a)).counit.app (object j a X) := by
  have h := (Free.adjunction (j.obj a)).homEquiv_counit
    (X := X) (Y := object j a X)
    (g := homEquiv j a X (object j a X) (𝟙 (object j a X)))
  rw [Free.adjunction_homEquiv] at h
  exact h

/-- Composing with the actual inverse identifies the two original entire Hom functions. -/
theorem homEquiv_comparison (a : A) (X : V) (Y : EnrichedFunctorCat V B)
    (f : object j a X ⟶ Y) :
    homEquiv j a X Y f = Free.homEquiv (j.obj a) X Y (inv j a X ≫ f) := by
  change _ = Free.evaluate (j.obj a) X Y (inv j a X ≫ f)
  rw [Free.evaluate_postcomp, evaluate_inv]
  have h := homEquiv_postcomp j a X (𝟙 (object j a X)) f
  rw [Category.id_comp] at h
  exact h

/-- The inverse entire Hom function retains both original transposes. -/
theorem homEquiv_symm_apply (a : A) (X : V) (Y : EnrichedFunctorCat V B)
    (f : X ⟶ Y.toEnrichedFunctor.obj (j.obj a)) :
    (homEquiv j a X Y).symm f = hom j a X ≫ Free.extend (j.obj a) X Y f := by
  apply (homEquiv j a X Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_comparison,
    ← Category.assoc, inv_hom_id, Category.id_comp]
  exact (Free.evaluate_extend (j.obj a) X Y f).symm

/-- Coefficient precomposition uses the actual Kan and free functor maps. -/
theorem homEquiv_coefficient (a : A) {X X' : V} (f : X ⟶ X')
    (Y : EnrichedFunctorCat V B) (g : object j a X' ⟶ Y) :
    homEquiv j a X Y ((leftKan j).map (Free.coefficientMap a f) ≫ g) =
      f ≫ homEquiv j a X' Y g := by
  change Free.homEquiv a X (restrictionObject j Y)
      (leftKanHomEquiv j (Free.object a X) Y
        ((leftKan j).map (Free.coefficientMap a f) ≫ g)) = _
  rw [leftKanHomEquiv_naturality_left]
  have h := (Free.adjunction a).homEquiv_naturality_left f
    (leftKanHomEquiv j (Free.object a X') Y g)
  rw [Free.adjunction_homEquiv] at h
  exact h

/-- The actual comparison is natural in every original coefficient morphism. -/
theorem hom_coefficient (a : A) {X Y : V} (f : X ⟶ Y) :
    (leftKan j).map (Free.coefficientMap a f) ≫ hom j a Y =
      hom j a X ≫ Free.coefficientMap (j.obj a) f := by
  apply (homEquiv j a X (Free.object (j.obj a) Y)).injective
  rw [homEquiv_coefficient, homEquiv_postcomp, homEquiv_hom, homEquiv_hom]
  have h := (Free.adjunction (j.obj a)).homEquiv_naturality_left f
    (𝟙 (Free.object (j.obj a) Y))
  rw [Free.adjunction_homEquiv, Category.comp_id] at h
  have h' := Free.evaluate_postcomp (j.obj a) X
    (𝟙 (Free.object (j.obj a) X)) (Free.coefficientMap (j.obj a) f)
  rw [Category.id_comp] at h'
  exact h.symm.trans h'

/-- The same coefficient morphisms preserve the complete inverse map. -/
theorem inv_coefficient_naturality (a : A) {X Y : V} (f : X ⟶ Y) :
    Free.coefficientMap (j.obj a) f ≫ inv j a Y =
      inv j a X ≫ (leftKan j).map (Free.coefficientMap a f) := by
  apply (cancel_mono (iso j a Y).hom).1
  rw [iso_hom]
  rw [Category.assoc, inv_hom_id, Category.comp_id,
    Category.assoc, hom_coefficient, ← Category.assoc, inv_hom_id, Category.id_comp]

/-- Both full coefficient functors are compared by the same original Kan/free maps. -/
def functorIso (a : A) : Free.functor a ⋙ leftKan j ≅ Free.functor (j.obj a) :=
  NatIso.ofComponents (iso j a) (fun f => hom_coefficient j a f)

/-- The complete coefficient family has the original forward transpose at every object. -/
theorem functorIso_hom_app (a : A) (X : V) :
    (functorIso j a).hom.app X = hom j a X := rfl

/-- The complete coefficient family has the original inverse extension at every object. -/
theorem functorIso_inv_app (a : A) (X : V) :
    (functorIso j a).inv.app X = inv j a X := rfl

/-- The original contravariant source map is carried through both actual full Hom maps. -/
theorem hom_source {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    (leftKan j).map (Free.sourceMap e X) ≫ hom j a X =
      hom j a' X ≫ Free.sourceMap (e ≫ j.map a a') X := by
  apply (leftKanHomEquiv j (Free.object a' X) (Free.object (j.obj a) X)).injective
  apply (Free.homEquiv a' X (restrictionObject j (Free.object (j.obj a) X))).injective
  rw [leftKanHomEquiv_naturality_left, leftKanHomEquiv_naturality_right]
  have hu : leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)
      (hom j a X) = FreeHomTransport.map j a X :=
    (leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)).apply_symm_apply
      (FreeHomTransport.map j a X)
  have hu' : leftKanHomEquiv j (Free.object a' X) (Free.object (j.obj a') X)
      (hom j a' X) = FreeHomTransport.map j a' X :=
    (leftKanHomEquiv j (Free.object a' X) (Free.object (j.obj a') X)).apply_symm_apply
      (FreeHomTransport.map j a' X)
  change Free.evaluate a' X (restrictionObject j (Free.object (j.obj a) X))
      (Free.sourceMap e X ≫ leftKanHomEquiv j (Free.object a X)
        (Free.object (j.obj a) X) (hom j a X)) =
    Free.evaluate a' X (restrictionObject j (Free.object (j.obj a) X))
      (leftKanHomEquiv j (Free.object a' X) (Free.object (j.obj a') X) (hom j a' X) ≫
        restrictionMap j (Free.sourceMap (e ≫ j.map a a') X))
  rw [hu, hu', Free.evaluate_sourceMap, FreeHomTransport.map_component,
    FreeHomTransport.evaluate_map]
  have h := Free.evaluate_sourceMap (e ≫ j.map a a') X
    (Free.object (j.obj a) X) (𝟙 (Free.object (j.obj a) X))
  rw [Category.comp_id, component_id, Category.comp_id] at h
  rw [h, whiskerLeft_comp]
  rfl

/-- The inverse preserves the same complete contravariant source transformation. -/
theorem inv_source {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    Free.sourceMap (e ≫ j.map a a') X ≫ inv j a X =
      inv j a' X ≫ (leftKan j).map (Free.sourceMap e X) := by
  apply (cancel_mono (iso j a X).hom).1
  rw [iso_hom]
  rw [Category.assoc, inv_hom_id, Category.comp_id, Category.assoc,
    hom_source, ← Category.assoc, inv_hom_id, Category.id_comp]

end CategoryTheory.EnrichedFunctorCat.LeftKanFreeComparison
