/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Full Hom reflection from an actual coaugmented endofunctor

Both iterated unit families are isomorphisms. Naturality and cancellation
prove their coherence, then give both complete Hom functions and all source
and target naturalities. Any specified class of test objects containing the
actual image and on which the unit is invertible detects precisely the maps
inverted by the functor. No adjunction or desired reflection is given.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory

namespace CategoryTheory.Functor.CoaugmentedReflection

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hunit : ∀ X, IsIso (η.app (F.obj X)))
variable (hmap : ∀ X, IsIso (F.map (η.app X)))

include hunit hmap in
/-- The two whole iterated unit maps agree by their actual naturality squares. -/
theorem map_unit_eq_unit_obj (X : C) : F.map (η.app X) = η.app (F.obj X) := by
  let _ : IsIso (η.app (F.obj X)) := hunit X
  let _ : IsIso (F.map (η.app X)) := hmap X
  let _ : IsIso (η.app (F.obj (F.obj X))) := hunit (F.obj X)
  have h₁ : F.map (η.app (F.obj X)) = η.app (F.obj (F.obj X)) := by
    apply (cancel_epi (η.app (F.obj X))).mp
    simpa only [Functor.id_map, Functor.id_obj] using (η.naturality (η.app (F.obj X))).symm
  have h₂ : F.map (F.map (η.app X)) = F.map (η.app (F.obj X)) := by
    apply (cancel_epi (F.map (η.app X))).mp
    simpa only [Functor.id_map, Functor.id_obj, F.map_comp] using
      (F.congr_map (η.naturality (η.app X))).symm
  have h₃ : F.map (η.app X) ≫ η.app (F.obj (F.obj X)) =
      η.app (F.obj X) ≫ F.map (F.map (η.app X)) := by
    simpa only [Functor.id_map, Functor.id_obj] using η.naturality (F.map (η.app X))
  rw [h₂, h₁] at h₃
  exact (cancel_mono (η.app (F.obj (F.obj X)))).mp h₃

/-- Both complete Hom functions use the actual functor, unit and inverse unit. -/
def unitHomEquiv (X Z : C) [IsIso (η.app Z)] : (F.obj X ⟶ Z) ≃ (X ⟶ Z) where
  toFun g := η.app X ≫ g
  invFun f := F.map f ≫ CategoryTheory.inv (η.app Z)
  left_inv g := by
    calc
      F.map (η.app X ≫ g) ≫ CategoryTheory.inv (η.app Z) =
          (η.app (F.obj X) ≫ F.map g) ≫ CategoryTheory.inv (η.app Z) := by
        rw [F.map_comp, map_unit_eq_unit_obj F η hunit hmap X]
      _ = (g ≫ η.app Z) ≫ CategoryTheory.inv (η.app Z) := by
        rw [← η.naturality g, Functor.id_map]
      _ = g := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  right_inv f := by
    calc
      η.app X ≫ (F.map f ≫ CategoryTheory.inv (η.app Z)) =
          (f ≫ η.app Z) ≫ CategoryTheory.inv (η.app Z) := by
        rw [← Category.assoc, ← η.naturality f, Functor.id_map]
      _ = f := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The full forward function is precomposition with the original unit. -/
theorem unitHomEquiv_apply (X Z : C) [IsIso (η.app Z)] (g : F.obj X ⟶ Z) :
    unitHomEquiv F η hunit hmap X Z g = η.app X ≫ g := rfl

/-- The full inverse function is the functor map followed by the actual inverse unit. -/
theorem unitHomEquiv_symm_apply (X Z : C) [IsIso (η.app Z)] (f : X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z).symm f = F.map f ≫ CategoryTheory.inv (η.app Z) := rfl

/-- Every source map preserves the whole forward Hom function. -/
theorem unitHomEquiv_source {X X' : C} (a : X' ⟶ X) (Z : C)
    [IsIso (η.app Z)] (g : F.obj X ⟶ Z) :
    unitHomEquiv F η hunit hmap X' Z (F.map a ≫ g) =
      a ≫ unitHomEquiv F η hunit hmap X Z g := by
  change η.app X' ≫ (F.map a ≫ g) = a ≫ (η.app X ≫ g)
  rw [← Category.assoc, ← η.naturality a, Functor.id_map, Category.assoc]

/-- Every source map preserves the whole inverse Hom function. -/
theorem unitHomEquiv_source_symm {X X' : C} (a : X' ⟶ X) (Z : C)
    [IsIso (η.app Z)] (f : X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X' Z).symm (a ≫ f) =
      F.map a ≫ (unitHomEquiv F η hunit hmap X Z).symm f := by
  rw [unitHomEquiv_symm_apply, unitHomEquiv_symm_apply, F.map_comp, Category.assoc]

/-- Every target map preserves the full forward function on fixed objects. -/
theorem unitHomEquiv_target (X : C) {Z Z' : C}
    [IsIso (η.app Z)] [IsIso (η.app Z')] (b : Z ⟶ Z') (g : F.obj X ⟶ Z) :
    unitHomEquiv F η hunit hmap X Z' (g ≫ b) =
      unitHomEquiv F η hunit hmap X Z g ≫ b := (Category.assoc _ _ _).symm

/-- Every target map preserves the full inverse function on fixed objects. -/
theorem unitHomEquiv_target_symm (X : C) {Z Z' : C}
    [IsIso (η.app Z)] [IsIso (η.app Z')] (b : Z ⟶ Z') (f : X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z').symm (f ≫ b) =
      (unitHomEquiv F η hunit hmap X Z).symm f ≫ b := by
  apply (unitHomEquiv F η hunit hmap X Z').injective
  rw [Equiv.apply_symm_apply, unitHomEquiv_target, Equiv.apply_symm_apply]

include hunit hmap in
/-- Every fixed target has the actual full unit precomposition bijection. -/
theorem precomp_unit_bijective (X Z : C) [IsIso (η.app Z)] :
    Function.Bijective (fun g : F.obj X ⟶ Z => η.app X ≫ g) :=
  (unitHomEquiv F η hunit hmap X Z).bijective

variable (P : C → Prop) (himage : ∀ X, P (F.obj X))
variable (hfixed : ∀ Z, P Z → IsIso (η.app Z))

include η hunit hmap himage hfixed in
/-- A specified fixed test class containing the actual image detects all functor-inverted maps. -/
theorem map_isIso_iff_fixed_homtests {X Y : C} (f : X ⟶ Y) :
    IsIso (F.map f) ↔
      ∀ Z, P Z → Function.Bijective (fun g : Y ⟶ Z => f ≫ g) := by
  constructor
  · intro hf Z hZ
    let _ : IsIso (η.app Z) := hfixed Z hZ
    let eX := unitHomEquiv F η hunit hmap X Z
    let eY := unitHomEquiv F η hunit hmap Y Z
    have hF : Function.Bijective (fun g : F.obj Y ⟶ Z => F.map f ≫ g) :=
      (isIso_iff_coyoneda_map_bijective (F.map f)).mp hf Z
    have h := eX.bijective.comp (hF.comp eY.symm.bijective)
    change Function.Bijective (fun g : Y ⟶ Z => eX (F.map f ≫ eY.symm g)) at h
    have he : (fun g : Y ⟶ Z => eX (F.map f ≫ eY.symm g)) =
        (fun g : Y ⟶ Z => f ≫ g) := by
      funext g
      exact (unitHomEquiv_source F η hunit hmap f Z (eY.symm g)).trans
        (congrArg (fun a => f ≫ a) (eY.apply_symm_apply g))
    rw [he] at h
    exact h
  · intro h
    let _ : IsIso (η.app (F.obj X)) := hunit X
    let _ : IsIso (η.app (F.obj Y)) := hunit Y
    let eXX := unitHomEquiv F η hunit hmap X (F.obj X)
    let eYX := unitHomEquiv F η hunit hmap Y (F.obj X)
    let eXY := unitHomEquiv F η hunit hmap X (F.obj Y)
    let eYY := unitHomEquiv F η hunit hmap Y (F.obj Y)
    obtain ⟨g, hg⟩ := (h (F.obj X) (himage X)).surjective (η.app X)
    let r : F.obj Y ⟶ F.obj X := eYX.symm g
    have hr : F.map f ≫ r = 𝟙 (F.obj X) := by
      apply eXX.injective
      calc
        eXX (F.map f ≫ r) = f ≫ eYX r :=
          unitHomEquiv_source F η hunit hmap f (F.obj X) r
        _ = f ≫ g := congrArg (fun a => f ≫ a) (eYX.apply_symm_apply g)
        _ = η.app X := hg
        _ = eXX (𝟙 (F.obj X)) := (Category.comp_id _).symm
    have hl : r ≫ F.map f = 𝟙 (F.obj Y) := by
      apply eYY.injective
      apply (h (F.obj Y) (himage Y)).injective
      calc
        f ≫ eYY (r ≫ F.map f) = eXY (F.map f ≫ (r ≫ F.map f)) :=
          (unitHomEquiv_source F η hunit hmap f (F.obj Y) (r ≫ F.map f)).symm
        _ = eXY (F.map f) := by rw [← Category.assoc, hr, Category.id_comp]
        _ = f ≫ eYY (𝟙 (F.obj Y)) := by
          exact (congrArg eXY (Category.comp_id (F.map f)).symm).trans
            (unitHomEquiv_source F η hunit hmap f (F.obj Y) (𝟙 (F.obj Y)))
    exact (Iso.mk (F.map f) r hr hl).isIso_hom

end CategoryTheory.Functor.CoaugmentedReflection


namespace CategoryTheory.Functor.CoaugmentedReflection

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) (η : 𝟭 C ⟶ F)
variable (hunit : ∀ X, IsIso (η.app (F.obj X)))
variable (hmap : ∀ X, IsIso (F.map (η.app X)))

/-- The complete inverse is characterized by its composite with the original unit. -/
theorem unitHomEquiv_characteristic (X Z : C) [IsIso (η.app Z)]
    (f : X ⟶ Z) (g : F.obj X ⟶ Z) :
    (unitHomEquiv F η hunit hmap X Z).symm f = g ↔ η.app X ≫ g = f := by
  constructor
  · intro h
    rw [← h]
    exact (unitHomEquiv F η hunit hmap X Z).apply_symm_apply f
  · intro h
    apply (unitHomEquiv F η hunit hmap X Z).injective
    exact ((unitHomEquiv F η hunit hmap X Z).apply_symm_apply f).trans h.symm

include hunit hmap in
/-- The original unit followed by the entire inverse Hom function is the original arrow. -/
theorem unitHomEquiv_right_triangle (X Z : C) [IsIso (η.app Z)] (f : X ⟶ Z) :
    η.app X ≫ (F.map f ≫ CategoryTheory.inv (η.app Z)) = f :=
  (unitHomEquiv F η hunit hmap X Z).apply_symm_apply f

include hunit hmap in
/-- The entire inverse Hom function followed by the original forward function is unchanged. -/
theorem unitHomEquiv_left_triangle (X Z : C) [IsIso (η.app Z)] (g : F.obj X ⟶ Z) :
    F.map (η.app X ≫ g) ≫ CategoryTheory.inv (η.app Z) = g :=
  (unitHomEquiv F η hunit hmap X Z).symm_apply_apply g

variable (P : ObjectProperty C) (himage : ∀ X, P (F.obj X))
variable (hfixed : ∀ Z, P Z → IsIso (η.app Z))

/-- The actual original functor takes values in the specified full category of test objects. -/
def testFunctor : C ⥤ P.FullSubcategory := ObjectProperty.lift P F himage

/-- The target unit Iso is the actual original unit at that specified test object. -/
def testUnitIso (Z : P.FullSubcategory) : Z.obj ≅ F.obj Z.obj := by
  let _ : IsIso (η.app Z.obj) := hfixed Z.obj Z.property
  exact asIso (η.app Z.obj)

/-- The full-category Hom correspondence uses the same complete original unit functions. -/
def testHomEquiv (X : C) (Z : P.FullSubcategory) :
    ((testFunctor F P himage).obj X ⟶ Z) ≃ (X ⟶ Z.obj) := by
  let _ : IsIso (η.app Z.obj) := hfixed Z.obj Z.property
  exact (P.fullyFaithfulι.homEquiv (X := (testFunctor F P himage).obj X) (Y := Z)).trans
    (unitHomEquiv F η hunit hmap X Z.obj)

/-- The entire full-category forward function is the same original unit precomposition. -/
theorem testHomEquiv_apply (X : C) (Z : P.FullSubcategory)
    (g : (testFunctor F P himage).obj X ⟶ Z) :
    testHomEquiv F η hunit hmap P himage hfixed X Z g = η.app X ≫ g.hom := rfl

/-- The full-category inverse uses the original functor and original unit inverse. -/
theorem testHomEquiv_symm_apply (X : C) (Z : P.FullSubcategory) (f : X ⟶ Z.obj) :
    ((testHomEquiv F η hunit hmap P himage hfixed X Z).symm f).hom =
      F.map f ≫ (testUnitIso F η P hfixed Z).inv := rfl

/-- The actual unit-Hom functions derive an adjunction to the full test category. -/
def testAdjunction : testFunctor F P himage ⊣ P.ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := testHomEquiv F η hunit hmap P himage hfixed
      homEquiv_naturality_left_symm := by
        intro X' X Z a f
        let _ : IsIso (η.app Z.obj) := hfixed Z.obj Z.property
        apply ObjectProperty.hom_ext
        change (unitHomEquiv F η hunit hmap X' Z.obj).symm (a ≫ f) =
          F.map a ≫ (unitHomEquiv F η hunit hmap X Z.obj).symm f
        exact unitHomEquiv_source_symm F η hunit hmap a Z.obj f
      homEquiv_naturality_right := by
        intro X Z Z' g b
        change η.app X ≫ (g.hom ≫ b.hom) = (η.app X ≫ g.hom) ≫ b.hom
        exact (Category.assoc _ _ _).symm }

/-- Every component of the derived adjunction unit is the actual original coaugmentation. -/
theorem testAdjunction_unit_app (X : C) :
    (testAdjunction F η hunit hmap P himage hfixed).unit.app X = η.app X := by
  change η.app X ≫ (𝟙 (F.obj X)) = η.app X
  exact Category.comp_id _

/-- Every component of the derived counit is the same actual target-unit inverse. -/
theorem testAdjunction_counit_app (Z : P.FullSubcategory) :
    ((testAdjunction F η hunit hmap P himage hfixed).counit.app Z).hom =
      (testUnitIso F η P hfixed Z).inv := by
  change F.map (𝟙 Z.obj) ≫ (testUnitIso F η P hfixed Z).inv = _
  rw [F.map_id, Category.id_comp]

/-- The actual full-category left triangle retains the original coaugmentation. -/
theorem testAdjunction_left_triangle (X : C) :
    (testFunctor F P himage).map (η.app X) ≫
      (testAdjunction F η hunit hmap P himage hfixed).counit.app
        ((testFunctor F P himage).obj X) = 𝟙 ((testFunctor F P himage).obj X) := by
  have h := (testAdjunction F η hunit hmap P himage hfixed).left_triangle_components X
  rw [testAdjunction_unit_app] at h
  exact h

/-- The actual full-category right triangle retains the original test-object unit. -/
theorem testAdjunction_right_triangle (Z : P.FullSubcategory) :
    η.app Z.obj ≫ ((testAdjunction F η hunit hmap P himage hfixed).counit.app Z).hom =
      𝟙 Z.obj := by
  have h := (testAdjunction F η hunit hmap P himage hfixed).right_triangle_components Z
  rw [testAdjunction_unit_app] at h
  exact h

/-- The adjunction Hom function is exactly the original unit precomposition on every arrow. -/
theorem testAdjunction_homEquiv_apply (X : C) (Z : P.FullSubcategory)
    (g : (testFunctor F P himage).obj X ⟶ Z) :
    (testAdjunction F η hunit hmap P himage hfixed).homEquiv X Z g = η.app X ≫ g.hom := by
  rw [Adjunction.homEquiv_unit, testAdjunction_unit_app]
  rfl

/-- The entire derived adjunction Hom equivalence equals the original Hom equivalence. -/
theorem testAdjunction_homEquiv (X : C) (Z : P.FullSubcategory) :
    (testAdjunction F η hunit hmap P himage hfixed).homEquiv X Z =
      testHomEquiv F η hunit hmap P himage hfixed X Z := by
  apply Equiv.ext
  intro g
  exact testAdjunction_homEquiv_apply F η hunit hmap P himage hfixed X Z g

end CategoryTheory.Functor.CoaugmentedReflection
