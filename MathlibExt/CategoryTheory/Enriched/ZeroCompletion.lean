/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Restriction
public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Logic.Small.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! Genuine enriched added-zero completion and diagram equivalence. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

universe uV vV uA w

namespace CategoryTheory

/- The base parameter tags the actual enrichment, as in ForgetEnrichment. -/
/-- Objects of `A` with one added object, tagged by the enriching category `V`. -/
@[nolint unusedArguments]
def EnrichedZeroCompletion (_V : Type uV) (A : Type uA) : Type uA := Option A

namespace EnrichedZeroCompletion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [EnrichedCategory V A]

/-- A tensor with a zero left factor is a zero object. -/
theorem tensor_isZero_left {X : V} (hX : IsZero X) (Y : V) : IsZero (X ⊗ Y) :=
  Functor.map_isZero (tensorRight Y) hX

omit [BraidedCategory V] in
/-- A tensor with a zero right factor is a zero object. -/
theorem tensor_isZero_right (X : V) {Y : V} (hY : IsZero Y) : IsZero (X ⊗ Y) :=
  Functor.map_isZero (tensorLeft X) hY

omit [BraidedCategory V] in
/-- An internal Hom with zero target is a zero object. -/
theorem ihom_isZero_target (X : V) {Y : V} (hY : IsZero Y) :
    IsZero ((ihom X).obj Y) :=
  Functor.map_isZero (ihom X) hY

omit [BraidedCategory V] in
/-- Uncurrying the zero internal-Hom morphism gives the zero morphism. -/
theorem uncurry_zero (X Y Z : V) :
    MonoidalClosed.uncurry (0 : Y ⟶ (ihom X).obj Z) = 0 := by
  have h : X ◁ (0 : Y ⟶ (ihom X).obj Z) = 0 :=
    Functor.map_zero (tensorLeft X) Y ((ihom X).obj Z)
  rw [MonoidalClosed.uncurry_eq, h, zero_comp]

omit [BraidedCategory V] in
/-- The enriched identity of an object vanishes exactly when that object is zero. -/
theorem eId_eq_zero_iff (X : V) : eId V X = 0 ↔ IsZero X := by
  constructor
  · intro h
    have hu := congrArg MonoidalClosed.uncurry h
    rw [MonoidalClosed.enrichedCategorySelf_id, MonoidalClosed.id_eq,
      MonoidalClosed.uncurry_curry, uncurry_zero] at hu
    apply (IsZero.iff_id_eq_zero X).2
    calc
      𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := (Iso.inv_hom_id _).symm
      _ = 0 := by rw [hu, comp_zero]
  · intro hX
    exact (ihom_isZero_target X hX).eq_zero_of_tgt _

/-- Include an original object in the added-zero index. -/
def of (a : A) : EnrichedZeroCompletion V A := some a

/-- The added zero object of the completed enriched index. -/
def zero : EnrichedZeroCompletion V A := none

/-- Original enriched Hom objects, with zero Hom objects whenever an endpoint is added zero. -/
def hom : EnrichedZeroCompletion V A → EnrichedZeroCompletion V A → V
  | some a, some b => a ⟶[V] b
  | _, _ => 0

/-- The original enriched identity on included objects and the zero identity at added zero. -/
def identity : ∀ x : EnrichedZeroCompletion V A, 𝟙_ V ⟶ hom x x
  | none => 0
  | some a => eId V a

/-- Original enriched composition, with zero composition whenever an object is added zero. -/
def composition : ∀ x y z : EnrichedZeroCompletion V A,
    hom x y ⊗ hom y z ⟶ hom x z
  | some a, some b, some c => eComp V a b c
  | _, _, _ => 0

omit [BraidedCategory V] [MonoidalClosed V] in
/-- The completed enriched identity satisfies the left identity law. -/
theorem identity_comp (x y : EnrichedZeroCompletion V A) :
    (λ_ (hom x y)).inv ≫ identity x ▷ hom x y ≫ composition x x y =
      𝟙 (hom x y) := by
  cases x with
  | none => exact (isZero_zero V).eq_of_src _ _
  | some a =>
    cases y with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some b => exact e_id_comp V a b

omit [BraidedCategory V] [MonoidalClosed V] in
/-- The completed enriched identity satisfies the right identity law. -/
theorem comp_identity (x y : EnrichedZeroCompletion V A) :
    (ρ_ (hom x y)).inv ≫ hom x y ◁ identity y ≫ composition x y y =
      𝟙 (hom x y) := by
  cases x with
  | none => exact (isZero_zero V).eq_of_src _ _
  | some a =>
    cases y with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some b => exact e_comp_id V a b

/-- The completed enriched composition satisfies the associativity law. -/
theorem composition_assoc (w x y z : EnrichedZeroCompletion V A) :
    (α_ (hom w x) (hom x y) (hom y z)).inv ≫
        composition w x y ▷ hom y z ≫ composition w y z =
      hom w x ◁ composition x y z ≫ composition w x z := by
  cases w with
  | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
  | some a =>
    cases x with
    | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
    | some b =>
      cases y with
      | none =>
        exact (tensor_isZero_right _
          (tensor_isZero_left (isZero_zero V) _)).eq_of_src _ _
      | some c =>
        cases z with
        | none =>
          exact (tensor_isZero_right _
            (tensor_isZero_right _ (isZero_zero V))).eq_of_src _ _
        | some d => exact e_assoc V a b c d

instance enrichedCategory : EnrichedCategory V (EnrichedZeroCompletion V A) where
  Hom := hom
  id := identity
  comp := composition
  id_comp := identity_comp
  comp_id := comp_identity
  assoc := composition_assoc

/-- The enriched inclusion of the original index into its zero completion. -/
def inclusion : EnrichedFunctor V A (EnrichedZeroCompletion V A) where
  obj := of
  map a b := 𝟙 (a ⟶[V] b)
  map_id a := by
    change eId V a ≫ 𝟙 (a ⟶[V] a) = eId V a
    exact Category.comp_id _
  map_comp a b c := by
    change eComp V a b c ≫ 𝟙 (a ⟶[V] c) =
      (𝟙 (a ⟶[V] b) ⊗ₘ 𝟙 (b ⟶[V] c)) ≫ eComp V a b c
    simp only [Category.comp_id, id_tensorHom_id, Category.id_comp]

/-- The added object is zero in the underlying ordinary category. -/
theorem isZero_added :
    IsZero (ForgetEnrichment.of V (zero : EnrichedZeroCompletion V A)) where
  unique_to Y := ⟨by
    change Unique (𝟙_ V ⟶ hom zero (ForgetEnrichment.to V Y))
    change Unique (𝟙_ V ⟶ (0 : V))
    infer_instance⟩
  unique_from Y := ⟨by
    change Unique (𝟙_ V ⟶ hom (ForgetEnrichment.to V Y) zero)
    cases Y
    all_goals change Unique (𝟙_ V ⟶ (0 : V)); infer_instance⟩

instance underlyingHasZeroObject :
    HasZeroObject (ForgetEnrichment V (EnrichedZeroCompletion V A)) :=
  ⟨⟨ForgetEnrichment.of V zero, isZero_added⟩⟩

/-- Extend an enriched diagram on objects by assigning the chosen zero to the added object. -/
def extendObj (F : EnrichedFunctor V A V) : EnrichedZeroCompletion V A → V
  | none => 0
  | some a => F.obj a

/-- Extend a diagram's enriched maps by zero whenever an endpoint is the added object. -/
def extendMap (F : EnrichedFunctor V A V) :
    ∀ x y : EnrichedZeroCompletion V A,
      hom x y ⟶ (ihom (extendObj F x)).obj (extendObj F y)
  | some a, some b => F.map a b
  | _, _ => 0

omit [BraidedCategory V] in
/-- Extension by zero preserves each enriched identity. -/
theorem extend_identity (F : EnrichedFunctor V A V)
    (x : EnrichedZeroCompletion V A) :
    identity x ≫ extendMap F x x = eId V (extendObj F x) := by
  cases x with
  | none => exact (ihom_isZero_target (0 : V) (isZero_zero V)).eq_of_tgt _ _
  | some a => exact F.map_id a

/-- Extension by zero preserves each enriched composition. -/
theorem extend_composition (F : EnrichedFunctor V A V)
    (x y z : EnrichedZeroCompletion V A) :
    composition x y z ≫ extendMap F x z =
      (extendMap F x y ⊗ₘ extendMap F y z) ≫
        eComp V (extendObj F x) (extendObj F y) (extendObj F z) := by
  cases x with
  | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
  | some a =>
    cases y with
    | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
    | some b =>
      cases z with
      | none => exact (tensor_isZero_right _ (isZero_zero V)).eq_of_src _ _
      | some c => exact F.map_comp a b c

/-- Extend an enriched diagram by the chosen zero value at the added object. -/
def extend (F : EnrichedFunctor V A V) :
    EnrichedFunctor V (EnrichedZeroCompletion V A) V where
  obj := extendObj F
  map := extendMap F
  map_id := extend_identity F
  map_comp := extend_composition F

/-- Every enriched diagram on the completed index has zero value at the added object. -/
theorem diagram_added_isZero (F : EnrichedFunctor V (EnrichedZeroCompletion V A) V) :
    IsZero (F.obj zero) := by
  apply (eId_eq_zero_iff _).1
  have h := F.map_id zero
  change (0 : 𝟙_ V ⟶ (0 : V)) ≫ F.map zero zero = eId V (F.obj zero) at h
  have hz : (0 : 𝟙_ V ⟶ (0 : V)) ≫ F.map zero zero =
      (0 : 𝟙_ V ⟶ (ihom (F.obj zero)).obj (F.obj zero)) := zero_comp
  exact h.symm.trans hz

/-- Restrict a completed enriched diagram to the original index objects. -/
def restrict (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    EnrichedFunctorCat V A :=
  EnrichedFunctorCat.restrictionObject inclusion F

omit [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  [EnrichedCategory V A] in
/-- An included original object is distinct from the added zero object. -/
theorem of_ne_zero (a : A) : (of a : EnrichedZeroCompletion V A) ≠ zero :=
  Option.some_ne_none a

omit [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  [EnrichedCategory V A] in
/-- The inclusion of original objects into the completed index is injective. -/
theorem of_injective : Function.Injective (of : A → EnrichedZeroCompletion V A) :=
  Option.some_injective A

/-- The enriched inclusion acts by identity on every original Hom object. -/
theorem inclusion_map (a b : A) :
    inclusion.map a b = 𝟙 (a ⟶[V] b) := rfl

/-- Every original Hom map of the enriched inclusion is an isomorphism. -/
theorem inclusion_map_isIso (a b : A) : IsIso (inclusion.map (V := V) a b) := by
  change IsIso (𝟙 (a ⟶[V] b))
  infer_instance

/-- Extension has literally the chosen zero value at the added object. -/
theorem extend_obj_zero (F : EnrichedFunctor V A V) :
    (extend F).obj zero = (0 : V) := rfl

/-- Extension keeps the original value at an included object. -/
theorem extend_obj_of (F : EnrichedFunctor V A V) (a : A) :
    (extend F).obj (of a) = F.obj a := rfl

/-- Extension keeps the original enriched map between included objects. -/
theorem extend_map_of (F : EnrichedFunctor V A V) (a b : A) :
    (extend F).map (of a) (of b) = F.map a b := rfl

/-- An extended enriched map out of the added object is zero. -/
theorem extend_map_zero_left (F : EnrichedFunctor V A V)
    (x : EnrichedZeroCompletion V A) : (extend F).map zero x = 0 := by
  cases x <;> rfl

/-- An extended enriched map into the added object is zero. -/
theorem extend_map_zero_right (F : EnrichedFunctor V A V)
    (x : EnrichedZeroCompletion V A) : (extend F).map x zero = 0 := by
  cases x <;> rfl

/-- Extend a graded natural transformation by a zero component at the added object. -/
def extendGraded {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P F G) : GradedNatTrans P (extend F) (extend G) where
  app x := match x with
    | none => 0
    | some a => t.app a
  naturality x y := by
    cases x with
    | none => exact (tensor_isZero_right P.1 (isZero_zero V)).eq_of_src _ _
    | some a =>
      cases y with
      | none => exact (tensor_isZero_right P.1 (isZero_zero V)).eq_of_src _ _
      | some b => exact t.naturality a b

/-- An extended graded transformation keeps its component at each original object. -/
theorem extendGraded_app_of {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P F G) (a : A) :
    (extendGraded t).app (of a) = t.app a := rfl

/-- The component of an extended graded transformation at added zero is zero. -/
theorem extendGraded_app_zero {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P F G) : (extendGraded t).app zero = 0 := rfl

/-- Restrict a graded transformation between extended diagrams to the original index. -/
def restrictExtendedGraded {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P (extend F) (extend G)) : GradedNatTrans P F G where
  app a := t.app (of a)
  naturality a b := t.naturality (of a) (of b)

/-- Restricting an extended graded transformation recovers the original transformation. -/
theorem restrict_extend_graded {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P F G) : restrictExtendedGraded (extendGraded t) = t := by
  ext a
  rfl

/-- Extension recovers a graded transformation between two extended diagrams. -/
theorem extend_restrict_graded {P : Center V} {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans P (extend F) (extend G)) :
    extendGraded (restrictExtendedGraded t) = t := by
  ext x
  cases x with
  | none => exact (ihom_isZero_target (0 : V) (isZero_zero V)).eq_of_tgt _ _
  | some a => rfl

/-- Graded transformations between original diagrams correspond to those between extensions. -/
def gradedExtensionEquiv (P : Center V) (F G : EnrichedFunctor V A V) :
    GradedNatTrans P F G ≃ GradedNatTrans P (extend F) (extend G) where
  toFun := extendGraded
  invFun := restrictExtendedGraded
  left_inv := restrict_extend_graded
  right_inv := extend_restrict_graded

/-- Extension by zero identifies the complete graded Hom presheaves. -/
def gradedHomPresheafIso (F G : EnrichedFunctor V A V) :
    enrichedNatTransYoneda F G ≅ enrichedNatTransYoneda (extend F) (extend G) :=
  NatIso.ofComponents
    (fun P =>
      { hom := ↾fun t => extendGraded t
        inv := ↾fun t => restrictExtendedGraded t
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro t
          exact restrict_extend_graded t
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro t
          exact extend_restrict_graded t })
    (by
      intro P Q f
      apply ConcreteCategory.hom_ext
      intro t
      apply GradedNatTrans.ext
      funext x
      cases x with
      | none => exact (ihom_isZero_target (0 : V) (isZero_zero V)).eq_of_tgt _ _
      | some a => rfl)

/-- The completed diagram obtained by extending an original diagram by zero. -/
def extensionObject (F : EnrichedFunctorCat V A) :
    EnrichedFunctorCat V (EnrichedZeroCompletion V A) := ⟨extend F.toEnrichedFunctor⟩

/-- Extend a morphism of enriched diagrams by zero at the added object. -/
def extensionMap {F G : EnrichedFunctorCat V A} (t : F ⟶ G) :
    extensionObject F ⟶ extensionObject G := extendGraded t

/-- Extension keeps the ordinary component of a diagram morphism at an original object. -/
theorem extensionMap_component_of {F G : EnrichedFunctorCat V A} (t : F ⟶ G)
    (a : A) : EnrichedFunctorCat.component (extensionMap t) (of a) =
      EnrichedFunctorCat.component t a := rfl

/-- The added-object component of an extended diagram morphism is zero. -/
theorem extensionMap_component_zero {F G : EnrichedFunctorCat V A} (t : F ⟶ G) :
    EnrichedFunctorCat.component (extensionMap t) zero = (0 : (0 : V) ⟶ 0) :=
  (isZero_zero V).eq_zero_of_src _

/-- The ordinary functor extending enriched diagrams by the chosen added-zero value. -/
def extension : EnrichedFunctorCat V A ⥤
    EnrichedFunctorCat V (EnrichedZeroCompletion V A) where
  obj := extensionObject
  map := extensionMap
  map_id F := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    cases x with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some a =>
      change EnrichedFunctorCat.component (extensionMap (𝟙 F)) (of a) =
        EnrichedFunctorCat.component (𝟙 (extensionObject F)) (of a)
      rw [extensionMap_component_of, EnrichedFunctorCat.component_id,
        EnrichedFunctorCat.component_id]
      rfl
  map_comp t s := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    cases x with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some a =>
      change EnrichedFunctorCat.component (extensionMap (t ≫ s)) (of a) =
        EnrichedFunctorCat.component (extensionMap t ≫ extensionMap s) (of a)
      rw [extensionMap_component_of, EnrichedFunctorCat.component_comp,
        EnrichedFunctorCat.component_comp, extensionMap_component_of,
        extensionMap_component_of]
      rfl

/-- The ordinary functor restricting completed enriched diagrams to the original index. -/
def restriction : EnrichedFunctorCat V (EnrichedZeroCompletion V A) ⥤
    EnrichedFunctorCat V A := EnrichedFunctorCat.restriction inclusion

/-- Restriction keeps every original component of a completed diagram morphism. -/
theorem restriction_map_component
    {F G : EnrichedFunctorCat V (EnrichedZeroCompletion V A)} (t : F ⟶ G) (a : A) :
    EnrichedFunctorCat.component (restriction.map t) a =
      EnrichedFunctorCat.component t (of a) :=
  EnrichedFunctorCat.restrictionMap_component inclusion t a

/-- Restriction keeps the complete original enriched Hom map of a diagram. -/
theorem restriction_obj_fullMap
    (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) (a b : A) :
    (restriction.obj F).toEnrichedFunctor.map a b = F.toEnrichedFunctor.map (of a) (of b) := by
  change 𝟙 (a ⟶[V] b) ≫ F.toEnrichedFunctor.map (of a) (of b) = _
  exact Category.id_comp _

/-- The extension-restriction unit morphism, with identity components at original objects. -/
def unitHom (F : EnrichedFunctorCat V A) : F ⟶ (extension ⋙ restriction).obj F :=
  GradedNatTrans.unitOfComponents (fun a => 𝟙 (F.toEnrichedFunctor.obj a)) (by
    intro a b
    change MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (𝟙 (a ⟶[V] b) ≫ F.toEnrichedFunctor.map a b)
    simp only [Category.comp_id, Category.id_comp, id_tensorHom_id])

/-- The inverse extension-restriction unit morphism, with original identity components. -/
def unitInv (F : EnrichedFunctorCat V A) : (extension ⋙ restriction).obj F ⟶ F :=
  GradedNatTrans.unitOfComponents (fun a => 𝟙 (F.toEnrichedFunctor.obj a)) (by
    intro a b
    change MonoidalClosed.uncurry
        (𝟙 (a ⟶[V] b) ≫ F.toEnrichedFunctor.map a b) ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b)
    simp only [Category.comp_id, Category.id_comp, id_tensorHom_id])

/-- Each original component of the extension-restriction unit is the identity. -/
theorem unitHom_component (F : EnrichedFunctorCat V A) (a : A) :
    EnrichedFunctorCat.component (unitHom F) a = 𝟙 (F.toEnrichedFunctor.obj a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- Each original component of the inverse extension-restriction unit is the identity. -/
theorem unitInv_component (F : EnrichedFunctorCat V A) (a : A) :
    EnrichedFunctorCat.component (unitInv F) a = 𝟙 (F.toEnrichedFunctor.obj a) :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The isomorphism from an original diagram to the restriction of its zero extension. -/
def unitIso (F : EnrichedFunctorCat V A) : F ≅ (extension ⋙ restriction).obj F where
  hom := unitHom F
  inv := unitInv F
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [EnrichedFunctorCat.component_comp, unitHom_component, unitInv_component,
      EnrichedFunctorCat.component_id]
    change 𝟙 (F.toEnrichedFunctor.obj a) ≫ 𝟙 (F.toEnrichedFunctor.obj a) =
      𝟙 (F.toEnrichedFunctor.obj a)
    exact Category.comp_id _
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro a
    rw [EnrichedFunctorCat.component_comp, unitInv_component, unitHom_component,
      EnrichedFunctorCat.component_id]
    change 𝟙 (F.toEnrichedFunctor.obj a) ≫ 𝟙 (F.toEnrichedFunctor.obj a) =
      𝟙 (F.toEnrichedFunctor.obj a)
    exact Category.comp_id _

/-- Counit components use original identities and the zero map from the added zero value. -/
def counitHomComponent (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    ∀ x : EnrichedZeroCompletion V A,
      ((restriction ⋙ extension).obj F).toEnrichedFunctor.obj x ⟶
        F.toEnrichedFunctor.obj x
  | none => 0
  | some a => 𝟙 (F.toEnrichedFunctor.obj (of a))

/-- Inverse counit components use original identities and zero maps to added-zero values. -/
def counitInvComponent (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    ∀ x : EnrichedZeroCompletion V A,
      F.toEnrichedFunctor.obj x ⟶
        ((restriction ⋙ extension).obj F).toEnrichedFunctor.obj x
  | none => 0
  | some a => 𝟙 (F.toEnrichedFunctor.obj (of a))

/-- The completed-diagram counit morphism from restriction followed by zero extension. -/
def counitHom (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    (restriction ⋙ extension).obj F ⟶ F :=
  GradedNatTrans.unitOfComponents (counitHomComponent F) (by
    intro x y
    cases x with
    | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
    | some a =>
      cases y with
      | none => exact (tensor_isZero_right _ (isZero_zero V)).eq_of_src _ _
      | some b =>
        let f : (a ⟶[V] b) ⟶
            (ihom (F.toEnrichedFunctor.obj (of a))).obj
              (F.toEnrichedFunctor.obj (of b)) := F.toEnrichedFunctor.map (of a) (of b)
        change MonoidalClosed.uncurry (𝟙 (a ⟶[V] b) ≫ f) ≫ 𝟙 _ =
          (𝟙 _ ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry f
        simp only [Category.comp_id, Category.id_comp, id_tensorHom_id])

/-- The inverse completed-diagram counit morphism to restriction followed by zero extension. -/
def counitInv (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    F ⟶ (restriction ⋙ extension).obj F :=
  GradedNatTrans.unitOfComponents (counitInvComponent F) (by
    intro x y
    cases x with
    | none => exact (tensor_isZero_right _ (isZero_zero V)).eq_of_src _ _
    | some a =>
      cases y with
      | none => exact (tensor_isZero_right _ (isZero_zero V)).eq_of_src _ _
      | some b =>
        let f : (a ⟶[V] b) ⟶
            (ihom (F.toEnrichedFunctor.obj (of a))).obj
              (F.toEnrichedFunctor.obj (of b)) := F.toEnrichedFunctor.map (of a) (of b)
        change MonoidalClosed.uncurry f ≫ 𝟙 _ =
          (𝟙 _ ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (𝟙 (a ⟶[V] b) ≫ f)
        simp only [Category.comp_id, Category.id_comp, id_tensorHom_id])

/-- The counit morphism has its specified identity or zero component at every index object. -/
theorem counitHom_component (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A))
    (x : EnrichedZeroCompletion V A) :
    EnrichedFunctorCat.component (counitHom F) x = counitHomComponent F x :=
  GradedNatTrans.unitOfComponents_component _ _ x

/-- The inverse counit has its specified identity or zero component at every index object. -/
theorem counitInv_component (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A))
    (x : EnrichedZeroCompletion V A) :
    EnrichedFunctorCat.component (counitInv F) x = counitInvComponent F x :=
  GradedNatTrans.unitOfComponents_component _ _ x

/-- Every completed diagram is isomorphic to its restriction followed by zero extension. -/
def counitIso (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    (restriction ⋙ extension).obj F ≅ F where
  hom := counitHom F
  inv := counitInv F
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    cases x with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some a =>
      change EnrichedFunctorCat.component (counitHom F ≫ counitInv F) (of a) =
        EnrichedFunctorCat.component (𝟙 ((restriction ⋙ extension).obj F)) (of a)
      rw [EnrichedFunctorCat.component_comp, counitHom_component, counitInv_component,
        EnrichedFunctorCat.component_id]
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      exact Category.comp_id _
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro x
    cases x with
    | none => exact (diagram_added_isZero F.toEnrichedFunctor).eq_of_src _ _
    | some a =>
      change EnrichedFunctorCat.component (counitInv F ≫ counitHom F) (of a) =
        EnrichedFunctorCat.component (𝟙 F) (of a)
      rw [EnrichedFunctorCat.component_comp, counitInv_component, counitHom_component,
        EnrichedFunctorCat.component_id]
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      exact Category.comp_id _

/-- The natural extension-restriction unit isomorphism on original diagrams. -/
def unitNatIso : 𝟭 (EnrichedFunctorCat V A) ≅ extension ⋙ restriction :=
  NatIso.ofComponents unitIso (by
    intro F G t
    apply EnrichedFunctorCat.hom_ext
    intro a
    let f : F.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a :=
      EnrichedFunctorCat.component t a
    have hLeft : EnrichedFunctorCat.component (t ≫ unitHom G) a = f :=
      (EnrichedFunctorCat.component_comp t (unitHom G) a).trans
        ((congrArg (fun q : G.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a =>
            f ≫ q) (unitHom_component G a)).trans (Category.comp_id f))
    have hMap : EnrichedFunctorCat.component (restriction.map (extensionMap t)) a = f :=
      (restriction_map_component (extensionMap t) a).trans
        (extensionMap_component_of t a)
    have hPair : EnrichedFunctorCat.component (unitHom F) a ≫
        EnrichedFunctorCat.component (restriction.map (extensionMap t)) a =
        𝟙 (F.toEnrichedFunctor.obj a) ≫ f :=
      congrArg₂ (fun (q : F.toEnrichedFunctor.obj a ⟶ F.toEnrichedFunctor.obj a)
          (r : F.toEnrichedFunctor.obj a ⟶ G.toEnrichedFunctor.obj a) => q ≫ r)
        (unitHom_component F a) hMap
    have hRight : EnrichedFunctorCat.component
        (unitHom F ≫ restriction.map (extensionMap t)) a = f :=
      (EnrichedFunctorCat.component_comp (unitHom F)
        (restriction.map (extensionMap t)) a).trans
        (hPair.trans (Category.id_comp f))
    exact hLeft.trans hRight.symm)

/-- The natural restriction-extension counit isomorphism on completed diagrams. -/
def counitNatIso : restriction ⋙ extension ≅
    𝟭 (EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :=
  NatIso.ofComponents counitIso (by
    intro F G t
    apply EnrichedFunctorCat.hom_ext
    intro x
    cases x with
    | none => exact (isZero_zero V).eq_of_src _ _
    | some a =>
      let f : F.toEnrichedFunctor.obj (of a) ⟶ G.toEnrichedFunctor.obj (of a) :=
        EnrichedFunctorCat.component t (of a)
      have hMap : EnrichedFunctorCat.component ((restriction ⋙ extension).map t) (of a) = f :=
        (extensionMap_component_of (restriction.map t) a).trans
          (restriction_map_component t a)
      have hG : EnrichedFunctorCat.component (counitHom G) (of a) =
          𝟙 (G.toEnrichedFunctor.obj (of a)) := counitHom_component G (of a)
      have hF : EnrichedFunctorCat.component (counitHom F) (of a) =
          𝟙 (F.toEnrichedFunctor.obj (of a)) := counitHom_component F (of a)
      have hLeft : EnrichedFunctorCat.component
          ((restriction ⋙ extension).map t ≫ counitHom G) (of a) = f :=
        (EnrichedFunctorCat.component_comp ((restriction ⋙ extension).map t)
          (counitHom G) (of a)).trans
          ((congrArg₂ (fun
              (q : F.toEnrichedFunctor.obj (of a) ⟶ G.toEnrichedFunctor.obj (of a))
              (r : G.toEnrichedFunctor.obj (of a) ⟶ G.toEnrichedFunctor.obj (of a)) => q ≫ r)
            hMap hG).trans (Category.comp_id f))
      have hRight : EnrichedFunctorCat.component (counitHom F ≫ t) (of a) = f :=
        (EnrichedFunctorCat.component_comp (counitHom F) t (of a)).trans
          ((congrArg₂ (fun
              (q : F.toEnrichedFunctor.obj (of a) ⟶ F.toEnrichedFunctor.obj (of a))
              (r : F.toEnrichedFunctor.obj (of a) ⟶ G.toEnrichedFunctor.obj (of a)) => q ≫ r)
            hF rfl).trans (Category.id_comp f))
      exact hLeft.trans hRight.symm)

/-- The unit and counit satisfy the extension triangle law. -/
theorem extension_triangle (F : EnrichedFunctorCat V A) :
    extension.map (unitHom F) ≫ counitHom (extension.obj F) = 𝟙 (extension.obj F) := by
  apply EnrichedFunctorCat.hom_ext
  intro x
  cases x with
  | none => exact (isZero_zero V).eq_of_src _ _
  | some a =>
    have hFirst : EnrichedFunctorCat.component (extension.map (unitHom F)) (of a) =
        𝟙 (F.toEnrichedFunctor.obj a) :=
      (extensionMap_component_of (unitHom F) a).trans (unitHom_component F a)
    have hSecond : EnrichedFunctorCat.component (counitHom (extension.obj F)) (of a) =
        𝟙 (F.toEnrichedFunctor.obj a) := counitHom_component (extension.obj F) (of a)
    have hPair : EnrichedFunctorCat.component (extension.map (unitHom F)) (of a) ≫
        EnrichedFunctorCat.component (counitHom (extension.obj F)) (of a) =
        𝟙 (F.toEnrichedFunctor.obj a) ≫ 𝟙 (F.toEnrichedFunctor.obj a) :=
      congrArg₂ (fun (q r : F.toEnrichedFunctor.obj a ⟶ F.toEnrichedFunctor.obj a) => q ≫ r)
        hFirst hSecond
    have hLeft : EnrichedFunctorCat.component
        (extension.map (unitHom F) ≫ counitHom (extension.obj F)) (of a) =
        𝟙 (F.toEnrichedFunctor.obj a) :=
      (EnrichedFunctorCat.component_comp (extension.map (unitHom F))
        (counitHom (extension.obj F)) (of a)).trans
        (hPair.trans (Category.comp_id _))
    exact hLeft.trans (EnrichedFunctorCat.component_id (extension.obj F) (of a)).symm

/-- The unit and counit satisfy the restriction triangle law. -/
theorem restriction_triangle
    (F : EnrichedFunctorCat V (EnrichedZeroCompletion V A)) :
    unitHom (restriction.obj F) ≫ restriction.map (counitHom F) =
      𝟙 (restriction.obj F) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  rw [EnrichedFunctorCat.component_comp, unitHom_component,
    restriction_map_component, counitHom_component, EnrichedFunctorCat.component_id]
  change 𝟙 (F.toEnrichedFunctor.obj (of a)) ≫ 𝟙 (F.toEnrichedFunctor.obj (of a)) =
    𝟙 (F.toEnrichedFunctor.obj (of a))
  exact Category.comp_id _

/-- Original enriched diagrams are equivalent to diagrams on the added-zero completion. -/
def diagramEquivalence : EnrichedFunctorCat V A ≌
    EnrichedFunctorCat V (EnrichedZeroCompletion V A) where
  functor := extension
  inverse := restriction
  unitIso := unitNatIso
  counitIso := counitNatIso
  functor_unitIso_comp F := extension_triangle F

/-- The added-object component of every completed diagram morphism is an isomorphism. -/
theorem component_zero_isIso
    {F G : EnrichedFunctorCat V (EnrichedZeroCompletion V A)} (t : F ⟶ G) :
    IsIso (EnrichedFunctorCat.component t zero) :=
  (diagram_added_isZero F.toEnrichedFunctor).isIso
    (diagram_added_isZero G.toEnrichedFunctor) _

/-- Extension preserves and reflects lifting for a pair of whole diagram arrows. -/
theorem extension_hasLiftingProperty_iff
    {F G X Y : EnrichedFunctorCat V A} (i : F ⟶ G) (p : X ⟶ Y) :
    HasLiftingProperty (extension.map i) (extension.map p) ↔ HasLiftingProperty i p := by
  let _ : (extension (V := V) (A := A)).IsEquivalence :=
    inferInstanceAs (diagramEquivalence.functor.IsEquivalence)
  exact Functor.hasLiftingProperty_iff_of_isEquivalence extension i p

/-- Restriction preserves and reflects lifting for a pair of whole completed diagram arrows. -/
theorem restriction_hasLiftingProperty_iff
    {F G X Y : EnrichedFunctorCat V (EnrichedZeroCompletion V A)}
    (i : F ⟶ G) (p : X ⟶ Y) :
    HasLiftingProperty (restriction.map i) (restriction.map p) ↔ HasLiftingProperty i p := by
  let _ : (restriction (V := V) (A := A)).IsEquivalence :=
    inferInstanceAs (diagramEquivalence.inverse.IsEquivalence)
  exact Functor.hasLiftingProperty_iff_of_isEquivalence restriction i p

/-- An enriched diagram with zero value at every original object is itself a zero object. -/
theorem diagram_isZero_of_obj_isZero (F : EnrichedFunctorCat V A)
    (hF : ∀ a : A, IsZero (F.toEnrichedFunctor.obj a)) : IsZero F where
  unique_to G := ⟨
    { default := GradedNatTrans.unitOfComponents (fun a => (hF a).to_ _) (by
        intro a b
        exact (tensor_isZero_left (hF a) _).eq_of_src _ _)
      uniq := fun t => by
        apply EnrichedFunctorCat.hom_ext
        intro a
        exact (hF a).eq_of_src _ _ }⟩
  unique_from G := ⟨
    { default := GradedNatTrans.unitOfComponents (fun a => (hF a).from_ _) (by
        intro a b
        exact (hF b).eq_of_tgt _ _)
      uniq := fun t => by
        apply EnrichedFunctorCat.hom_ext
        intro a
        exact (hF a).eq_of_tgt _ _ }⟩

/-- Every value of a free diagram at the added zero index is a zero object. -/
theorem freeAtAdded_obj_isZero (X : V) (y : EnrichedZeroCompletion V A) :
    IsZero ((EnrichedFunctorCat.Free.object zero X).toEnrichedFunctor.obj y) := by
  change IsZero (X ⊗ hom zero y)
  cases y <;> exact tensor_isZero_right X (isZero_zero V)

/-- The whole free enriched diagram at the added zero index is a zero object. -/
theorem freeAtAdded_isZero (X : V) :
    IsZero (EnrichedFunctorCat.Free.object (zero : EnrichedZeroCompletion V A) X) :=
  diagram_isZero_of_obj_isZero _ (freeAtAdded_obj_isZero X)

omit [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
  [HasZeroObject V] [EnrichedCategory V A] in
/-- Adjoining the added zero object preserves smallness in the same universe. -/
theorem completion_small [Small.{w} A] : Small.{w} (EnrichedZeroCompletion V A) := by
  apply small_of_injective.{w} (f := (Equiv.optionCongr (equivShrink.{w} A)).toFun)
  exact (Equiv.optionCongr (equivShrink.{w} A)).injective








end EnrichedZeroCompletion
end CategoryTheory

universe uB vA

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

attribute [local instance] Enriched.prodCategory

/-- Extend an index functor on objects, fixing added zero and mapping included objects. -/
def mapIndexObj (F : EnrichedFunctor V A B) : EnrichedZeroCompletion V A →
    EnrichedZeroCompletion V B
  | none => zero
  | some a => of (F.obj a)

/-- Extend an index functor's original enriched Hom maps by zero at added endpoints. -/
def mapIndexMap (F : EnrichedFunctor V A B) :
    ∀ x y : EnrichedZeroCompletion V A,
      (x ⟶[V] y) ⟶ (mapIndexObj F x ⟶[V] mapIndexObj F y)
  | some a, some b => F.map a b
  | _, _ => 0

/-- Extend an enriched index functor while fixing the added zero object. -/
def mapIndex (F : EnrichedFunctor V A B) :
    EnrichedFunctor V (EnrichedZeroCompletion V A) (EnrichedZeroCompletion V B) where
  obj := mapIndexObj F
  map := mapIndexMap F
  map_id x := by
    cases x with
    | none => exact (isZero_zero V).eq_of_tgt _ _
    | some a => exact F.map_id a
  map_comp x y z := by
    cases x with
    | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
    | some a =>
      cases y with
      | none => exact (tensor_isZero_left (isZero_zero V) _).eq_of_src _ _
      | some b =>
        cases z with
        | none => exact (tensor_isZero_right _ (isZero_zero V)).eq_of_src _ _
        | some c => exact F.map_comp a b c

/-- The completed index functor fixes the added zero object literally. -/
theorem mapIndex_obj_zero (F : EnrichedFunctor V A B) : (mapIndex F).obj zero = zero := rfl

/-- The completed index functor sends an included object to its included original image. -/
theorem mapIndex_obj_of (F : EnrichedFunctor V A B) (a : A) :
    (mapIndex F).obj (of a) = of (F.obj a) := rfl

/-- The completed index functor retains its original enriched Hom maps. -/
theorem mapIndex_map_of (F : EnrichedFunctor V A B) (a b : A) :
    (mapIndex F).map (of a) (of b) = F.map a b := rfl

/-- The enriched Hom object out of the added zero is a zero object. -/
theorem hom_zero_left_isZero (x : EnrichedZeroCompletion V A) :
    IsZero (zero ⟶[V] x) := by
  cases x <;> exact isZero_zero V

/-- The enriched Hom object into the added zero is a zero object. -/
theorem hom_zero_right_isZero (x : EnrichedZeroCompletion V A) :
    IsZero (x ⟶[V] zero) := by
  cases x <;> exact isZero_zero V

/-- Merge a pair of completed objects, collapsing any added-zero factor to added zero. -/
def prodMergeObj : (EnrichedZeroCompletion V A × EnrichedZeroCompletion V B) →
    EnrichedZeroCompletion V (A × B)
  | (some a, some b) => of (a, b)
  | _ => zero

omit [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  [EnrichedCategory V A] [EnrichedCategory V B] in
/-- A completed product pair merges to zero or consists of two original objects. -/
theorem prodMerge_cases (x : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B) :
    prodMergeObj x = zero ∨ ∃ a b, x = (of a, of b) := by
  rcases x with ⟨x₁, x₂⟩
  cases x₁ with
  | none => exact Or.inl rfl
  | some a =>
    cases x₂ with
    | none => exact Or.inl rfl
    | some b => exact Or.inr ⟨a, b, rfl⟩

/-- Hom objects out of a product pair collapsed to added zero are zero objects. -/
theorem prodHom_isZero_left
    (x y : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B)
    (hx : prodMergeObj x = zero) : IsZero (x ⟶[V] y) := by
  rcases x with ⟨x₁, x₂⟩
  cases x₁ with
  | none => exact tensor_isZero_left (hom_zero_left_isZero y.1) _
  | some a =>
    cases x₂ with
    | none => exact tensor_isZero_right _ (hom_zero_left_isZero y.2)
    | some b =>
      change (some (a, b) : Option (A × B)) = none at hx
      cases hx

/-- Hom objects into a product pair collapsed to added zero are zero objects. -/
theorem prodHom_isZero_right
    (x y : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B)
    (hy : prodMergeObj y = zero) : IsZero (x ⟶[V] y) := by
  rcases y with ⟨y₁, y₂⟩
  cases y₁ with
  | none => exact tensor_isZero_left (hom_zero_right_isZero x.1) _
  | some a =>
    cases y₂ with
    | none => exact tensor_isZero_right _ (hom_zero_right_isZero x.2)
    | some b =>
      change (some (a, b) : Option (A × B)) = none at hy
      cases hy

/-- Merge enriched product Hom objects by identity on original pairs and zero otherwise. -/
def prodMergeMap : ∀ x y : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B,
    (x ⟶[V] y) ⟶ (prodMergeObj x ⟶[V] prodMergeObj y)
  | (some a, some b), (some a', some b') => 𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b'))
  | _, _ => 0

/-- The enriched functor merging completed product indices and collapsing added-zero factors. -/
def prodMerge : EnrichedFunctor V
    (EnrichedZeroCompletion V A × EnrichedZeroCompletion V B)
    (EnrichedZeroCompletion V (A × B)) where
  obj := prodMergeObj
  map := prodMergeMap
  map_id x := by
    rcases prodMerge_cases x with hx | ⟨a, b, rfl⟩
    · have h : IsZero (prodMergeObj x ⟶[V] prodMergeObj x) := by
        rw [hx]
        exact isZero_zero V
      exact h.eq_of_tgt _ _
    · change eId V (a, b) ≫ 𝟙 ((a, b) ⟶[V] (a, b)) = eId V (a, b)
      exact Category.comp_id _
  map_comp x y z := by
    rcases prodMerge_cases x with hx | ⟨a, b, rfl⟩
    · exact (tensor_isZero_left (prodHom_isZero_left x y hx) _).eq_of_src _ _
    · rcases prodMerge_cases y with hy | ⟨a', b', rfl⟩
      · exact (tensor_isZero_left (prodHom_isZero_right _ y hy) _).eq_of_src _ _
      · rcases prodMerge_cases z with hz | ⟨a'', b'', rfl⟩
        · exact (tensor_isZero_right _ (prodHom_isZero_right _ z hz)).eq_of_src _ _
        · change eComp V (a, b) (a', b') (a'', b'') ≫
              𝟙 ((a, b) ⟶[V] (a'', b'')) =
            (𝟙 ((a, b) ⟶[V] (a', b')) ⊗ₘ 𝟙 ((a', b') ⟶[V] (a'', b''))) ≫
              eComp V (a, b) (a', b') (a'', b'')
          simp only [Category.comp_id, id_tensorHom_id, Category.id_comp]

/-- Merging two included original objects gives their included original pair. -/
theorem prodMerge_obj_of (a : A) (b : B) :
    (prodMerge (V := V)).obj (of a, of b) = of (a, b) := rfl

/-- Merging original product Hom objects acts by the identity. -/
theorem prodMerge_map_of (a a' : A) (b b' : B) :
    (prodMerge (V := V)).map (of a, of b) (of a', of b') =
      𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) := rfl

/-- The product-merge Hom map is zero when its source pair merges to added zero. -/
theorem prodMerge_map_eq_zero_left
    (x y : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B)
    (hx : (prodMerge (V := V)).obj x = zero) : (prodMerge (V := V)).map x y = 0 := by
  have h : IsZero (prodMergeObj x ⟶[V] prodMergeObj y) := by
    rw [show prodMergeObj x = zero from hx]
    exact hom_zero_left_isZero _
  exact h.eq_zero_of_tgt _

/-- The product-merge Hom map is zero when its target pair merges to added zero. -/
theorem prodMerge_map_eq_zero_right
    (x y : EnrichedZeroCompletion V A × EnrichedZeroCompletion V B)
    (hy : (prodMerge (V := V)).obj y = zero) : (prodMerge (V := V)).map x y = 0 := by
  have h : IsZero (prodMergeObj x ⟶[V] prodMergeObj y) := by
    rw [show prodMergeObj y = zero from hy]
    exact hom_zero_right_isZero _
  exact h.eq_zero_of_tgt _


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [EnrichedOrdinaryCategory V A]

attribute [local instance] Enriched.prodCategory

/-- Extend the given enriched tensor with added zero absorbing in either variable. -/
def tensorEnrichment (d : EnrichedMonoidalCategoryData V A) :
    EnrichedFunctor V (EnrichedZeroCompletion V A × EnrichedZeroCompletion V A)
      (EnrichedZeroCompletion V A) :=
  (prodMerge (V := V) (A := A) (B := A)).comp V (mapIndex d.tensorEnrichedFunctor)

/-- The completed enriched tensor retains the tensor of two included original objects. -/
theorem tensorEnrichment_obj_of (d : EnrichedMonoidalCategoryData V A) (a b : A) :
    (tensorEnrichment d).obj (of a, of b) = of (a ⊗ b) := rfl

/-- Added zero is a literal absorbing left factor for the enriched tensor. -/
theorem tensorEnrichment_obj_zero_left (d : EnrichedMonoidalCategoryData V A)
    (x : EnrichedZeroCompletion V A) :
    (tensorEnrichment d).obj (zero, x) = zero := rfl

/-- Added zero is a literal absorbing right factor for the enriched tensor. -/
theorem tensorEnrichment_obj_zero_right (d : EnrichedMonoidalCategoryData V A)
    (x : EnrichedZeroCompletion V A) :
    (tensorEnrichment d).obj (x, zero) = zero := by
  cases x <;> rfl

/-- The completed enriched tensor retains the given tensor map on original Hom objects. -/
theorem tensorEnrichment_map_of (d : EnrichedMonoidalCategoryData V A)
    (a a' b b' : A) :
    (tensorEnrichment d).map (of a, of b) (of a', of b') = d.tensorMap a a' b b' := by
  change 𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) ≫ d.tensorMap a a' b b' = _
  exact Category.id_comp _

/-- The completed enriched tensor preserves every enriched identity. -/
theorem tensorEnrichment_full_id (d : EnrichedMonoidalCategoryData V A)
    (x : EnrichedZeroCompletion V A × EnrichedZeroCompletion V A) :
    eId V x ≫ (tensorEnrichment d).map x x = eId V ((tensorEnrichment d).obj x) :=
  (tensorEnrichment d).map_id x

/-- The completed enriched tensor preserves every enriched composition. -/
theorem tensorEnrichment_full_comp (d : EnrichedMonoidalCategoryData V A)
    (x y z : EnrichedZeroCompletion V A × EnrichedZeroCompletion V A) :
    eComp V x y z ≫ (tensorEnrichment d).map x z =
      ((tensorEnrichment d).map x y ⊗ₘ (tensorEnrichment d).map y z) ≫
        eComp V ((tensorEnrichment d).obj x) ((tensorEnrichment d).obj y)
          ((tensorEnrichment d).obj z) :=
  (tensorEnrichment d).map_comp x y z


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [EnrichedCategory V A]

/-- The underlying ordinary category induced by the completed enriched Hom objects. -/
@[instance_reducible]
def category : Category.{vV} (EnrichedZeroCompletion V A) :=
  inferInstanceAs (Category (ForgetEnrichment V (EnrichedZeroCompletion V A)))

/-- Compatibility of the completed enriched category with its induced ordinary category. -/
@[instance_reducible]
def enrichedOrdinaryCategory :
    @EnrichedOrdinaryCategory V _ _ (EnrichedZeroCompletion V A)
      (category (V := V) (A := A)) :=
  inferInstanceAs (EnrichedOrdinaryCategory V
    (ForgetEnrichment V (EnrichedZeroCompletion V A)))

/-- The added object is zero for the specified induced ordinary category. -/
theorem isZero_added_ordinary :
    @IsZero (EnrichedZeroCompletion V A) (category (V := V) (A := A)) zero :=
  isZero_added

/-- The induced ordinary category of the completed index has the added zero object. -/
theorem hasZeroObject : @HasZeroObject (EnrichedZeroCompletion V A)
    (category (V := V) (A := A)) := underlyingHasZeroObject

end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type uA} [EnrichedCategory V C]
  {D : Type uB} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

/-- Tensor interchange fixes the canonical fourfold point of the monoidal unit. -/
theorem unit_point_interchange :
    let U := 𝟙_ V
    let q : U ⟶ (U ⊗ U) ⊗ (U ⊗ U) := (λ_ U).inv ≫ ((λ_ U).inv ⊗ₘ (λ_ U).inv)
    q ≫ tensorμ U U U U = q := by
  dsimp only
  simp only [tensorμ, braiding_tensorUnit_left]
  monoidal

/-- Reordering four enriched points is compatible with tensor interchange. -/
theorem point_tensor_input
    {H₁ H₂ K₁ K₂ : V} (f₁ : 𝟙_ V ⟶ H₁) (f₂ : 𝟙_ V ⟶ H₂)
    (g₁ : 𝟙_ V ⟶ K₁) (g₂ : 𝟙_ V ⟶ K₂) :
    (λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (f₁ ⊗ₘ g₁)) ⊗ₘ
          ((λ_ (𝟙_ V)).inv ≫ (f₂ ⊗ₘ g₂))) =
      (λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (f₁ ⊗ₘ f₂)) ⊗ₘ
          ((λ_ (𝟙_ V)).inv ≫ (g₁ ⊗ₘ g₂))) ≫ tensorμ H₁ H₂ K₁ K₂ := by
  let U := 𝟙_ V
  let q : U ⟶ (U ⊗ U) ⊗ (U ⊗ U) := (λ_ U).inv ≫ ((λ_ U).inv ⊗ₘ (λ_ U).inv)
  have hq : q ≫ tensorμ U U U U = q := unit_point_interchange
  have h := congrArg (fun k => q ≫ k) (tensorμ_natural f₁ f₂ g₁ g₂)
  simp only [← Category.assoc] at h
  rw [hq] at h
  simpa only [q, U, Category.assoc, tensorHom_comp_tensorHom] using h.symm

/-- Tensor interchange commutes with composition of the two paired point maps. -/
theorem point_tensor_composition
    {H₁ H₂ K₁ K₂ L₁ L₂ : V} (f₁ : 𝟙_ V ⟶ H₁) (f₂ : 𝟙_ V ⟶ H₂)
    (g₁ : 𝟙_ V ⟶ K₁) (g₂ : 𝟙_ V ⟶ K₂)
    (c₁ : H₁ ⊗ K₁ ⟶ L₁) (c₂ : H₂ ⊗ K₂ ⟶ L₂) :
    (λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (f₁ ⊗ₘ g₁) ≫ c₁) ⊗ₘ
          ((λ_ (𝟙_ V)).inv ≫ (f₂ ⊗ₘ g₂) ≫ c₂)) =
      (λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (f₁ ⊗ₘ f₂)) ⊗ₘ
          ((λ_ (𝟙_ V)).inv ≫ (g₁ ⊗ₘ g₂))) ≫
        tensorμ H₁ H₂ K₁ K₂ ≫ (c₁ ⊗ₘ c₂) := by
  simpa only [Category.assoc, tensorHom_comp_tensorHom] using
    congrArg (fun k => k ≫ (c₁ ⊗ₘ c₂)) (point_tensor_input f₁ f₂ g₁ g₂)

/-- Combine two underlying ordinary objects into the underlying enriched-product object. -/
def pointProductObj (x : ForgetEnrichment V C × ForgetEnrichment V D) :
    ForgetEnrichment V (C × D) :=
  ForgetEnrichment.of V (ForgetEnrichment.to V x.1, ForgetEnrichment.to V x.2)

/-- Combine two ordinary morphisms through the tensor of their enriched points. -/
def pointProductMap {x y : ForgetEnrichment V C × ForgetEnrichment V D} (f : x ⟶ y) :
    pointProductObj x ⟶ pointProductObj y :=
  ForgetEnrichment.homOf V ((λ_ (𝟙_ V)).inv ≫
    (ForgetEnrichment.homTo V f.1 ⊗ₘ ForgetEnrichment.homTo V f.2))

omit [BraidedCategory V] in
/-- An underlying ordinary morphism is determined by its enriched point. -/
theorem homTo_injective {x y : ForgetEnrichment V C} :
    Function.Injective (ForgetEnrichment.homTo V : (x ⟶ y) →
      (𝟙_ V ⟶ (ForgetEnrichment.to V x ⟶[V] ForgetEnrichment.to V y))) := by
  intro f g h
  have h' := congrArg (ForgetEnrichment.homOf V) h
  simpa only [ForgetEnrichment.homOf_homTo] using h'

/-- The functor from ordinary product categories to the underlying enriched product. -/
def pointProduct : (ForgetEnrichment V C × ForgetEnrichment V D) ⥤
    ForgetEnrichment V (C × D) where
  obj := pointProductObj
  map := pointProductMap
  map_id x := by
    apply homTo_injective
    rw [ForgetEnrichment.homTo_id]
    change (λ_ (𝟙_ V)).inv ≫
        (ForgetEnrichment.homTo V (𝟙 x.1) ⊗ₘ ForgetEnrichment.homTo V (𝟙 x.2)) =
      eId V (ForgetEnrichment.to V x.1, ForgetEnrichment.to V x.2)
    rw [ForgetEnrichment.homTo_id, ForgetEnrichment.homTo_id]
    rfl
  map_comp {x y z} f g := by
    apply homTo_injective
    rw [ForgetEnrichment.homTo_comp]
    simp only [pointProductMap, ForgetEnrichment.homTo_homOf, pointProductObj,
      ForgetEnrichment.to_of, Category.assoc]
    let f₁ := ForgetEnrichment.homTo V f.1
    let f₂ := ForgetEnrichment.homTo V f.2
    let g₁ := ForgetEnrichment.homTo V g.1
    let g₂ := ForgetEnrichment.homTo V g.2
    let H₁ := ForgetEnrichment.to V x.1 ⟶[V] ForgetEnrichment.to V y.1
    let H₂ := ForgetEnrichment.to V x.2 ⟶[V] ForgetEnrichment.to V y.2
    let K₁ := ForgetEnrichment.to V y.1 ⟶[V] ForgetEnrichment.to V z.1
    let K₂ := ForgetEnrichment.to V y.2 ⟶[V] ForgetEnrichment.to V z.2
    let c₁ := eComp V (ForgetEnrichment.to V x.1) (ForgetEnrichment.to V y.1)
      (ForgetEnrichment.to V z.1)
    let c₂ := eComp V (ForgetEnrichment.to V x.2) (ForgetEnrichment.to V y.2)
      (ForgetEnrichment.to V z.2)
    change (λ_ (𝟙_ V)).inv ≫
        (ForgetEnrichment.homTo V (f.1 ≫ g.1) ⊗ₘ ForgetEnrichment.homTo V (f.2 ≫ g.2)) =
      (λ_ (𝟙_ V)).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (f₁ ⊗ₘ f₂)) ⊗ₘ
          ((λ_ (𝟙_ V)).inv ≫ (g₁ ⊗ₘ g₂))) ≫
        tensorμ H₁ H₂ K₁ K₂ ≫ (c₁ ⊗ₘ c₂)
    rw [ForgetEnrichment.homTo_comp, ForgetEnrichment.homTo_comp]
    simpa only [Category.assoc] using point_tensor_composition f₁ f₂ g₁ g₂ c₁ c₂


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [EnrichedOrdinaryCategory V A]

attribute [local instance] category enrichedOrdinaryCategory hasZeroObject
attribute [local instance] Enriched.prodCategory

/-- The ordinary inclusion of the original index into its enriched zero completion. -/
def ofFunctor : A ⥤ EnrichedZeroCompletion V A :=
  ForgetEnrichment.equivInverse V A ⋙ (inclusion (V := V) (A := A)).forget

omit [MonoidalCategory A] in
/-- The ordinary inclusion sends an original object to its included completed object. -/
theorem ofFunctor_obj (a : A) : (ofFunctor (V := V)).obj a = of a := rfl

omit [MonoidalCategory A] in
/-- The ordinary inclusion represents an original morphism by its enriched point. -/
theorem ofFunctor_map {a b : A} (f : a ⟶ b) :
    (ofFunctor (V := V)).map f = eHomEquiv V f := by
  change (eHomEquiv V f) ≫ 𝟙 (a ⟶[V] b) = eHomEquiv V f
  exact Category.comp_id _

omit [MonoidalCategory A] in
omit [MonoidalCategory A] in
/-- The ordinary inclusion is injective on each original Hom set. -/
theorem ofFunctor_map_injective (a b : A) :
    Function.Injective ((ofFunctor (V := V)).map :
      (a ⟶ b) → ((of a : EnrichedZeroCompletion V A) ⟶ of b)) := by
  intro f g h
  apply (eHomEquiv V).injective
  exact (ofFunctor_map f).symm.trans (h.trans (ofFunctor_map g))

/-- The ordinary tensor functor induced by the completed enriched tensor. -/
def tensorOrdinary (d : EnrichedMonoidalCategoryData V A) :
    (EnrichedZeroCompletion V A × EnrichedZeroCompletion V A) ⥤ EnrichedZeroCompletion V A :=
  (pointProduct (V := V) (C := EnrichedZeroCompletion V A)
      (D := EnrichedZeroCompletion V A)) ⋙ (tensorEnrichment d).forget

/-- The completed ordinary tensor retains the tensor of two included original objects. -/
theorem tensorOrdinary_obj_of (d : EnrichedMonoidalCategoryData V A) (a b : A) :
    (tensorOrdinary d).obj (of a, of b) = of (a ⊗ b) := rfl

/-- Added zero is a literal absorbing left factor for the ordinary tensor. -/
theorem tensorOrdinary_obj_zero_left (d : EnrichedMonoidalCategoryData V A)
    (x : EnrichedZeroCompletion V A) : (tensorOrdinary d).obj (zero, x) = zero := rfl

/-- Added zero is a literal absorbing right factor for the ordinary tensor. -/
theorem tensorOrdinary_obj_zero_right (d : EnrichedMonoidalCategoryData V A)
    (x : EnrichedZeroCompletion V A) : (tensorOrdinary d).obj (x, zero) = zero := by
  cases x <;> rfl

/-- The completed ordinary tensor retains tensor products of included original morphisms. -/
theorem tensorOrdinary_map_ofFunctor (d : EnrichedMonoidalCategoryData V A)
    {a a' b b' : A} (f : a ⟶ a') (g : b ⟶ b') :
    (tensorOrdinary d).map (X := (of a, of b)) (Y := (of a', of b'))
        ((ofFunctor (V := V)).map f, (ofFunctor (V := V)).map g) =
      (ofFunctor (V := V)).map (f ⊗ₘ g) := by
  rw [ofFunctor_map, ofFunctor_map, ofFunctor_map]
  change ((λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V g)) ≫
      (𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b')) ≫ d.tensorMap a a' b b') =
    eHomEquiv V (f ⊗ₘ g)
  simp only [Category.id_comp, Category.assoc]
  exact d.tensorMap_eHomEquiv f g


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [EnrichedOrdinaryCategory V A]

attribute [local instance] category enrichedOrdinaryCategory hasZeroObject

omit [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  [Category A] [MonoidalCategory A] [EnrichedOrdinaryCategory V A] in
/-- Every completed object is the added zero or an included original object. -/
theorem object_cases (x : EnrichedZeroCompletion V A) :
    x = zero ∨ ∃ a : A, x = of a := by
  cases x with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

omit [MonoidalCategory A] in
/-- The ordinary inclusion is surjective on Hom sets between included original objects. -/
theorem ofFunctor_map_surjective (a b : A) :
    Function.Surjective ((ofFunctor (V := V)).map :
      (a ⟶ b) → ((of a : EnrichedZeroCompletion V A) ⟶ of b)) := by
  intro f
  let e : (a ⟶ b) ≃ (𝟙_ V ⟶ (a ⟶[V] b)) := eHomEquiv V
  refine ⟨e.symm f, ?_⟩
  exact (ofFunctor_map _).trans (e.apply_symm_apply f)

/-- Triple tensors have both parenthesizations zero or all three factors are original objects. -/
theorem triple_cases (d : EnrichedMonoidalCategoryData V A)
    (x y z : EnrichedZeroCompletion V A) :
    (((tensorOrdinary d).obj ((tensorOrdinary d).obj (x, y), z) = zero) ∧
      ((tensorOrdinary d).obj (x, (tensorOrdinary d).obj (y, z)) = zero)) ∨
      ∃ a b c, x = of a ∧ y = of b ∧ z = of c := by
  cases x with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some a =>
    cases y with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some b =>
      cases z with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some c => exact Or.inr ⟨a, b, c, rfl, rfl, rfl⟩

/-- An iterated fourfold tensor is zero or all four factors are original objects. -/
theorem quadruple_cases (d : EnrichedMonoidalCategoryData V A)
    (w x y z : EnrichedZeroCompletion V A) :
    (tensorOrdinary d).obj ((tensorOrdinary d).obj ((tensorOrdinary d).obj (w, x), y), z) = zero ∨
      ∃ a b c e, w = of a ∧ x = of b ∧ y = of c ∧ z = of e := by
  cases w with
  | none => exact Or.inl rfl
  | some a =>
    cases x with
    | none => exact Or.inl rfl
    | some b =>
      cases y with
      | none => exact Or.inl rfl
      | some c =>
        cases z with
        | none => exact Or.inl rfl
        | some e => exact Or.inr ⟨a, b, c, e, rfl, rfl, rfl, rfl⟩

omit [MonoidalCategory A] in
/-- Equal original composites have equal composites under the ordinary inclusion. -/
theorem mapped_composites {X Y Z Y' : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') :
    (ofFunctor (V := V)).map f ≫ (ofFunctor (V := V)).map g =
      (ofFunctor (V := V)).map f' ≫ (ofFunctor (V := V)).map g' :=
  ((ofFunctor (V := V)).map_comp f g).symm.trans
    ((congrArg (fun k => (ofFunctor (V := V)).map k) h).trans
      ((ofFunctor (V := V)).map_comp f' g'))

/-- The original associator on included objects, with identity on added-zero tensor values. -/
def completionAssociator (d : EnrichedMonoidalCategoryData V A) :
    ∀ x y z : EnrichedZeroCompletion V A,
      (tensorOrdinary d).obj ((tensorOrdinary d).obj (x, y), z) ≅
        (tensorOrdinary d).obj (x, (tensorOrdinary d).obj (y, z))
  | none, _, _ => Iso.refl zero
  | some _, none, _ => Iso.refl zero
  | some _, some _, none => Iso.refl zero
  | some a, some b, some c => (ofFunctor (V := V)).mapIso (α_ a b c)

/-- The original left unit isomorphism on included objects, with identity at added zero. -/
def completionLeftUnitor (d : EnrichedMonoidalCategoryData V A) :
    ∀ x : EnrichedZeroCompletion V A, (tensorOrdinary d).obj (of (𝟙_ A), x) ≅ x
  | none => Iso.refl zero
  | some a => (ofFunctor (V := V)).mapIso (λ_ a)

/-- The original right unit isomorphism on included objects, with identity at added zero. -/
def completionRightUnitor (d : EnrichedMonoidalCategoryData V A) :
    ∀ x : EnrichedZeroCompletion V A, (tensorOrdinary d).obj (x, of (𝟙_ A)) ≅ x
  | none => Iso.refl zero
  | some a => (ofFunctor (V := V)).mapIso (ρ_ a)

/-- Completed tensor and unit operations, with the added zero absorbing. -/
@[instance_reducible]
def monoidalStruct (d : EnrichedMonoidalCategoryData V A) :
    MonoidalCategoryStruct (EnrichedZeroCompletion V A) where
  tensorObj x y := (tensorOrdinary d).obj (x, y)
  whiskerLeft x {y₁ y₂} f :=
    (tensorOrdinary d).map (X := (x, y₁)) (Y := (x, y₂)) (𝟙 x, f)
  whiskerRight {x₁ x₂} f y :=
    (tensorOrdinary d).map (X := (x₁, y)) (Y := (x₂, y)) (f, 𝟙 y)
  tensorHom {x₁ y₁ x₂ y₂} f g :=
    (tensorOrdinary d).map (X := (x₁, x₂)) (Y := (y₁, y₂)) (f, g)
  tensorUnit := of (𝟙_ A)
  associator := completionAssociator d
  leftUnitor := completionLeftUnitor d
  rightUnitor := completionRightUnitor d

/-- The monoidal category structure extending the original tensor with absorbing added zero. -/
@[instance_reducible]
def monoidalCategory (d : EnrichedMonoidalCategoryData V A) :
    MonoidalCategory (EnrichedZeroCompletion V A) := by
  letI : MonoidalCategoryStruct (EnrichedZeroCompletion V A) := monoidalStruct d
  refine MonoidalCategory.ofTensorHom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y
    exact (tensorOrdinary d).map_id (x, y)
  · intros
    rfl
  · intros
    rfl
  · intros x₁ y₁ z₁ x₂ y₂ z₂ f₁ f₂ g₁ g₂
    exact ((tensorOrdinary d).map_comp (X := (x₁, x₂)) (Y := (y₁, y₂))
      (Z := (z₁, z₂)) (f₁, f₂) (g₁, g₂)).symm
  · intro x₁ x₂ x₃ y₁ y₂ y₃ f₁ f₂ f₃
    rcases triple_cases d x₁ x₂ x₃ with hx | ⟨a, b, c, rfl, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso hx.1)).eq_of_src _ _
    · rcases triple_cases d y₁ y₂ y₃ with hy | ⟨a', b', c', rfl, rfl, rfl⟩
      · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso hy.2)).eq_of_tgt _ _
      · rcases ofFunctor_map_surjective a a' f₁ with ⟨g₁, rfl⟩
        rcases ofFunctor_map_surjective b b' f₂ with ⟨g₂, rfl⟩
        rcases ofFunctor_map_surjective c c' f₃ with ⟨g₃, rfl⟩
        change (tensorOrdinary d).map
              (X := (of (a ⊗ b), of c)) (Y := (of (a' ⊗ b'), of c'))
              ((tensorOrdinary d).map (X := (of a, of b)) (Y := (of a', of b'))
                ((ofFunctor (V := V)).map g₁, (ofFunctor (V := V)).map g₂),
                (ofFunctor (V := V)).map g₃) ≫
            (ofFunctor (V := V)).map (α_ a' b' c').hom =
          (ofFunctor (V := V)).map (α_ a b c).hom ≫
            (tensorOrdinary d).map
              (X := (of a, of (b ⊗ c))) (Y := (of a', of (b' ⊗ c')))
              ((ofFunctor (V := V)).map g₁,
                (tensorOrdinary d).map (X := (of b, of c)) (Y := (of b', of c'))
                  ((ofFunctor (V := V)).map g₂, (ofFunctor (V := V)).map g₃))
        rw [tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor,
          tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
        exact mapped_composites _ _ _ _ (MonoidalCategory.associator_naturality g₁ g₂ g₃)
  · intro x y f
    rcases object_cases x with rfl | ⟨a, rfl⟩
    · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_src _ _
    · rcases object_cases y with rfl | ⟨b, rfl⟩
      · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_tgt _ _
      · rcases ofFunctor_map_surjective a b f with ⟨g, rfl⟩
        change (tensorOrdinary d).map (X := (of (𝟙_ A), of a)) (Y := (of (𝟙_ A), of b))
            (𝟙 (of (𝟙_ A)), (ofFunctor (V := V)).map g) ≫
            (ofFunctor (V := V)).map (λ_ b).hom =
          (ofFunctor (V := V)).map (λ_ a).hom ≫ (ofFunctor (V := V)).map g
        have hid : (𝟙 (of (𝟙_ A)) : (of (𝟙_ A) : EnrichedZeroCompletion V A) ⟶ of (𝟙_ A)) =
            (ofFunctor (V := V)).map (𝟙 (𝟙_ A)) := ((ofFunctor (V := V)).map_id _).symm
        rw [hid, tensorOrdinary_map_ofFunctor]
        apply mapped_composites
        simpa only [id_tensorHom] using MonoidalCategory.leftUnitor_naturality g
  · intro x y f
    rcases object_cases x with rfl | ⟨a, rfl⟩
    · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_src _ _
    · rcases object_cases y with rfl | ⟨b, rfl⟩
      · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_tgt _ _
      · rcases ofFunctor_map_surjective a b f with ⟨g, rfl⟩
        change (tensorOrdinary d).map (X := (of a, of (𝟙_ A))) (Y := (of b, of (𝟙_ A)))
            ((ofFunctor (V := V)).map g, 𝟙 (of (𝟙_ A))) ≫
            (ofFunctor (V := V)).map (ρ_ b).hom =
          (ofFunctor (V := V)).map (ρ_ a).hom ≫ (ofFunctor (V := V)).map g
        have hid : (𝟙 (of (𝟙_ A)) : (of (𝟙_ A) : EnrichedZeroCompletion V A) ⟶ of (𝟙_ A)) =
            (ofFunctor (V := V)).map (𝟙 (𝟙_ A)) := ((ofFunctor (V := V)).map_id _).symm
        rw [hid, tensorOrdinary_map_ofFunctor]
        apply mapped_composites
        simpa only [tensorHom_id] using MonoidalCategory.rightUnitor_naturality g
  · intro w x y z
    rcases quadruple_cases d w x y z with h | ⟨a, b, c, e, rfl, rfl, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h)).eq_of_src _ _
    · change (tensorOrdinary d).map
            (X := (of ((a ⊗ b) ⊗ c), of e)) (Y := (of (a ⊗ (b ⊗ c)), of e))
            ((ofFunctor (V := V)).map (α_ a b c).hom, 𝟙 (of e)) ≫
          (ofFunctor (V := V)).map (α_ a (b ⊗ c) e).hom ≫
          (tensorOrdinary d).map
            (X := (of a, of ((b ⊗ c) ⊗ e))) (Y := (of a, of (b ⊗ (c ⊗ e))))
            (𝟙 (of a), (ofFunctor (V := V)).map (α_ b c e).hom) =
        (ofFunctor (V := V)).map (α_ (a ⊗ b) c e).hom ≫
          (ofFunctor (V := V)).map (α_ a b (c ⊗ e)).hom
      have hidE : (𝟙 (of e) : (of e : EnrichedZeroCompletion V A) ⟶ of e) =
          (ofFunctor (V := V)).map (𝟙 e) := ((ofFunctor (V := V)).map_id e).symm
      have hidA : (𝟙 (of a) : (of a : EnrichedZeroCompletion V A) ⟶ of a) =
          (ofFunctor (V := V)).map (𝟙 a) := ((ofFunctor (V := V)).map_id a).symm
      rw [hidE, hidA, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
      let m₁ := (α_ a b c).hom ⊗ₘ 𝟙 e
      let m₂ := (α_ a (b ⊗ c) e).hom
      let m₃ := 𝟙 a ⊗ₘ (α_ b c e).hom
      let m₄ := (α_ (a ⊗ b) c e).hom
      let m₅ := (α_ a b (c ⊗ e)).hom
      have hSource : m₁ ≫ m₂ ≫ m₃ = m₄ ≫ m₅ := by
        simpa only [m₁, m₂, m₃, m₄, m₅, tensorHom_id, id_tensorHom] using
          MonoidalCategory.pentagon a b c e
      have hFirst : (ofFunctor (V := V)).map m₁ ≫ (ofFunctor (V := V)).map m₂ ≫
            (ofFunctor (V := V)).map m₃ =
          (ofFunctor (V := V)).map m₁ ≫ (ofFunctor (V := V)).map (m₂ ≫ m₃) :=
        congrArg (fun q : (of ((a ⊗ (b ⊗ c)) ⊗ e) : EnrichedZeroCompletion V A) ⟶
            of (a ⊗ (b ⊗ (c ⊗ e))) => (ofFunctor (V := V)).map m₁ ≫ q)
          ((ofFunctor (V := V)).map_comp m₂ m₃).symm
      exact hFirst.trans (mapped_composites m₁ (m₂ ≫ m₃) m₄ m₅ hSource)
  · intro x y
    rcases object_cases x with rfl | ⟨a, rfl⟩
    · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_src _ _
    · rcases object_cases y with rfl | ⟨b, rfl⟩
      · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_src _ _
      · change (ofFunctor (V := V)).map (α_ a (𝟙_ A) b).hom ≫
            (tensorOrdinary d).map (X := (of a, of ((𝟙_ A) ⊗ b))) (Y := (of a, of b))
              (𝟙 (of a), (ofFunctor (V := V)).map (λ_ b).hom) =
          (tensorOrdinary d).map (X := (of (a ⊗ (𝟙_ A)), of b)) (Y := (of a, of b))
            ((ofFunctor (V := V)).map (ρ_ a).hom, 𝟙 (of b))
        have hidA : (𝟙 (of a) : (of a : EnrichedZeroCompletion V A) ⟶ of a) =
            (ofFunctor (V := V)).map (𝟙 a) := ((ofFunctor (V := V)).map_id a).symm
        have hidB : (𝟙 (of b) : (of b : EnrichedZeroCompletion V A) ⟶ of b) =
            (ofFunctor (V := V)).map (𝟙 b) := ((ofFunctor (V := V)).map_id b).symm
        rw [hidA, hidB, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
        have hSource : (α_ a (𝟙_ A) b).hom ≫ (𝟙 a ⊗ₘ (λ_ b).hom) =
            (ρ_ a).hom ⊗ₘ 𝟙 b := by
          simpa only [tensorHom_id, id_tensorHom] using MonoidalCategory.triangle a b
        exact ((ofFunctor (V := V)).map_comp _ _).symm.trans
          (congrArg (fun k => (ofFunctor (V := V)).map k) hSource)


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [EnrichedOrdinaryCategory V A]

attribute [local instance] category enrichedOrdinaryCategory hasZeroObject
attribute [local instance] Enriched.prodCategory

omit [MonoidalCategory A] in
/-- Inclusion preserves the enriched point represented by an ordinary morphism. -/
theorem ofFunctor_eHom {a b : A} (f : a ⟶ b) :
    eHomEquiv (C := EnrichedZeroCompletion V A) V ((ofFunctor (V := V)).map f) =
      eHomEquiv (C := A) V f :=
  ofFunctor_map f

/-- Included associators have exactly the original enriched Hom points. -/
theorem associator_eHom_of (d : EnrichedMonoidalCategoryData V A) (a b c : A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    eHomEquiv (C := EnrichedZeroCompletion V A) V (α_ (of a) (of b) (of c)).hom =
      eHomEquiv (C := A) V (α_ a b c).hom := by
  let _ : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  exact ofFunctor_eHom (α_ a b c).hom

/-- Included left unit isomorphisms have exactly the original enriched Hom points. -/
theorem leftUnitor_eHom_of (d : EnrichedMonoidalCategoryData V A) (a : A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    eHomEquiv (C := EnrichedZeroCompletion V A) V (λ_ (of a)).hom =
      eHomEquiv (C := A) V (λ_ a).hom := by
  let _ : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  exact ofFunctor_eHom (λ_ a).hom

/-- Included right unit isomorphisms have exactly the original enriched Hom points. -/
theorem rightUnitor_eHom_of (d : EnrichedMonoidalCategoryData V A) (a : A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    eHomEquiv (C := EnrichedZeroCompletion V A) V (ρ_ (of a)).hom =
      eHomEquiv (C := A) V (ρ_ a).hom := by
  let _ : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  exact ofFunctor_eHom (ρ_ a).hom

/-- The tensor of three Hom objects is zero when the source triple tensor is added zero. -/
theorem tripleHom_isZero_left (d : EnrichedMonoidalCategoryData V A)
    (x y z x' y' z' : EnrichedZeroCompletion V A)
    (h : (tensorOrdinary d).obj ((tensorOrdinary d).obj (x, y), z) = zero) :
    IsZero (((x ⟶[V] x') ⊗ (y ⟶[V] y')) ⊗ (z ⟶[V] z')) := by
  cases x with
  | none => exact tensor_isZero_left (tensor_isZero_left (hom_zero_left_isZero x') _) _
  | some a =>
    cases y with
    | none => exact tensor_isZero_left (tensor_isZero_right _ (hom_zero_left_isZero y')) _
    | some b =>
      cases z with
      | none => exact tensor_isZero_right _ (hom_zero_left_isZero z')
      | some c =>
        change (some ((a ⊗ b) ⊗ c) : Option A) = none at h
        cases h

/-- The tensor of three Hom objects is zero when the target triple tensor is added zero. -/
theorem tripleHom_isZero_right (d : EnrichedMonoidalCategoryData V A)
    (x y z x' y' z' : EnrichedZeroCompletion V A)
    (h : (tensorOrdinary d).obj ((tensorOrdinary d).obj (x', y'), z') = zero) :
    IsZero (((x ⟶[V] x') ⊗ (y ⟶[V] y')) ⊗ (z ⟶[V] z')) := by
  cases x' with
  | none => exact tensor_isZero_left (tensor_isZero_left (hom_zero_right_isZero x) _) _
  | some a =>
    cases y' with
    | none => exact tensor_isZero_left (tensor_isZero_right _ (hom_zero_right_isZero y)) _
    | some b =>
      cases z' with
      | none => exact tensor_isZero_right _ (hom_zero_right_isZero z)
      | some c =>
        change (some ((a ⊗ b) ⊗ c) : Option A) = none at h
        cases h

/-- The completed monoidal tensor retains the tensor of included original objects literally. -/
theorem tensorObj_of (d : EnrichedMonoidalCategoryData V A) (a b : A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    (of a : EnrichedZeroCompletion V A) ⊗ of b = of (a ⊗ b) := rfl

/-- The completed monoidal unit is literally the included original unit. -/
theorem tensorUnit_of (d : EnrichedMonoidalCategoryData V A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    𝟙_ (EnrichedZeroCompletion V A) = of (𝟙_ A) := rfl

/-- Enriched monoidal data on the zero completion induced by the original data. -/
def enrichedMonoidalData (d : EnrichedMonoidalCategoryData V A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    EnrichedMonoidalCategoryData V (EnrichedZeroCompletion V A) := by
  letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  refine
    { tensorMap := fun x x' y y' => (tensorEnrichment d).map (x, y) (x', y')
      tensorMap_comp := ?_
      tensorMap_eHomEquiv := ?_
      associatorNaturality := ?_
      leftUnitorNaturality := ?_
      rightUnitorNaturality := ?_ }
  · intro x x' x'' y y' y''
    exact (tensorEnrichment d).map_comp (x, y) (x', y') (x'', y'')
  · intro x x' y y' f g
    change (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ (tensorEnrichment d).map (x, y) (x', y') =
      ((λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g)) ≫ (tensorEnrichment d).map (x, y) (x', y')
    exact (Category.assoc _ _ _).symm
  · intro x x' y y' z z'
    rcases triple_cases d x y z with hx | ⟨a, b, c, rfl, rfl, rfl⟩
    · exact (tensor_isZero_right (𝟙_ V)
        (tripleHom_isZero_left d x y z x' y' z' hx.1)).eq_of_src _ _
    · rcases triple_cases d x' y' z' with hy | ⟨a', b', c', rfl, rfl, rfl⟩
      · exact (tensor_isZero_right (𝟙_ V)
          (tripleHom_isZero_right d (of a) (of b) (of c) x' y' z' hy.1)).eq_of_src _ _
      · simp only [associator_eHom_of]
        simp only [tensorObj_of, tensorEnrichment_map_of]
        exact d.associatorNaturality a a' b b' c c'
  · intro x x'
    rcases object_cases x with rfl | ⟨a, rfl⟩
    · exact (tensor_isZero_right (𝟙_ V) (hom_zero_left_isZero x')).eq_of_src _ _
    · rcases object_cases x' with rfl | ⟨a', rfl⟩
      · exact (tensor_isZero_right (𝟙_ V) (hom_zero_right_isZero (of a))).eq_of_src _ _
      · simp only [leftUnitor_eHom_of]
        simp only [tensorUnit_of, tensorObj_of, tensorEnrichment_map_of]
        exact d.leftUnitorNaturality a a'
  · intro x x'
    rcases object_cases x with rfl | ⟨a, rfl⟩
    · exact (tensor_isZero_right (𝟙_ V) (hom_zero_left_isZero x')).eq_of_src _ _
    · rcases object_cases x' with rfl | ⟨a', rfl⟩
      · exact (tensor_isZero_right (𝟙_ V) (hom_zero_right_isZero (of a))).eq_of_src _ _
      · simp only [rightUnitor_eHom_of]
        simp only [tensorUnit_of, tensorObj_of, tensorEnrichment_map_of]
        exact d.rightUnitorNaturality a a'


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [BraidedCategory A]
  [EnrichedOrdinaryCategory V A]

attribute [local instance] category enrichedOrdinaryCategory hasZeroObject
attribute [local instance] Enriched.prodCategory

omit [BraidedCategory A] in
/-- A tensor of two completed objects is added zero or both factors are original objects. -/
theorem pair_cases (d : EnrichedMonoidalCategoryData V A)
    (x y : EnrichedZeroCompletion V A) :
    (tensorOrdinary d).obj (x, y) = zero ∨ ∃ a b, x = of a ∧ y = of b := by
  cases x with
  | none => exact Or.inl rfl
  | some a =>
    cases y with
    | none => exact Or.inl rfl
    | some b => exact Or.inr ⟨a, b, rfl, rfl⟩

omit [MonoidalCategory A] [BraidedCategory A] in
/-- Equal original triple composites have equal included triple composites. -/
theorem mapped_triples {X Y Z T Y' Z' : A}
    (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) (f₃ : Z ⟶ T)
    (g₁ : X ⟶ Y') (g₂ : Y' ⟶ Z') (g₃ : Z' ⟶ T)
    (h : f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ ≫ g₃) :
    (ofFunctor (V := V)).map f₁ ≫ (ofFunctor (V := V)).map f₂ ≫
        (ofFunctor (V := V)).map f₃ =
      (ofFunctor (V := V)).map g₁ ≫ (ofFunctor (V := V)).map g₂ ≫
        (ofFunctor (V := V)).map g₃ := by
  have hf :
      (ofFunctor (V := V)).map f₁ ≫ (ofFunctor (V := V)).map f₂ ≫
          (ofFunctor (V := V)).map f₃ =
        (ofFunctor (V := V)).map f₁ ≫ (ofFunctor (V := V)).map (f₂ ≫ f₃) :=
    congrArg (fun q : (of Y : EnrichedZeroCompletion V A) ⟶ of T =>
      (ofFunctor (V := V)).map f₁ ≫ q) ((ofFunctor (V := V)).map_comp f₂ f₃).symm
  have hg :
      (ofFunctor (V := V)).map g₁ ≫ (ofFunctor (V := V)).map g₂ ≫
          (ofFunctor (V := V)).map g₃ =
        (ofFunctor (V := V)).map g₁ ≫ (ofFunctor (V := V)).map (g₂ ≫ g₃) :=
    congrArg (fun q : (of Y' : EnrichedZeroCompletion V A) ⟶ of T =>
      (ofFunctor (V := V)).map g₁ ≫ q) ((ofFunctor (V := V)).map_comp g₂ g₃).symm
  exact hf.trans ((mapped_composites f₁ (f₂ ≫ f₃) g₁ (g₂ ≫ g₃) h).trans hg.symm)

/-- The original braiding on included objects, with identity on tensors containing added zero. -/
def completionBraiding (d : EnrichedMonoidalCategoryData V A) :
    ∀ x y : EnrichedZeroCompletion V A,
      (tensorOrdinary d).obj (x, y) ≅ (tensorOrdinary d).obj (y, x)
  | none, none => Iso.refl zero
  | none, some _ => Iso.refl zero
  | some _, none => Iso.refl zero
  | some a, some b => (ofFunctor (V := V)).mapIso (β_ a b)

/-- The braided category structure extending the original braiding to the zero completion. -/
@[instance_reducible]
def braidedCategory (d : EnrichedMonoidalCategoryData V A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    BraidedCategory (EnrichedZeroCompletion V A) := by
  letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  refine
    { braiding := completionBraiding d
      braiding_naturality_right := ?_
      braiding_naturality_left := ?_
      hexagon_forward := ?_
      hexagon_reverse := ?_ }
  · intro x y z f
    rcases pair_cases d x y with h | ⟨a, b, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h)).eq_of_src _ _
    · rcases object_cases z with rfl | ⟨c, rfl⟩
      · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_tgt _ _
      · rcases ofFunctor_map_surjective b c f with ⟨g, rfl⟩
        change (tensorOrdinary d).map (X := (of a, of b)) (Y := (of a, of c))
              (𝟙 (of a), (ofFunctor (V := V)).map g) ≫
            (ofFunctor (V := V)).map (β_ a c).hom =
          (ofFunctor (V := V)).map (β_ a b).hom ≫
            (tensorOrdinary d).map (X := (of b, of a)) (Y := (of c, of a))
              ((ofFunctor (V := V)).map g, 𝟙 (of a))
        have hid : (𝟙 (of a) : (of a : EnrichedZeroCompletion V A) ⟶ of a) =
            (ofFunctor (V := V)).map (𝟙 a) := ((ofFunctor (V := V)).map_id a).symm
        rw [hid, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
        apply mapped_composites
        simpa only [id_tensorHom, tensorHom_id] using
          BraidedCategory.braiding_naturality_right a g
  · intro x y f z
    rcases pair_cases d x z with h | ⟨a, c, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h)).eq_of_src _ _
    · rcases object_cases y with rfl | ⟨b, rfl⟩
      · exact (isZero_added_ordinary (V := V) (A := A)).eq_of_tgt _ _
      · rcases ofFunctor_map_surjective a b f with ⟨g, rfl⟩
        change (tensorOrdinary d).map (X := (of a, of c)) (Y := (of b, of c))
              ((ofFunctor (V := V)).map g, 𝟙 (of c)) ≫
            (ofFunctor (V := V)).map (β_ b c).hom =
          (ofFunctor (V := V)).map (β_ a c).hom ≫
            (tensorOrdinary d).map (X := (of c, of a)) (Y := (of c, of b))
              (𝟙 (of c), (ofFunctor (V := V)).map g)
        have hid : (𝟙 (of c) : (of c : EnrichedZeroCompletion V A) ⟶ of c) =
            (ofFunctor (V := V)).map (𝟙 c) := ((ofFunctor (V := V)).map_id c).symm
        rw [hid, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
        apply mapped_composites
        simpa only [id_tensorHom, tensorHom_id] using
          BraidedCategory.braiding_naturality_left g c
  · intro x y z
    rcases triple_cases d x y z with h | ⟨a, b, c, rfl, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h.1)).eq_of_src _ _
    · change (ofFunctor (V := V)).map (α_ a b c).hom ≫
            (ofFunctor (V := V)).map (β_ a (b ⊗ c)).hom ≫
            (ofFunctor (V := V)).map (α_ b c a).hom =
          (tensorOrdinary d).map (X := (of (a ⊗ b), of c)) (Y := (of (b ⊗ a), of c))
              ((ofFunctor (V := V)).map (β_ a b).hom, 𝟙 (of c)) ≫
            (ofFunctor (V := V)).map (α_ b a c).hom ≫
            (tensorOrdinary d).map (X := (of b, of (a ⊗ c))) (Y := (of b, of (c ⊗ a)))
              (𝟙 (of b), (ofFunctor (V := V)).map (β_ a c).hom)
      have hidC : (𝟙 (of c) : (of c : EnrichedZeroCompletion V A) ⟶ of c) =
          (ofFunctor (V := V)).map (𝟙 c) := ((ofFunctor (V := V)).map_id c).symm
      have hidB : (𝟙 (of b) : (of b : EnrichedZeroCompletion V A) ⟶ of b) =
          (ofFunctor (V := V)).map (𝟙 b) := ((ofFunctor (V := V)).map_id b).symm
      rw [hidC, hidB, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
      apply mapped_triples
      simpa only [id_tensorHom, tensorHom_id] using BraidedCategory.hexagon_forward a b c
  · intro x y z
    rcases triple_cases d x y z with h | ⟨a, b, c, rfl, rfl, rfl⟩
    · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h.2)).eq_of_src _ _
    · change (ofFunctor (V := V)).map (α_ a b c).inv ≫
            (ofFunctor (V := V)).map (β_ (a ⊗ b) c).hom ≫
            (ofFunctor (V := V)).map (α_ c a b).inv =
          (tensorOrdinary d).map (X := (of a, of (b ⊗ c))) (Y := (of a, of (c ⊗ b)))
              (𝟙 (of a), (ofFunctor (V := V)).map (β_ b c).hom) ≫
            (ofFunctor (V := V)).map (α_ a c b).inv ≫
            (tensorOrdinary d).map (X := (of (a ⊗ c), of b)) (Y := (of (c ⊗ a), of b))
              ((ofFunctor (V := V)).map (β_ a c).hom, 𝟙 (of b))
      have hidA : (𝟙 (of a) : (of a : EnrichedZeroCompletion V A) ⟶ of a) =
          (ofFunctor (V := V)).map (𝟙 a) := ((ofFunctor (V := V)).map_id a).symm
      have hidB : (𝟙 (of b) : (of b : EnrichedZeroCompletion V A) ⟶ of b) =
          (ofFunctor (V := V)).map (𝟙 b) := ((ofFunctor (V := V)).map_id b).symm
      rw [hidA, hidB, tensorOrdinary_map_ofFunctor, tensorOrdinary_map_ofFunctor]
      apply mapped_triples
      simpa only [id_tensorHom, tensorHom_id] using BraidedCategory.hexagon_reverse a b c

/-- The braiding of included original objects retains exactly its original enriched Hom point. -/
theorem braiding_eHom_of (d : EnrichedMonoidalCategoryData V A) (a b : A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    letI : BraidedCategory (EnrichedZeroCompletion V A) := braidedCategory d
    eHomEquiv (C := EnrichedZeroCompletion V A) V (β_ (of a) (of b)).hom =
      eHomEquiv (C := A) V (β_ a b).hom := by
  let _ : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  let _ : BraidedCategory (EnrichedZeroCompletion V A) := braidedCategory d
  exact ofFunctor_eHom (β_ a b).hom

/-- The extended braiding satisfies the enriched compatibility of the original braiding data. -/
theorem enrichedBraidedData (d : EnrichedMonoidalCategoryData V A)
    (b : EnrichedBraidedMonoidalCategoryData V A d) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    letI : BraidedCategory (EnrichedZeroCompletion V A) := braidedCategory d
    EnrichedBraidedMonoidalCategoryData V (EnrichedZeroCompletion V A)
      (enrichedMonoidalData d) := by
  let _ : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  let _ : BraidedCategory (EnrichedZeroCompletion V A) := braidedCategory d
  refine ⟨?_⟩
  intro x x' y y'
  rcases prodMerge_cases (x, y) with h | ⟨a, c, he⟩
  · exact (tensor_isZero_right (𝟙_ V)
      (prodHom_isZero_left (x, y) (x', y') h)).eq_of_src _ _
  · cases he
    rcases prodMerge_cases (x', y') with h | ⟨a', c', he'⟩
    · exact (tensor_isZero_right (𝟙_ V)
        (prodHom_isZero_right (of a, of c) (x', y') h)).eq_of_src _ _
    · cases he'
      simp only [braiding_eHom_of]
      simp only [enrichedMonoidalData, tensorObj_of, tensorEnrichment_map_of]
      exact b.braidingNaturality a a' c c'


end CategoryTheory.EnrichedZeroCompletion

namespace CategoryTheory.EnrichedZeroCompletion

open MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [HasZeroObject V]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [SymmetricCategory A]
  [EnrichedOrdinaryCategory V A]

attribute [local instance] category enrichedOrdinaryCategory hasZeroObject

/-- The symmetric category structure inherited from the original index on its zero completion. -/
@[instance_reducible]
def symmetricCategory (d : EnrichedMonoidalCategoryData V A) :
    letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
    SymmetricCategory (EnrichedZeroCompletion V A) := by
  letI : MonoidalCategory (EnrichedZeroCompletion V A) := monoidalCategory d
  refine
    { toBraidedCategory := braidedCategory d
      symmetry := ?_ }
  intro x y
  rcases pair_cases d x y with h | ⟨a, b, rfl, rfl⟩
  · exact ((isZero_added_ordinary (V := V) (A := A)).of_iso (eqToIso h)).eq_of_src _ _
  · change (ofFunctor (V := V)).map (β_ a b).hom ≫
        (ofFunctor (V := V)).map (β_ b a).hom = 𝟙 (of (a ⊗ b))
    exact ((ofFunctor (V := V)).map_comp _ _).symm.trans
      ((congrArg (fun f => (ofFunctor (V := V)).map f)
        (SymmetricCategory.symmetry a b)).trans ((ofFunctor (V := V)).map_id _))


end CategoryTheory.EnrichedZeroCompletion
