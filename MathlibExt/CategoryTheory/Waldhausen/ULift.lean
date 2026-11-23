/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.Gluing
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Waldhausen transport through an object-only universe lift

The stock `uliftCategory` on `ULift C` keeps every original Hom type.
Cofibrations and weak equivalences are the inverse images of the original
classes along the actual `ULift.downFunctor`; existing pushout squares and
the full gluing axiom are transported through the stock equivalence.

The explicit lifted source zero is `ULift.up (0 : C)`. Its up/down readers
are strict. The independently chosen `HasZeroObject` zero is retained
through its actual comparison isomorphism, without an object equality premise.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C]

local instance : (ULift.upFunctor : C ⥤ ULift.{v} C).IsEquivalence := by
  let e : C ≌ ULift.{v} C := ULift.equivalence
  change e.functor.IsEquivalence
  infer_instance

local instance : (ULift.downFunctor : ULift.{v} C ⥤ C).IsEquivalence := by
  let e : C ≌ ULift.{v} C := ULift.equivalence
  change e.inverse.IsEquivalence
  infer_instance

/-- The object-only lift preserves and reflects zero objects through the
same original unique Hom witnesses. -/
theorem ulift_isZero_iff (X : ULift.{v} C) : IsZero X ↔ IsZero X.down := by
  constructor
  · intro h
    exact {
      unique_to := fun Y => h.unique_to (ULift.up Y)
      unique_from := fun Y => h.unique_from (ULift.up Y) }
  · intro h
    exact {
      unique_to := fun Y => h.unique_to Y.down
      unique_from := fun Y => h.unique_from Y.down }

/-- Every original pushout is preserved and reflected by the actual
object-only down functor, with every original arrow unchanged. -/
theorem ulift_isPushout_iff {X Y Z P : ULift.{v} C}
    (f : X ⟶ Y) (i : X ⟶ Z) (l : Y ⟶ P) (r : Z ⟶ P) :
    IsPushout f i l r ↔ IsPushout
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map f)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map i)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map l)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map r) :=
  ⟨fun h => Functor.map_isPushout (ULift.downFunctor : ULift.{v} C ⥤ C) h,
    fun h => h.of_map_of_faithful (ULift.downFunctor : ULift.{v} C ⥤ C)⟩

variable [HasZeroObject C]

/-- The explicit original source zero in the object-only lift. -/
def uliftZeroObject : ULift.{v} C := ULift.up (0 : C)

/-- The literal lifted original zero is genuinely zero. -/
theorem uliftZeroObject_isZero : IsZero (uliftZeroObject.{u, v} C) :=
  (ulift_isZero_iff.{u, v} C (uliftZeroObject.{u, v} C)).mpr (isZero_zero C)

/-- The original up functor sends the original chosen zero to this exact point. -/
theorem uliftZeroObject_up :
    (ULift.upFunctor : C ⥤ ULift.{v} C).obj (0 : C) = uliftZeroObject.{u, v} C := rfl

/-- The original down functor returns that same chosen source zero exactly. -/
theorem uliftZeroObject_down :
    (ULift.downFunctor : ULift.{v} C ⥤ C).obj (uliftZeroObject.{u, v} C) = (0 : C) := rfl

/-- Zero existence on the object lift, from the explicit original zero witness. -/
theorem uliftHasZeroObject : HasZeroObject (ULift.{v} C) :=
  (uliftZeroObject_isZero.{u, v} C).hasZeroObject

local instance : HasZeroObject (ULift.{v} C) := uliftHasZeroObject.{u, v} C

/-- The genuine comparison with the target's independently chosen zero. -/
def uliftZeroObjectIsoZero : uliftZeroObject.{u, v} C ≅ (0 : ULift.{v} C) :=
  (uliftZeroObject_isZero.{u, v} C).isoZero

/-- Lowering the independently chosen target zero gives a genuinely zero
original object; no equality with the original chosen zero is asserted. -/
theorem uliftChosenZero_down_isZero :
    IsZero ((ULift.downFunctor : ULift.{v} C ⥤ C).obj (0 : ULift.{v} C)) :=
  (ulift_isZero_iff.{u, v} C (0 : ULift.{v} C)).mp (isZero_zero (ULift.{v} C))

/-- The actual source-category zero isomorphism attached to the down program. -/
def uliftChosenZeroDownIso :
    (ULift.downFunctor : ULift.{v} C ⥤ C).obj (0 : ULift.{v} C) ≅ (0 : C) :=
  (uliftChosenZero_down_isZero.{u, v} C).isoZero


/-- The comparison with the independently chosen target zero retains
the original unique arrow out of the original chosen source zero. -/
theorem uliftZeroObjectIsoZero_hom :
    (uliftZeroObjectIsoZero.{u, v} C).hom =
      (isZero_zero C).to_ ((0 : ULift.{v} C).down) :=
  (isZero_zero C).eq_of_src _ _

/-- Its inverse retains the original unique arrow into that same source zero. -/
theorem uliftZeroObjectIsoZero_inv :
    (uliftZeroObjectIsoZero.{u, v} C).inv =
      (isZero_zero C).from_ ((0 : ULift.{v} C).down) :=
  (isZero_zero C).eq_of_tgt _ _

/-- The down-program zero comparison is the original source-category arrow. -/
theorem uliftChosenZeroDownIso_hom :
    (uliftChosenZeroDownIso.{u, v} C).hom =
      (isZero_zero C).from_ ((0 : ULift.{v} C).down) :=
  (isZero_zero C).eq_of_tgt _ _

/-- Its inverse is the original unique map from the original chosen zero. -/
theorem uliftChosenZeroDownIso_inv :
    (uliftChosenZeroDownIso.{u, v} C).inv =
      (isZero_zero C).to_ ((0 : ULift.{v} C).down) :=
  (isZero_zero C).eq_of_src _ _


variable [WaldhausenCategory C]

/-- The pulled-back original Waldhausen structure on the object-only lift.
Every Hom remains in the original Hom universe. -/
@[instance_reducible]
def uliftWaldhausenCategory : WaldhausenCategory (ULift.{v} C) where
  cofibrations := (WaldhausenCategory.cofibrations (C := C)).inverseImage
    (ULift.downFunctor : ULift.{v} C ⥤ C)
  weakEquivalences := (WaldhausenCategory.weakEquivalences (C := C)).inverseImage
    (ULift.downFunctor : ULift.{v} C ⥤ C)
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration X f := by
    change WaldhausenCategory.cofibrations (C := C)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map f)
    let e := uliftChosenZeroDownIso.{u, v} C
    have h : WaldhausenCategory.cofibrations (C := C)
        (e.inv ≫ (ULift.downFunctor : ULift.{v} C ⥤ C).map f) :=
      WaldhausenCategory.zero_isCofibration X.down _
    have he : WaldhausenCategory.cofibrations (C := C) e.hom :=
      (WaldhausenCategory.cofibrations (C := C)).of_isIso e.hom
    have hc := (WaldhausenCategory.cofibrations (C := C)).comp_mem _ _ he h
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hc
  cofibration_pushout i hi X' f := by
    change WaldhausenCategory.cofibrations (C := C)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map i) at hi
    obtain ⟨P, l, r, hp, hl⟩ := WaldhausenCategory.cofibration_pushout
      (C := C) ((ULift.downFunctor : ULift.{v} C ⥤ C).map i) hi X'.down
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map f)
    refine ⟨ULift.up P, l, r, ?_, ?_⟩
    · exact hp.of_map_of_faithful (ULift.downFunctor : ULift.{v} C ⥤ C)
    · exact hl

local instance : WaldhausenCategory (ULift.{v} C) := uliftWaldhausenCategory.{u, v} C

/-- Cofibrations are exactly the original cofibrations on the unchanged arrow. -/
theorem ulift_isCofibration_iff {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsCofibration f ↔ IsCofibration ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) := Iff.rfl

/-- Weak equivalences are exactly the original weak equivalences on that arrow. -/
theorem ulift_isWeakEquivalence_iff {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsWeakEquivalence f ↔ IsWeakEquivalence ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) := Iff.rfl


/-- The original up arrow preserves and reflects the exact source cofibration class. -/
theorem uliftUp_isCofibration_iff {X Y : C} (f : X ⟶ Y) :
    IsCofibration ((ULift.upFunctor : C ⥤ ULift.{v} C).map f) ↔ IsCofibration f := Iff.rfl

/-- The original up arrow preserves and reflects the exact source weak class. -/
theorem uliftUp_isWeakEquivalence_iff {X Y : C} (f : X ⟶ Y) :
    IsWeakEquivalence ((ULift.upFunctor : C ⥤ ULift.{v} C).map f) ↔ IsWeakEquivalence f := Iff.rfl


/-- The actual original down functor is Waldhausen exact. -/
theorem uliftDown_isWaldhausenExact :
    (ULift.downFunctor : ULift.{v} C ⥤ C).IsWaldhausenExact where
  map_isZero h := (ulift_isZero_iff.{u, v} C _).mp h
  map_cofibration _ h := h
  map_weakEquivalence _ h := h
  map_pushout _ _ _ _ _ h := Functor.map_isPushout (ULift.downFunctor : ULift.{v} C ⥤ C) h

/-- The actual original up functor is Waldhausen exact. -/
theorem uliftUp_isWaldhausenExact :
    (ULift.upFunctor : C ⥤ ULift.{v} C).IsWaldhausenExact where
  map_isZero h := (ulift_isZero_iff.{u, v} C _).mpr h
  map_cofibration _ h := h
  map_weakEquivalence _ h := h
  map_pushout _ _ _ _ _ h := Functor.map_isPushout (ULift.upFunctor : C ⥤ ULift.{v} C) h

/-- Both maps of the existing stock equivalence are exact for the original
and pulled-back structures; no new equivalence provider is introduced. -/
theorem uliftEquivalence_isWaldhausenExact :
    (show C ≌ ULift.{v} C from ULift.equivalence).functor.IsWaldhausenExact ∧
      (show C ≌ ULift.{v} C from ULift.equivalence).inverse.IsWaldhausenExact :=
  ⟨uliftUp_isWaldhausenExact.{u, v} C, uliftDown_isWaldhausenExact.{u, v} C⟩

/-- The original full gluing axiom gives the gluing axiom on the literal
object-only lift, using the same original spans and weak arrows. -/
theorem uliftGluing (hG : WaldhausenGluingAxiom (C := C)) :
    WaldhausenGluingAxiom (C := ULift.{v} C) where
  gluing hP hP' x y z p hi hi' h₁ h₂ h₃ h₄ hx hy hz :=
    hG.gluing
      (Functor.map_isPushout (ULift.downFunctor : ULift.{v} C ⥤ C) hP)
      (Functor.map_isPushout (ULift.downFunctor : ULift.{v} C ⥤ C) hP')
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map x)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map y)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map z)
      ((ULift.downFunctor : ULift.{v} C ⥤ C).map p)
      hi hi' h₁ h₂ h₃ h₄ hx hy hz

/-- Gluing is reflected by the object-only lift as well as preserved. -/
theorem uliftGluing_iff :
    WaldhausenGluingAxiom (C := ULift.{v} C) ↔ WaldhausenGluingAxiom (C := C) := by
  refine ⟨?_, uliftGluing.{u, v} C⟩
  intro hG
  refine ⟨?_⟩
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' h₁ h₂ h₃ h₄ hx hy hz
  exact hG.gluing
    (Functor.map_isPushout (ULift.upFunctor : C ⥤ ULift.{v} C) hP)
    (Functor.map_isPushout (ULift.upFunctor : C ⥤ ULift.{v} C) hP')
    ((ULift.upFunctor : C ⥤ ULift.{v} C).map x)
    ((ULift.upFunctor : C ⥤ ULift.{v} C).map y)
    ((ULift.upFunctor : C ⥤ ULift.{v} C).map z)
    ((ULift.upFunctor : C ⥤ ULift.{v} C).map p)
    hi hi' h₁ h₂ h₃ h₄ hx hy hz

end CategoryTheory.Waldhausen
