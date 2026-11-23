/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Equivalence
public import MathlibExt.CategoryTheory.ExactCategory.Functor
public import MathlibExt.CategoryTheory.Waldhausen.ULift
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# The original exact structure under an object-only universe lift

The stock category on `ULift C` keeps every original Hom type and arrow.
The actual down functor pulls back the original exact structure as explicit
DATA; the original up/down equivalence is unchanged. Admissible and whole
short exact rows and their splittings retain the actual original maps.

The standard Waldhausen structure induced by this exact structure is compared
with the already proved original Waldhausen object lift. Explicit lifted
source zero points and the independently chosen target-zero Iso are retained.
No conflicting global structures or chosen-zero equality are installed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C]

local instance : (ULift.upFunctor : C ⥤ ULift.{v} C).IsEquivalence := by
  let e : C ≌ ULift.{v} C := ULift.equivalence
  change e.functor.IsEquivalence
  infer_instance

local instance : (ULift.downFunctor : ULift.{v} C ⥤ C).IsEquivalence := by
  let e : C ≌ ULift.{v} C := ULift.equivalence
  change e.inverse.IsEquivalence
  infer_instance

/-- Fully faithful DATA for the actual down functor with the SAME original
arrow as its preimage. -/
def uliftDownFullyFaithful :
    (ULift.downFunctor : ULift.{v} C ⥤ C).FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

variable [Preadditive C]

/-- The original additive Hom structure on the object-only lift, as explicit DATA. -/
@[instance_reducible]
def uliftPreadditive : Preadditive (ULift.{v} C) :=
  Preadditive.ofFullyFaithful (uliftDownFullyFaithful.{u, v} C)

/-- The actual unchanged-arrow down functor is additive. -/
theorem uliftDown_additive :
    letI := uliftPreadditive.{u, v} C
    (ULift.downFunctor : ULift.{v} C ⥤ C).Additive := by
  let _ := uliftPreadditive.{u, v} C
  exact (uliftDownFullyFaithful.{u, v} C).additive_ofFullyFaithful

/-- The actual object-only up functor is additive for the same original Hom DATA. -/
theorem uliftUp_additive :
    letI := uliftPreadditive.{u, v} C
    (ULift.upFunctor : C ⥤ ULift.{v} C).Additive := by
  let _ := uliftPreadditive.{u, v} C
  let e : ULift.{v} C ≌ C := ULift.equivalence.symm
  let _ : e.functor.Additive := uliftDown_additive.{u, v} C
  exact e.inverse_additive

variable [HasBinaryBiproducts C]

/-- The mapped original bilimit bicones supply binary biproduct DATA without
changing any original Hom world. -/
theorem uliftHasBinaryBiproducts :
    letI := uliftPreadditive.{u, v} C
    HasBinaryBiproducts (ULift.{v} C) := by
  let _ := uliftPreadditive.{u, v} C
  let _ := uliftUp_additive.{u, v} C
  let F : C ⥤ ULift.{v} C := ULift.upFunctor
  refine ⟨fun X Y => ?_⟩
  let _ : PreservesBinaryBiproduct X.down Y.down F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  change HasBinaryBiproduct (F.obj X.down) (F.obj Y.down)
  exact Functor.hasBinaryBiproduct_of_preserves F X.down Y.down

variable [HasZeroObject C]

local instance : Preadditive (ULift.{v} C) := uliftPreadditive.{u, v} C
local instance : HasZeroObject (ULift.{v} C) := Waldhausen.uliftHasZeroObject.{u, v} C
local instance : HasBinaryBiproducts (ULift.{v} C) := uliftHasBinaryBiproducts.{u, v} C
local instance : (ULift.downFunctor : ULift.{v} C ⥤ C).Additive := uliftDown_additive.{u, v} C
local instance : (ULift.upFunctor : C ⥤ ULift.{v} C).Additive := uliftUp_additive.{u, v} C

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- The entire original row returns through the literal up/down composite. -/
theorem uliftUp_down_mapShortComplex (S : ShortComplex C) :
    (S.map (ULift.upFunctor : C ⥤ ULift.{v} C)).map
        (ULift.downFunctor : ULift.{v} C ⥤ C) = S := rfl

/-- The actual stock counit compares every full down/up row with the
original lifted row, retaining its three original component maps. -/
def uliftDown_up_shortComplexIso (S : ShortComplex (ULift.{v} C)) :
    (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).map
        (ULift.upFunctor : C ⥤ ULift.{v} C) ≅ S := by
  let e : C ≌ ULift.{v} C := ULift.equivalence
  exact ShortComplex.isoMk (e.counitIso.app S.X₁) (e.counitIso.app S.X₂) (e.counitIso.app S.X₃)
    (e.counitIso.hom.naturality S.f).symm (e.counitIso.hom.naturality S.g).symm

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- Every whole short exact row is preserved and reflected by the actual down functor. -/
theorem ulift_shortExact_iff (S : ShortComplex (ULift.{v} C)) :
    S.ShortExact ↔ (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).ShortExact := by
  constructor
  · exact fun h => h.map_of_exact (ULift.downFunctor : ULift.{v} C ⥤ C)
  · intro h
    have ht := h.map_of_exact (ULift.upFunctor : C ⥤ ULift.{v} C)
    exact ShortComplex.shortExact_of_iso (uliftDown_up_shortComplexIso.{u, v} C S) ht

/-- Reconstruct a lifted splitting using the SAME original retraction and
section arrows; all three original splitting laws are retained. -/
def uliftSplittingOfDown (S : ShortComplex (ULift.{v} C))
    (s : (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting) : S.Splitting where
  r := s.r
  s := s.s
  f_r := s.f_r
  s_g := s.s_g
  id := s.id

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- The retraction is literally the original source retraction. -/
theorem uliftSplittingOfDown_r (S : ShortComplex (ULift.{v} C))
    (s : (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting) :
    (uliftSplittingOfDown.{u, v} C S s).r = s.r := rfl

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- The section is literally the original source section. -/
theorem uliftSplittingOfDown_s (S : ShortComplex (ULift.{v} C))
    (s : (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting) :
    (uliftSplittingOfDown.{u, v} C S s).s = s.s := rfl

omit [HasBinaryBiproducts C] [HasZeroObject C] in
/-- Full row splitting is preserved and reflected by the actual down program. -/
theorem ulift_splitting_iff (S : ShortComplex (ULift.{v} C)) :
    Nonempty S.Splitting ↔
      Nonempty (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)).Splitting := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.map (ULift.downFunctor : ULift.{v} C ⥤ C)⟩
  · rintro ⟨s⟩
    exact ⟨uliftSplittingOfDown.{u, v} C S s⟩

variable [ExactCategory C]

/-- Pull back the ORIGINAL exact structure through the actual down
equivalence, as explicit DATA with no split exact replacement. -/
@[instance_reducible]
def uliftExactCategory : ExactCategory (ULift.{v} C) := by
  let e : ULift.{v} C ≌ C := ULift.equivalence.symm
  letI : e.functor.Additive := uliftDown_additive.{u, v} C
  exact ExactCategory.ofEquivalence e

local instance : ExactCategory (ULift.{v} C) := uliftExactCategory.{u, v} C

/-- Every original admissible row is retained by the actual down map. -/
theorem ulift_isAdmissibleExact_iff (S : ShortComplex (ULift.{v} C)) :
    IsAdmissibleExact S ↔
      IsAdmissibleExact (S.map (ULift.downFunctor : ULift.{v} C ⥤ C)) := by
  let e : ULift.{v} C ≌ C := ULift.equivalence.symm
  let _ : e.functor.Additive := uliftDown_additive.{u, v} C
  exact ExactCategory.ofEquivalence_isAdmissibleExact_iff e S

/-- Admissible monomorphisms are the exact original class on the unchanged arrow. -/
theorem ulift_isAdmissibleMono_iff {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsAdmissibleMono f ↔ IsAdmissibleMono ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) := by
  let e : ULift.{v} C ≌ C := ULift.equivalence.symm
  let _ : e.functor.Additive := uliftDown_additive.{u, v} C
  exact ExactCategory.ofEquivalence_isAdmissibleMono_iff e f

/-- Admissible epimorphisms are the exact original class on the unchanged arrow. -/
theorem ulift_isAdmissibleEpi_iff {X Y : ULift.{v} C} (f : X ⟶ Y) :
    IsAdmissibleEpi f ↔ IsAdmissibleEpi ((ULift.downFunctor : ULift.{v} C ⥤ C).map f) := by
  let e : ULift.{v} C ≌ C := ULift.equivalence.symm
  let _ : e.functor.Additive := uliftDown_additive.{u, v} C
  exact ExactCategory.ofEquivalence_isAdmissibleEpi_iff e f

/-- The original up map preserves and reflects all original admissible rows. -/
theorem uliftUp_isAdmissibleExact_iff (S : ShortComplex C) :
    IsAdmissibleExact (S.map (ULift.upFunctor : C ⥤ ULift.{v} C)) ↔ IsAdmissibleExact S := by
  rw [ulift_isAdmissibleExact_iff, uliftUp_down_mapShortComplex]

/-- The original additive down map is Quillen exact. -/
theorem uliftDown_isExact : (ULift.downFunctor : ULift.{v} C ⥤ C).IsExact where
  map_admissibleExact S hS := (ulift_isAdmissibleExact_iff.{u, v} C S).mp hS

/-- The original additive object-only up map is Quillen exact. -/
theorem uliftUp_isExact : (ULift.upFunctor : C ⥤ ULift.{v} C).IsExact where
  map_admissibleExact S hS := (uliftUp_isAdmissibleExact_iff.{u, v} C S).mpr hS

/-- The full original structural splitting condition is preserved in both
directions, with every original admissible row retained. -/
theorem ulift_all_admissible_split_iff :
    (∀ S : ShortComplex (ULift.{v} C), IsAdmissibleExact S → Nonempty S.Splitting) ↔
      (∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) := by
  constructor
  · intro h S hS
    obtain ⟨s⟩ := h (S.map (ULift.upFunctor : C ⥤ ULift.{v} C))
      ((uliftUp_isAdmissibleExact_iff.{u, v} C S).mpr hS)
    have t := s.map (ULift.downFunctor : ULift.{v} C ⥤ C)
    exact ⟨t.ofIso (eqToIso (uliftUp_down_mapShortComplex.{u, v} C S))⟩
  · intro h S hS
    exact (ulift_splitting_iff.{u, v} C S).mpr
      (h _ ((ulift_isAdmissibleExact_iff.{u, v} C S).mp hS))

/-- The induced standard Waldhausen cofibration class is the same actual
inverse image of the original admissible monomorphism class. -/
theorem ulift_waldhausen_cofibrations :
    (ExactCategory.waldhausenCategory (ULift.{v} C)).cofibrations =
      ((ExactCategory.waldhausenCategory C).cofibrations).inverseImage
        (ULift.downFunctor : ULift.{v} C ⥤ C) := by
  funext X Y f
  exact propext (ulift_isAdmissibleMono_iff.{u, v} C f)

/-- The induced weak class is the same original isomorphism class pulled
back along the actual unchanged-arrow down functor. -/
theorem ulift_waldhausen_weakEquivalences :
    (ExactCategory.waldhausenCategory (ULift.{v} C)).weakEquivalences =
      ((ExactCategory.waldhausenCategory C).weakEquivalences).inverseImage
        (ULift.downFunctor : ULift.{v} C ⥤ C) := by
  funext X Y f
  apply propext
  change IsIso f ↔ IsIso ((ULift.downFunctor : ULift.{v} C ⥤ C).map f)
  exact (isIso_iff_of_reflects_iso f (ULift.downFunctor : ULift.{v} C ⥤ C)).symm

omit [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] in
private theorem waldhausen_eq_of_classes {D : Type u} [Category.{v} D] [HasZeroObject D]
    (A B : WaldhausenCategory D) (hc : A.cofibrations = B.cofibrations)
    (hw : A.weakEquivalences = B.weakEquivalences) : A = B := by
  cases A
  cases B
  cases hc
  cases hw
  rfl

/-- The induced standard Waldhausen structure equals the already proved
object-only pullback of the ORIGINAL standard exact structure. -/
theorem ulift_waldhausenCategory_eq :
    letI := ExactCategory.waldhausenCategory C
    ExactCategory.waldhausenCategory (ULift.{v} C) =
      Waldhausen.uliftWaldhausenCategory.{u, v} C := by
  let _ := ExactCategory.waldhausenCategory C
  have hc := ulift_waldhausen_cofibrations.{u, v} C
  have hw := ulift_waldhausen_weakEquivalences.{u, v} C
  let A := ExactCategory.waldhausenCategory (ULift.{v} C)
  let B := Waldhausen.uliftWaldhausenCategory.{u, v} C
  change A.cofibrations = B.cofibrations at hc
  change A.weakEquivalences = B.weakEquivalences at hw
  change A = B
  exact waldhausen_eq_of_classes A B hc hw

end CategoryTheory.ExactCategory
