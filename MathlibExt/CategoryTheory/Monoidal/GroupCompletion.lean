/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS
public import MathlibExt.CategoryTheory.Preadditive.Skeleton
public import MathlibExt.Algebra.Category.Grp.GrothendieckAddGroup
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Component invariants for the additive S⁻¹S construction

An object `(X₁,X₂)` of the additive `S⁻¹S` category has Grothendieck
difference `[X₁]-[X₂]`.  Every stabilized arrow preserves this difference,
giving a canonical functor to the discrete Grothendieck group of projective
isomorphism classes.

This is the forward component invariant.  This file does not yet identify
the fibers with connected components or assert the homological
group-completion theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject Algebra

universe v u

namespace CategoryTheory
namespace SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Grothendieck difference of the two coordinates of an `S⁻¹S` object. -/
noncomputable def Pair.difference (X : Pair C) :
    GrothendieckAddGroup (Skeleton C) :=
  GrothendieckAddGroup.of (toSkeleton X.fst) -
    GrothendieckAddGroup.of (toSkeleton X.snd)

/-- A raw stabilized arrow preserves the Grothendieck difference. -/
theorem RawHom.difference_eq {X Y : Pair C} (f : RawHom X Y) :
    X.difference = Y.difference := by
  have h₁ : toSkeleton f.stabilizer + toSkeleton X.fst =
      toSkeleton Y.fst := by
    rw [← Skeleton.toSkeleton_biprod]
    exact congr_toSkeleton_of_iso f.hom₁
  have h₂ : toSkeleton f.stabilizer + toSkeleton X.snd =
      toSkeleton Y.snd := by
    rw [← Skeleton.toSkeleton_biprod]
    exact congr_toSkeleton_of_iso f.hom₂
  have h₁' :
      GrothendieckAddGroup.of (toSkeleton f.stabilizer) +
          GrothendieckAddGroup.of (toSkeleton X.fst) =
        GrothendieckAddGroup.of (toSkeleton Y.fst) := by
    rw [← map_add, h₁]
  have h₂' :
      GrothendieckAddGroup.of (toSkeleton f.stabilizer) +
          GrothendieckAddGroup.of (toSkeleton X.snd) =
        GrothendieckAddGroup.of (toSkeleton Y.snd) := by
    rw [← map_add, h₂]
  unfold Pair.difference
  rw [← h₁', ← h₂']
  abel

/-- A quotient stabilized arrow preserves the Grothendieck difference. -/
theorem Hom.difference_eq {X Y : Pair C} (f : X ⟶ Y) :
    X.difference = Y.difference := by
  exact Quotient.inductionOn f (fun g => RawHom.difference_eq g)

/-- The canonical functor from additive `S⁻¹S` to the discrete
Grothendieck group of isomorphism classes. -/
noncomputable def differenceFunctor :
    Pair C ⥤ Discrete (GrothendieckAddGroup (Skeleton C)) where
  obj X := Discrete.mk X.difference
  map f := Discrete.eqToHom' (Hom.difference_eq f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem differenceFunctor_obj_as
    (X : Pair C) :
    (differenceFunctor.obj X).as = X.difference :=
  rfl

theorem difference_corePairInclusion_obj_as (X : Core C × Core C) :
    (differenceFunctor.obj (corePairInclusion.obj X)).as =
      GrothendieckAddGroup.of (toSkeleton X.1.of) -
        GrothendieckAddGroup.of (toSkeleton X.2.of) :=
  rfl

theorem difference_coreInclusion_obj_as (X : Core C) :
    (differenceFunctor.obj (coreInclusion.obj X)).as =
      GrothendieckAddGroup.of (toSkeleton X.of) := by
  simp [differenceFunctor, Pair.difference, coreInclusion, coreZeroPair,
    corePairInclusion, Pair.ofCorePair, Skeleton.toSkeleton_zero]

/-- The difference of the original core pair, in the generic functor's simp normal form. -/
@[simp]
theorem ofCorePair_difference (X : Core C × Core C) :
    (Pair.ofCorePair X).difference =
      GrothendieckAddGroup.of (toSkeleton X.1.of) -
        GrothendieckAddGroup.of (toSkeleton X.2.of) := rfl

/-- The original core inclusion has its canonical single-generator difference. -/
@[simp]
theorem coreInclusion_difference (X : Core C) :
    (coreInclusion.obj X).difference = GrothendieckAddGroup.of (toSkeleton X.of) := by
  simpa only [differenceFunctor_obj_as] using difference_coreInclusion_obj_as (C := C) X

/-- Every element of a Grothendieck group is a difference of two canonical
generators. -/
theorem grothendieck_exists_eq_difference
    (x : GrothendieckAddGroup (Skeleton C)) :
    ∃ a b : Skeleton C,
      x = GrothendieckAddGroup.of a - GrothendieckAddGroup.of b := by
  induction x using AddLocalization.induction_on with
  | _ p =>
      refine ⟨p.1, p.2.1, ?_⟩
      symm
      change
        (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Skeleton C))) p.1 -
            (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Skeleton C))) p.2.1 =
          AddLocalization.mk p.1 p.2
      rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk p.1,
        ← AddLocalization.mk_zero_eq_addMonoidOf_mk p.2.1,
        GrothendieckAddGroup.mk_sub_mk]
      simp

/-- Equality of canonical generators in a Grothendieck group is equality
after adding one common monoid element. -/
theorem grothendieck_of_eq_iff_exists_add_eq (a b : Skeleton C) :
    GrothendieckAddGroup.of a = GrothendieckAddGroup.of b ↔
      ∃ c : Skeleton C, a + c = b + c := by
  change
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Skeleton C))) a =
        (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (Skeleton C))) b ↔ _
  rw [← AddLocalization.mk_zero_eq_addMonoidOf_mk a,
    ← AddLocalization.mk_zero_eq_addMonoidOf_mk b,
    AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, by simpa [add_comm] using h⟩
  · rintro ⟨c, h⟩
    exact ⟨⟨c, AddSubmonoid.mem_top c⟩, by simpa [add_comm] using h⟩

/-- Equal differences admit a common stabilizing skeleton class after
crossing the two coordinates. -/
theorem Pair.exists_stable_cross_of_difference_eq {X Y : Pair C}
    (h : X.difference = Y.difference) :
    ∃ t : Skeleton C,
      (toSkeleton X.fst + toSkeleton Y.snd) + t =
        (toSkeleton Y.fst + toSkeleton X.snd) + t := by
  have hDiff := h
  change
    GrothendieckAddGroup.of (toSkeleton X.fst) -
        GrothendieckAddGroup.of (toSkeleton X.snd) =
      GrothendieckAddGroup.of (toSkeleton Y.fst) -
        GrothendieckAddGroup.of (toSkeleton Y.snd) at hDiff
  have hCross :
      GrothendieckAddGroup.of (toSkeleton X.fst) +
          GrothendieckAddGroup.of (toSkeleton Y.snd) =
        GrothendieckAddGroup.of (toSkeleton Y.fst) +
          GrothendieckAddGroup.of (toSkeleton X.snd) := by
    calc
      GrothendieckAddGroup.of (toSkeleton X.fst) +
          GrothendieckAddGroup.of (toSkeleton Y.snd) =
        (GrothendieckAddGroup.of (toSkeleton X.fst) -
            GrothendieckAddGroup.of (toSkeleton X.snd)) +
          GrothendieckAddGroup.of (toSkeleton X.snd) +
          GrothendieckAddGroup.of (toSkeleton Y.snd) := by abel
      _ = (GrothendieckAddGroup.of (toSkeleton Y.fst) -
            GrothendieckAddGroup.of (toSkeleton Y.snd)) +
          GrothendieckAddGroup.of (toSkeleton X.snd) +
          GrothendieckAddGroup.of (toSkeleton Y.snd) := by
        rw [hDiff]
      _ = GrothendieckAddGroup.of (toSkeleton Y.fst) +
          GrothendieckAddGroup.of (toSkeleton X.snd) := by abel
  have hOf :
      GrothendieckAddGroup.of
          (toSkeleton X.fst + toSkeleton Y.snd) =
        GrothendieckAddGroup.of
          (toSkeleton Y.fst + toSkeleton X.snd) := by
    simpa only [map_add] using hCross
  exact (grothendieck_of_eq_iff_exists_add_eq _ _).1 hOf

/-- Reassociate a triple biproduct while swapping its last two summands. -/
noncomputable def biprodSwapLastIso (A T B : C) :
    (A ⊞ T) ⊞ B ≅ (A ⊞ B) ⊞ T :=
  (biprod.associator A T B).trans
    ((biprod.mapIso (Iso.refl A) (biprod.braiding T B)).trans
      (biprod.associator A B T).symm)

/-- Move the last summand to the front while retaining the middle summand. -/
noncomputable def biprodRotateIso (A T B : C) :
    (A ⊞ T) ⊞ B ≅ (B ⊞ T) ⊞ A :=
  (biprod.braiding (A ⊞ T) B).trans
    ((biprod.mapIso (Iso.refl B) (biprod.braiding A T)).trans
      (biprod.associator B T A).symm)

/-- Objects with equal Grothendieck difference admit a common target in
additive `S⁻¹S`. -/
theorem Pair.exists_cospan_of_difference_eq {X Y : Pair C}
    (h : X.difference = Y.difference) :
    ∃ Z : Pair C, Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := by
  obtain ⟨t, ht⟩ := X.exists_stable_cross_of_difference_eq h
  let T : C := (fromSkeleton C).obj t
  have hStable :
      toSkeleton ((X.fst ⊞ Y.snd) ⊞ T) =
        toSkeleton ((Y.fst ⊞ X.snd) ⊞ T) := by
    rw [Skeleton.toSkeleton_biprod, Skeleton.toSkeleton_biprod,
      Skeleton.toSkeleton_biprod, Skeleton.toSkeleton_biprod,
      toSkeleton_fromSkeleton_obj]
    exact ht
  let e : (X.fst ⊞ Y.snd) ⊞ T ≅
      (Y.fst ⊞ X.snd) ⊞ T :=
    Skeleton.isoOfEq hStable
  let Z : Pair C :=
    ⟨(Y.fst ⊞ T) ⊞ X.fst, (Y.fst ⊞ T) ⊞ X.snd⟩
  let fX : RawHom X Z :=
    { stabilizer := Y.fst ⊞ T
      hom₁ := Iso.refl _
      hom₂ := Iso.refl _ }
  let fY : RawHom Y Z :=
    { stabilizer := X.fst ⊞ T
      hom₁ := biprodRotateIso X.fst T Y.fst
      hom₂ := (biprodSwapLastIso X.fst T Y.snd).trans
        (e.trans (biprodSwapLastIso Y.fst T X.snd).symm) }
  exact ⟨Z, ⟨Hom.mk fX⟩, ⟨Hom.mk fY⟩⟩

/-- Equal Grothendieck differences give a zigzag in additive `S⁻¹S`. -/
theorem Pair.zigzag_of_difference_eq {X Y : Pair C}
    (h : X.difference = Y.difference) : Zigzag X Y := by
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ := X.exists_cospan_of_difference_eq h
  exact Zigzag.of_hom_inv f g

/-- A zigzag in additive `S⁻¹S` forces equality of Grothendieck
differences. -/
theorem Pair.difference_eq_of_zigzag {X Y : Pair C}
    (h : Zigzag X Y) : X.difference = Y.difference := by
  have h' := zigzag_obj_of_zigzag differenceFunctor h
  exact CategoryTheory.eq_of_zigzag _ h'

/-- Grothendieck difference exactly classifies the categorical connected
components of additive `S⁻¹S`. -/
theorem Pair.zigzag_iff_difference_eq {X Y : Pair C} :
    Zigzag X Y ↔ X.difference = Y.difference :=
  ⟨Pair.difference_eq_of_zigzag, Pair.zigzag_of_difference_eq⟩

/-- Grothendieck difference on categorical connected components. -/
noncomputable def connectedComponentsToGrothendieck :
    ConnectedComponents (Pair C) → GrothendieckAddGroup (Skeleton C) :=
  Quotient.lift Pair.difference
    (fun _ _ h => Pair.difference_eq_of_zigzag h)

@[simp]
theorem connectedComponentsToGrothendieck_mk (X : Pair C) :
    connectedComponentsToGrothendieck (ConnectedComponents.mk X) =
      X.difference :=
  rfl

theorem connectedComponentsToGrothendieck_injective :
    Function.Injective
      (connectedComponentsToGrothendieck (C := C)) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ X =>
      induction y using Quotient.inductionOn with
      | _ Y =>
          apply Quotient.sound
          exact Pair.zigzag_of_difference_eq h

theorem connectedComponentsToGrothendieck_surjective :
    Function.Surjective
      (connectedComponentsToGrothendieck (C := C)) := by
  intro x
  obtain ⟨a, b, hab⟩ := grothendieck_exists_eq_difference (C := C) x
  let X : Pair C :=
    ⟨(fromSkeleton C).obj a, (fromSkeleton C).obj b⟩
  refine ⟨ConnectedComponents.mk X, ?_⟩
  change X.difference = x
  simpa [X, Pair.difference, toSkeleton_fromSkeleton_obj] using hab.symm

/-- The connected components of additive `S⁻¹S` are canonically the
Grothendieck group of isomorphism classes. -/
noncomputable def connectedComponentsEquivGrothendieck :
    ConnectedComponents (Pair C) ≃
      GrothendieckAddGroup (Skeleton C) :=
  Equiv.ofBijective connectedComponentsToGrothendieck
    ⟨connectedComponentsToGrothendieck_injective,
      connectedComponentsToGrothendieck_surjective⟩

/-! ## The identity component -/

/-- Objects in the identity component are those with zero Grothendieck
difference. -/
abbrev zeroComponentProperty : ObjectProperty (Pair C) :=
  fun X => X.difference = 0

/-- The full categorical identity component of additive `S⁻¹S`. -/
abbrev ZeroComponent :=
  (zeroComponentProperty (C := C)).FullSubcategory

/-- The selected zero object in the categorical identity component. -/
noncomputable def zeroComponentBaseObject : ZeroComponent (C := C) :=
  ⟨⟨0, 0⟩, by
    simp [zeroComponentProperty, Pair.difference,
      Skeleton.toSkeleton_zero]⟩

noncomputable instance zeroComponent_nonempty :
    Nonempty (ZeroComponent (C := C)) :=
  ⟨zeroComponentBaseObject (C := C)⟩

noncomputable instance zeroComponent_isConnected :
    IsConnected (ZeroComponent (C := C)) := by
  apply zigzag_isConnected
  intro X Y
  have hXY : X.obj.difference = Y.obj.difference :=
    X.property.trans Y.property.symm
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ :=
    X.obj.exists_cospan_of_difference_eq hXY
  have hZ : Z.difference = 0 :=
    (Hom.difference_eq f).symm.trans X.property
  let Z' : ZeroComponent (C := C) := ⟨Z, hZ⟩
  let f' : X ⟶ Z' := ObjectProperty.homMk f
  let g' : Y ⟶ Z' := ObjectProperty.homMk g
  exact Zigzag.of_hom_inv f' g'

/-- Every Grothendieck difference is represented by an object of additive
`S⁻¹S`. -/
noncomputable instance differenceFunctor_essSurj :
    (differenceFunctor (C := C)).EssSurj where
  mem_essImage Y := by
    obtain ⟨a, b, hab⟩ := grothendieck_exists_eq_difference (C := C) Y.as
    let X : Pair C :=
      ⟨(fromSkeleton C).obj a, (fromSkeleton C).obj b⟩
    refine ⟨X, ⟨eqToIso ?_⟩⟩
    apply Discrete.ext
    change X.difference = Y.as
    simpa [X, Pair.difference, toSkeleton_fromSkeleton_obj] using hab.symm

end SInverseS
end CategoryTheory
