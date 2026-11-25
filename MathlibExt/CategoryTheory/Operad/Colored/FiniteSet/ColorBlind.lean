/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.ColorBlind
public import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.Basic
public import MathlibExt.CategoryTheory.Operad.FiniteSet.Elementwise

/-!
# Type-valued color-blind operads

Elementwise formulas for the color-blind lift of an ordinary set operad. These formulas expose
exactly the collection, relabeling, unit, and substitution behavior needed to define predicate
suboperads without unfolding the finite-family source comparison.
-/

@[expose] public section

namespace CategoryTheory.Operad.ColoredOperadObj.ColorBlind

open CategoryTheory

universe u v

variable (Color : Type u)

/-- A color-blind set operad has the original operations at every colored profile of the same
arity. -/
@[simp]
theorem obj_collection_obj (O : SetOperad.{v}) (P : ColoredProfile Color) :
    (obj Color O).toCollection.obj P = O.toCollection.eval P.inputs :=
  rfl

/-- Relabeling a color-blind operation forgets the colors of the profile isomorphism. -/
@[simp]
theorem obj_collection_map (O : SetOperad.{v}) {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (obj Color O).toCollection.map f =
      O.toCollection.map (FinBijGroupoid.homOfEquiv f.inputEquiv) :=
  rfl

/-- Every colored unit in the color-blind lift is the original ordinary unit. -/
@[simp]
theorem obj_unitElement (O : SetOperad.{v}) (c : Color) :
    ColoredSetOperad.unitElement (obj Color O) c = SetOperad.unitElement O :=
  rfl

/-- Send a colored substitution family to the corresponding ordinary family. -/
abbrev sourceToOrdinary (O : SetOperad.{v}) (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionSource (collection Color O.toCollection)).obj d →
      (Operad.substitutionSource O.toCollection).obj d.toSubstitutionData :=
  (sourceNatIso Color O.toCollection).hom.app d

/-- The outer component of the color-blind source comparison is unchanged. -/
@[simp]
theorem sourceToOrdinary_none (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource (collection Color O.toCollection)).obj d) :
    sourceToOrdinary Color O d x none = x none := by
  with_unfolding_all rfl

/-- Every inner component of the color-blind source comparison is unchanged. -/
@[simp]
theorem sourceToOrdinary_some (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource (collection Color O.toCollection)).obj d)
    (i : d.inner.index) :
    sourceToOrdinary Color O d x (some i) = x (some i) := by
  with_unfolding_all rfl

/-- Substitution in the color-blind lift is ordinary substitution on the same factor family. -/
@[simp]
theorem obj_subst_app (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource (collection Color O.toCollection)).obj d) :
    (obj Color O).subst.app d x =
      O.subst.app d.toSubstitutionData (sourceToOrdinary Color O d x) :=
  rfl

private theorem sourceNatIso_hom_substitutionInput
    (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.eval d.inner.index)
    (inner : (i : d.inner.index) → O.toCollection.eval (d.inner.obj i).inputs) :
    (sourceNatIso Color O.toCollection).hom.app d
        (ColoredSetOperad.substitutionInputOf
          (collection Color O.toCollection) d outer inner) =
      (fun o ↦ match o with
        | none => outer
        | some i => inner i) := by
  with_unfolding_all
    funext o
    cases o with
    | none => rfl
    | some i => rfl

/-- Full substitution in the underlying color-blind data is ordinary substitution after forgetting
colors. -/
@[simp]
theorem fullSubstitutionOf_eq (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.eval d.inner.index)
    (inner : (i : d.inner.index) → O.toCollection.eval (d.inner.obj i).inputs) :
    ColoredSetOperad.fullSubstitutionOf (collection Color O.toCollection)
        (substitutionData Color O.toCollection O.subst) d outer inner =
      O.subst.app d.toSubstitutionData (fun o ↦ match o with
        | none => outer
        | some i => inner i) := by
  unfold ColoredSetOperad.fullSubstitutionOf substitutionData
  change O.subst.app d.toSubstitutionData
      ((sourceNatIso Color O.toCollection).hom.app d
        (ColoredSetOperad.substitutionInputOf
          (collection Color O.toCollection) d outer inner)) = _
  rw [sourceNatIso_hom_substitutionInput]
  rfl

/-- Full substitution in a color-blind operad is ordinary substitution after forgetting colors. -/
@[simp]
theorem obj_fullSubstitution_eq (O : SetOperad.{v}) (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.eval d.inner.index)
    (inner : (i : d.inner.index) → O.toCollection.eval (d.inner.obj i).inputs) :
    ColoredSetOperad.fullSubstitution (obj Color O) d outer inner =
      O.subst.app d.toSubstitutionData (fun o ↦ match o with
        | none => outer
        | some i => inner i) := by
  change ColoredSetOperad.fullSubstitutionOf (collection Color O.toCollection)
    (substitutionData Color O.toCollection O.subst) d outer inner = _
  exact fullSubstitutionOf_eq Color O d outer inner

end CategoryTheory.Operad.ColoredOperadObj.ColorBlind
