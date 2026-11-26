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

import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.ColorBlind

/-!
# Focused O7E finite-set color-blind public-contract packet

Pins the stable downstream-facing contracts for the
color-blind lift of set operads: collection evaluation and
relabeling by arity, unit elements, the source comparison
with outer/inner computations, substitution application,
and full substitution as ordinary substitution.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v

variable (Color : Type u)

-- Color-blind operations live at every profile of an arity.
example (O : SetOperad.{v}) (P : ColoredProfile Color) :
    (ColoredOperadObj.ColorBlind.obj Color O).toCollection.obj
        P = O.toCollection.eval P.inputs :=
  ColoredOperadObj.ColorBlind.obj_collection_obj Color O P

-- Color-blind relabeling forgets profile colors.
example (O : SetOperad.{v}) {P Q : ColoredProfile Color}
    (f : P ⟶ Q) :
    (ColoredOperadObj.ColorBlind.obj Color O).toCollection.map
        f =
      O.toCollection.map
        (FinBijGroupoid.homOfEquiv f.inputEquiv) :=
  ColoredOperadObj.ColorBlind.obj_collection_map Color O f

-- Color-blind units are the ordinary unit.
example (O : SetOperad.{v}) (c : Color) :
    ColoredSetOperad.unitElement
        (ColoredOperadObj.ColorBlind.obj Color O) c =
      SetOperad.unitElement O :=
  ColoredOperadObj.ColorBlind.obj_unitElement Color O c

-- The source comparison fixes the outer component.
example (O : SetOperad.{v})
    (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)).obj d) :
    ColoredOperadObj.ColorBlind.sourceToOrdinary Color O d x
        none = x none :=
  ColoredOperadObj.ColorBlind.sourceToOrdinary_none Color O
    d x

-- The source comparison fixes inner components.
example (O : SetOperad.{v})
    (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)).obj d)
    (i : d.inner.index) :
    ColoredOperadObj.ColorBlind.sourceToOrdinary Color O d x
        (some i) = x (some i) :=
  ColoredOperadObj.ColorBlind.sourceToOrdinary_some Color O
    d x i

-- Color-blind substitution is ordinary substitution.
example (O : SetOperad.{v})
    (d : ColoredSubstitutionData Color)
    (x : (ColoredOperadObj.substitutionSource
      (ColoredOperadObj.ColorBlind.collection Color
        O.toCollection)).obj d) :
    (ColoredOperadObj.ColorBlind.obj Color O).subst.app d
        x =
      O.subst.app d.toSubstitutionData
        (ColoredOperadObj.ColorBlind.sourceToOrdinary Color O
          d x) :=
  ColoredOperadObj.ColorBlind.obj_subst_app Color O d x

-- Full substitution forgets colors then substitutes.
example (O : SetOperad.{v})
    (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.eval d.inner.index)
    (inner : (i : d.inner.index) →
      O.toCollection.eval (d.inner.obj i).inputs) :
    ColoredSetOperad.fullSubstitution
          (ColoredOperadObj.ColorBlind.obj Color O) d
          outer inner =
      O.subst.app d.toSubstitutionData (fun o ↦ match o with
        | none => outer
        | some i => inner i) :=
  ColoredOperadObj.ColorBlind.obj_fullSubstitution_eq Color O
    d outer inner
