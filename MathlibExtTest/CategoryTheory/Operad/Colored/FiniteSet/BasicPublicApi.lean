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

import MathlibExt.CategoryTheory.Operad.Colored.FiniteSet.Basic

/-!
# Focused O7E colored set-operad basic public-contract packet

Pins the stable downstream-facing contracts for elementwise
colored set operads: the unit element, substitution inputs
with outer/inner projections, naturality in elementwise
form, relabeling functoriality, and full substitution.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v

variable {Color : Type u}

-- The unit element applies the unit to the empty element.
example (O : ColoredSetOperad Color) (c : Color) :
    ColoredSetOperad.unitElement O c =
      O.unit c ColoredSetOperad.emptyTensorElement :=
  rfl

-- Substitution inputs project to the outer operation.
example (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) →
      O.toCollection.obj (d.inner.obj i)) :
    ColoredSetOperad.substitutionInput O d outer inner
        none = outer :=
  ColoredSetOperad.substitutionInput_none O d outer inner

-- Substitution inputs project to inner operations.
example (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) →
      O.toCollection.obj (d.inner.obj i))
    (i : d.inner.index) :
    ColoredSetOperad.substitutionInput O d outer inner
        (some i) = inner i :=
  ColoredSetOperad.substitutionInput_some O d outer inner i

-- Elementwise naturality of substitution.
example (O : ColoredSetOperad Color)
    {X Y : ColoredSubstitutionData Color} (f : X ⟶ Y)
    (fam : (ColoredOperadObj.substitutionSource
      O.toCollection).obj X) :
    O.subst.app Y
          ((ColoredOperadObj.substitutionSource
            O.toCollection).map f fam) =
      O.toCollection.map
        (ColoredSubstitutionData.totalProfileMap f)
        (O.subst.app X fam) :=
  ColoredSetOperad.subst_naturality_apply O f fam

-- Elementwise functoriality of relabeling.
example (O : ColoredSymmetricCollection Color (Type v))
    {P Q R : ColoredProfile Color} (f : P ⟶ Q)
    (g : Q ⟶ R) (x : O.obj P) :
    O.map g (O.map f x) = O.map (f ≫ g) x :=
  ColoredSetOperad.map_comp_apply O f g x

-- Full substitution applies subst to the assembled input.
example (O : ColoredSetOperad Color)
    (d : ColoredSubstitutionData Color)
    (outer : O.toCollection.obj d.outerProfile)
    (inner : (i : d.inner.index) →
      O.toCollection.obj (d.inner.obj i)) :
    O.fullSubstitution d outer inner =
      O.subst.app d
        (ColoredSetOperad.substitutionInput O d outer
          inner) :=
  rfl
