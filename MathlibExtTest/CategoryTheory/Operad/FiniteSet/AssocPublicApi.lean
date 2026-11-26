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

import MathlibExt.CategoryTheory.Operad.FiniteSet.Assoc

/-!
# Focused O7E associative operad public-contract packet

Pins the stable downstream-facing contracts for the associative
finite-set operad: substitution naturality, the right-unit,
left-unit, and associativity laws, and the assembled operad
with its collection/unit/subst projections.
-/

open CategoryTheory
open CategoryTheory.Operad

-- Assoc substitution is natural.
example {X Y : SubstitutionData} (f : X ⟶ Y) :
    (substitutionSource
        SetOperad.AssocData.collection).map f ≫
        SetOperad.AssocData.substApp Y =
      SetOperad.AssocData.substApp X ≫
        (substitutionTarget
          SetOperad.AssocData.collection).map f :=
  SetOperad.AssocData.subst_naturality f

-- The assoc data satisfies the right-unit law.
example :
    IsRightUnit SetOperad.AssocData.collection
      SetOperad.AssocData.unitMor
      SetOperad.AssocData.subst :=
  SetOperad.AssocData.isRightUnit

-- The assoc data satisfies the left-unit law.
example :
    IsLeftUnit SetOperad.AssocData.collection
      SetOperad.AssocData.unitMor
      SetOperad.AssocData.subst :=
  SetOperad.AssocData.isLeftUnit

-- The assoc data satisfies associativity.
example :
    IsAssociative SetOperad.AssocData.collection
      SetOperad.AssocData.subst :=
  SetOperad.AssocData.isAssociative

-- The assoc operad projects to its collection.
example : SetOperad.assoc.toCollection =
    SetOperad.AssocData.collection :=
  rfl

-- The assoc operad projects to its unit.
example : SetOperad.assoc.unit =
    SetOperad.AssocData.unitMor :=
  rfl

-- The assoc operad projects to its substitution.
example : SetOperad.assoc.subst =
    SetOperad.AssocData.subst :=
  rfl

-- Assoc substitution applies the substitution app.
example (X : SubstitutionData) :
    SetOperad.AssocData.subst.app X =
      SetOperad.AssocData.substApp X :=
  rfl

-- The assoc collection evaluates to linear orders.
example (I : FintypeCat) :
    SetOperad.AssocData.collection.obj ⟨I⟩ =
      LinearOrder I :=
  rfl
