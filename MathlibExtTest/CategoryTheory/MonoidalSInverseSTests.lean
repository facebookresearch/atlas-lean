/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseS
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-! # Tests for faithful biproduct translations -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.SInverseSTests

variable {R : Type u} [Ring R]

example (P Q : FGProjectiveCat.{u} R) :
    Aut P →* Aut (P ⊞ Q) :=
  SInverseS.biprodRightAutHom P Q

example (P Q : FGProjectiveCat.{u} R) :
    Function.Injective (SInverseS.biprodRightAutHom P Q) :=
  SInverseS.biprodRightAutHom_injective P Q

example (P Q : FGProjectiveCat.{u} R) :
    Function.Injective (SInverseS.biprodLeftAutHom P Q) :=
  SInverseS.biprodLeftAutHom_injective P Q

example (X Y : SInverseS.Pair (FGProjectiveCat.{u} R)) : Type (u + 1) :=
  SInverseS.RawHom X Y

example (X Y : SInverseS.Pair (FGProjectiveCat.{u} R)) : Type (u + 1) :=
  SInverseS.Hom X Y

example {X Y Z : SInverseS.Pair (FGProjectiveCat.{u} R)}
    (f : SInverseS.RawHom X Y) (g : SInverseS.RawHom Y Z) :
    SInverseS.RawHom X Z :=
  f.comp g

example : Category (SInverseS.Pair (FGProjectiveCat.{u} R)) :=
  inferInstance

example (X Y : SInverseS.Pair (FGProjectiveCat.{u} R)) :
    (X ⟶ Y) = SInverseS.Hom X Y :=
  rfl

example :
    Core (FGProjectiveCat.{u} R) × Core (FGProjectiveCat.{u} R) ⥤
      SInverseS.Pair (FGProjectiveCat.{u} R) :=
  SInverseS.corePairInclusion

example : Core (FGProjectiveCat.{u} R) ⥤
    SInverseS.Pair (FGProjectiveCat.{u} R) :=
  SInverseS.coreInclusion

end CategoryTheory.SInverseSTests
