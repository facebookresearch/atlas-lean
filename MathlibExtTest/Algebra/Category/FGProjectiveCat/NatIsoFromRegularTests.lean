/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.NatIsoFromRegular

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

variable {R : Type u} [Ring R]
variable {D : Type w} [Category.{v} D] [Preadditive D]
variable {F G : FGProjectiveCat.{u} R ⥤ D} [F.Additive] [G.Additive]
variable (η : F ⟶ G) [IsIso (η.app (FGProjectiveCat.regular R))]

example (P : FGProjectiveCat.{u} R) : IsIso (η.app P) :=
  FGProjectiveCat.isIso_natTrans_app_of_regular η P

example : (FGProjectiveCat.natIsoOfRegular η).hom = η := by simp

example : IsIso (η.app (FGProjectiveCat.standardFree R 0)) :=
  FGProjectiveCat.isIso_natTrans_app_of_regular η _

end
