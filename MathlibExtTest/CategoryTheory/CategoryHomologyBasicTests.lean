/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Basic

/-! # Tests for homology of a small category -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomologyBasicTests

variable (A : Type u₂) [Category.{v₂} A] [Preadditive A]
  [HasCoproducts.{max u₁ v₁} A] [CategoryWithHomology A]
  (R : A) (n : ℕ)

example : CategoryTheory.Functor Cat.{v₁, u₁} A :=
  categoryHomologyFunctor A R n

variable {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  {F G : CategoryTheory.Functor C D}

example (α : F ⟶ G) :
    (categoryHomologyFunctor A R n).map F.toCatHom =
      (categoryHomologyFunctor A R n).map G.toCatHom :=
  categoryHomologyMap_eq_of_natTrans A α R n

example (e : F ≅ G) :
    (categoryHomologyFunctor A R n).map F.toCatHom =
      (categoryHomologyFunctor A R n).map G.toCatHom :=
  categoryHomologyMap_eq_of_natIso A e R n

example (e : C ≌ D) :
    (nerve C).homology R n ≅ (nerve D).homology R n :=
  categoryHomologyIsoOfEquivalence A e R n

end CategoryTheory.CategoryHomologyBasicTests

end
