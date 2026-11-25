/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Adjunction

/-! # Tests for category homology invariance under adjunctions -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u vA uA

namespace CategoryTheory.CategoryHomologyAdjunctionTests

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max u v} A] [CategoryWithHomology A]

example (F : C ⥤ D) (G : D ⥤ C) (h : F ⊣ G)
    (R : A) (n : ℕ) :
    (nerve C).homology R n ≅ (nerve D).homology R n :=
  categoryHomologyIsoOfAdjunction A F G h R n

end CategoryTheory.CategoryHomologyAdjunctionTests

end
