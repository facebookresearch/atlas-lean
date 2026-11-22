/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Closed.InternalHomInterchange

/-!
# Internal currying and both source variables

The actual internal currying isomorphism commutes with precomposition
in either tensor factor. The proofs use the original associator and
the existing closed adjunction, in an arbitrary closed monoidal category.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

private theorem double_uncurry_post_currying (K L : C) {A X : C}
    (f : A ⟶ (ihom (K ⊗ L)).obj X) :
    uncurry (uncurry (f ≫ ihomCurry K L X)) =
      (α_ K L A).inv ≫ uncurry f := by
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, uncurry_eq]

/-- Internal currying retains precomposition in the first source factor. -/
@[reassoc] theorem ihomCurry_naturality_first {K K' : C} (a : K ⟶ K') (L X : C) :
    (pre (a ▷ L)).app X ≫ ihomCurry K L X =
      ihomCurry K' L X ≫ (ihom L).map ((pre a).app X) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [double_uncurry_post_currying, uncurry_pre, uncurry_natural_right,
    uncurry_pre_app, uncurry_uncurry_ihomCurry, associator_inv_naturality_left_assoc]

/-- Internal currying retains precomposition in the second source factor. -/
@[reassoc] theorem ihomCurry_naturality_second (K : C) {L L' : C} (b : L ⟶ L') (X : C) :
    (pre (K ◁ b)).app X ≫ ihomCurry K L X =
      ihomCurry K L' X ≫ (pre b).app ((ihom K).obj X) := by
  apply uncurry_injective
  apply uncurry_injective
  rw [double_uncurry_post_currying, uncurry_pre, uncurry_pre_app,
    uncurry_natural_left, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_middle_assoc]

end CategoryTheory.MonoidalClosed
