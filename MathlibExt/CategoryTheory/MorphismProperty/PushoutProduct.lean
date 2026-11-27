/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Orthogonality and pushout-products

This file records two generic consequences of lifting adjunctions. The first
computes the right orthogonal of a strict functorial image. The second extends
a pushout-product lifting theorem from test classes to their double left
orthogonals.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ u₁ v₂ u₂ v u

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.MorphismProperty

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The right orthogonal of a literal strict image along a left adjoint is
the inverse image of the original right orthogonal along the right adjoint. -/
theorem strictMap_rlp_eq_inverseImage_rlp
    (P : MorphismProperty C) (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) :
    (P.strictMap L).rlp = P.rlp.inverseImage R := by
  ext X Y p
  constructor
  · intro hp A B i hi
    exact (adj.hasLiftingProperty_iff i p).mp
      (hp (L.map i) (P.map_mem_strictMap L i hi))
  · intro hp A B i hi
    cases hi with
    | map hi =>
        exact (adj.hasLiftingProperty_iff _ p).mpr (hp _ hi)

variable {E : Type u} [Category.{v} E]
variable [HasPushouts E] [HasPullbacks E]
variable [MonoidalCategory E] [MonoidalClosed E] [BraidedCategory E]

/-- If pushout-products of maps in `A` and `B` lie in the double left
orthogonal of `K`, the same holds for maps in the double left orthogonals of
`A` and `B`. -/
theorem pushoutProduct_mem_rlp_llp
    (A B K : MorphismProperty E)
    (hfree : ∀ ⦃X Y W Z : E⦄ (a : X ⟶ Y), A a →
      ∀ (b : W ⟶ Z), B b →
        K.rlp.llp ((Arrow.mk a □ Arrow.mk b).hom))
    {X Y W Z : E} {i : X ⟶ Y} {j : W ⟶ Z}
    (hi : A.rlp.llp i) (hj : B.rlp.llp j) :
    K.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) := by
  intro P Q p hp
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mpr
  apply hi
  intro X' Y' a ha
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mp
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mpr
  apply hj
  intro W' Z' b hb
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mp
  exact hfree a ha b hb p hp

end CategoryTheory.MorphismProperty
