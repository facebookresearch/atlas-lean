/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexAssociator

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.SphereOperatorIndexAssociator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The public full-Hom square works with independent object and morphism
universes, without closedness of V or a braiding on I. -/
example (d : EnrichedMonoidalCategoryData V I) (c b x y : I) :
    ((λ_ (x ⟶[V] y)).inv ≫
        (eId V (c ⊗ b) ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
        d.tensorMap (c ⊗ b) (c ⊗ b) x y) ≫
        eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom =
      ((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y ≫
          (λ_ ((b ⊗ x) ⟶[V] (b ⊗ y))).inv ≫
          (eId V c ⊗ₘ 𝟙 ((b ⊗ x) ⟶[V] (b ⊗ y))) ≫
          d.tensorMap c c (b ⊗ x) (b ⊗ y)) ≫
        eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)) :=
  Enriched.SphereOperator.associator_third_full_hom d c b x y

#check @CategoryTheory.Enriched.SphereOperator.associator_third_full_hom
#print axioms CategoryTheory.Enriched.SphereOperator.associator_third_full_hom

end MathlibExtTest.SphereOperatorIndexAssociator
