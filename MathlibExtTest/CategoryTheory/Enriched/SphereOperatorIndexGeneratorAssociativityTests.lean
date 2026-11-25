/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexGeneratorAssociativity

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.SphereOperatorIndexGeneratorAssociativity

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The entire original index cube has independent object/Hom universes
and requires neither closedness of V nor a braiding on I. -/
example (d : EnrichedMonoidalCategoryData V I) (n m k l a b c : I) :
    (Enriched.SphereOperator.indexGenerator d n m k a b ▷
        ((c ⊗ k) ⟶[V] l)) ≫
        Enriched.SphereOperator.indexGenerator d n k l (b ⊗ a) c ≫
        eHomWhiskerRight V ((α_ c b a).hom ⊗ₘ 𝟙 n) l =
      (α_ ((a ⊗ n) ⟶[V] m) ((b ⊗ m) ⟶[V] k)
          ((c ⊗ k) ⟶[V] l)).hom ≫
        ((a ⊗ n) ⟶[V] m) ◁
          Enriched.SphereOperator.indexGenerator d m k l b c ≫
        Enriched.SphereOperator.indexGenerator d n m l a (c ⊗ b) :=
  Enriched.SphereOperator.indexGenerator_assoc d n m k l a b c

#check @CategoryTheory.Enriched.SphereOperator.indexGenerator_assoc
#print axioms CategoryTheory.Enriched.SphereOperator.indexGenerator_assoc

end MathlibExtTest.SphereOperatorIndexGeneratorAssociativity
