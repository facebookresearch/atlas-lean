/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorTripleTensor

set_option autoImplicit false
noncomputable section
universe uV vV
open CategoryTheory MonoidalCategory

namespace MathlibExtTest.SphereOperatorTripleTensor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

example (W Z T A B C : V) :
    ((tensorδ W Z A B ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom)) ▷ (T ⊗ C)) ≫
        (tensorδ (W ⊗ Z) T (B ⊗ A) C ≫
          (𝟙 ((W ⊗ Z) ⊗ T) ⊗ₘ (β_ (B ⊗ A) C).hom)) ≫
        ((α_ W Z T).hom ⊗ₘ (α_ C B A).inv) =
      (α_ (W ⊗ A) (Z ⊗ B) (T ⊗ C)).hom ≫
        ((W ⊗ A) ◁ (tensorδ Z T B C ≫
          (𝟙 (Z ⊗ T) ⊗ₘ (β_ B C).hom))) ≫
        (tensorδ W (Z ⊗ T) A (C ⊗ B) ≫
          (𝟙 (W ⊗ (Z ⊗ T)) ⊗ₘ (β_ A (C ⊗ B)).hom)) :=
  Enriched.SphereOperator.tensorDelta_ordered_triple W Z T A B C

#check @CategoryTheory.Enriched.SphereOperator.tensorDelta_ordered_triple
#print axioms CategoryTheory.Enriched.SphereOperator.tensorDelta_ordered_triple

end MathlibExtTest.SphereOperatorTripleTensor
