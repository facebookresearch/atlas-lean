/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Unitors
import MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition
import Mathlib.Tactic

/-!
# Full enriched tensor parameter actions

These public clients retain the two complete Hom parameters, their actual unit
insertions, and the original source tensor data in independent universes.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace MathlibExtTest.FullTensorExchange

section Units
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

example {A B X Y : V} (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) :
    (((λ_ X).inv ≫ (f ⊗ₘ 𝟙 X)) ⊗ₘ
        ((ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ g))) ≫ tensorμ A X Y B =
      (β_ X Y).hom ≫
        (((λ_ Y).inv ≫ (f ⊗ₘ 𝟙 Y)) ⊗ₘ
          ((ρ_ X).inv ≫ (𝟙 X ⊗ₘ g))) :=
  EnrichedDayKernel.Unitors.tensorMu_two_units_exchange f g
end Units

section Tensor
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

example (b b' x y : I) :
    (((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y) ⊗ₘ
        (Enriched.SphereOperator.fixedRightTensor d y).map b b') ≫
      eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) =
    (β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫
      ((Enriched.SphereOperator.fixedRightTensor d x).map b b' ⊗ₘ
        ((λ_ (x ⟶[V] y)).inv ≫
          (eId V b' ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b' b' x y)) ≫
      eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) :=
  Enriched.SphereOperator.tensor_full_exchange d b b' x y

example (b x : I) :
    eId V x ≫ (λ_ (x ⟶[V] x)).inv ≫
        (eId V b ⊗ₘ 𝟙 (x ⟶[V] x)) ≫ d.tensorMap b b x x =
      eId V (b ⊗ x) :=
  Enriched.SphereOperator.tensor_left_id d b x

example (b x y z : I) :
    eComp V x y z ≫ (λ_ (x ⟶[V] z)).inv ≫
        (eId V b ⊗ₘ 𝟙 (x ⟶[V] z)) ≫ d.tensorMap b b x z =
      (((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y) ⊗ₘ
        ((λ_ (y ⟶[V] z)).inv ≫
          (eId V b ⊗ₘ 𝟙 (y ⟶[V] z)) ≫ d.tensorMap b b y z)) ≫
      eComp V (b ⊗ x) (b ⊗ y) (b ⊗ z) :=
  Enriched.SphereOperator.tensor_left_comp d b x y z
end Tensor

#check @EnrichedDayKernel.Unitors.tensorMu_two_units_exchange
#check @Enriched.SphereOperator.tensor_full_exchange
#check @Enriched.SphereOperator.tensor_left_id
#check @Enriched.SphereOperator.tensor_left_comp
#print axioms EnrichedDayKernel.Unitors.tensorMu_two_units_exchange
#print axioms Enriched.SphereOperator.tensor_full_exchange
#print axioms Enriched.SphereOperator.tensor_left_id
#print axioms Enriched.SphereOperator.tensor_left_comp

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Unitors
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition

end MathlibExtTest.FullTensorExchange
