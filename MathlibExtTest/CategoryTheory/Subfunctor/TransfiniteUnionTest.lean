/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uC vC uV uJ
open CategoryTheory CategoryTheory.Limits

namespace SubfunctorChainDataTest
variable {C : Type uC} [Category.{vC} C] {D : C ⥤ Type uV}
    {J : Type uJ} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (A : Subfunctor D) (B : J → Subfunctor D)

/-- Original union legs retain the SAME target D and actual underlying point. -/
example (j : J) :
    (Subfunctor.chainUnionCocone (Subfunctor.strictPrefixUnion A B)
      (Subfunctor.strictPrefixUnion_mono A B)).ι.app j ≫
      (⨆ k : J, Subfunctor.strictPrefixUnion A B k).ι =
    (Subfunctor.strictPrefixUnion A B j).ι :=
  Subfunctor.homOfLe_ι (le_iSup (Subfunctor.strictPrefixUnion A B) j)

/-- Original sites/operators act on the same point before inclusion. -/
example (j : J) {X Y : C} (f : X ⟶ Y)
    (x : (Subfunctor.strictPrefixUnion A B j).toFunctor.obj X) :
    (((Subfunctor.strictPrefixUnion A B j).toFunctor.map f) x).val = D.map f x.val := rfl

/-- At zero only A is present; seeds at maximal stages are not falsely included. -/
example : Subfunctor.strictPrefixUnion A B ⊥ = A := Subfunctor.strictPrefixUnion_bot A B

/-- Actual final-prefix geometry with a TRUE step-property input, not a supplied transfinite packet. -/
def actual_prefix (P : MorphismProperty (C ⥤ Type uV))
    (hstep : ∀ j : J, ¬ IsMax j → P (Subfunctor.homOfLe
      (Subfunctor.strictPrefixUnion_mono A B (Order.le_succ j)))) (t : J) :
    P.TransfiniteCompositionOfShape (Set.Iic t)
      (Subfunctor.homOfLe (show A ≤ Subfunctor.strictPrefixUnion A B t from le_sup_left)) :=
  Subfunctor.strictPrefixTransfinite A B P hstep t

end SubfunctorChainDataTest
