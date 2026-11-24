/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinUniformLifting
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Generated lifting classes and pushout joins

This file gives the double-orthogonal form of Joyal's Lemma 3.16. A class of
pushout joins contained in a generated left lifting class on generators
remains contained there after generating both input classes.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet

/-- Pushout joins that lie in a generated left lifting class on generators
continue to do so after replacing both input classes by their double left
orthogonals. -/
theorem pushoutJoin_mem_rlp_llp
    (P Q R : MorphismProperty SSet.{u})
    (hfree : ∀ ⦃A B K L : SSet.{u}⦄ (i : A ⟶ B), P i →
      ∀ (j : K ⟶ L), Q j →
        R.rlp.llp (joinUnderPushoutObjObj i j).ι)
    {A B K L : SSet.{u}} {i : A ⟶ B} {j : K ⟶ L}
    (hi : P.rlp.llp i) (hj : Q.rlp.llp j) :
    R.rlp.llp (joinUnderPushoutObjObj i j).ι := by
  intro X Y p hp
  apply (sliceOver.hasLiftingProperty_pushoutJoin_iff_forall j i p).mpr
  intro f
  apply hi
  intro A' B' a ha
  apply (sliceOver.hasLiftingProperty_pushoutJoin_iff_forall j a p).mp
  apply (sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall a j p).mpr
  intro g
  apply hj
  intro K' L' b hb
  apply (sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall a b p).mp
  exact hfree a ha b hb p hp

end SSet
