/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting
public import MathlibExt.CategoryTheory.LiftingProperties.Under

/-!
# Uniform lifting for pushout joins and slice comparisons

This file formalizes both orientations of Joyal's Lemma 3.15. A raw pushout
join lifts against a simplicial map exactly when the varying factor lifts
against every corresponding concrete slice comparison.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- The over-oriented pushout join lifts against `q` exactly when `a` lifts
against every concrete over-slice restriction comparison. -/
theorem sliceOver.hasLiftingProperty_pushoutJoin_iff_forall
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (q : X ⟶ S) :
    HasLiftingProperty (joinOverPushoutObjObj i a).ι q ↔
      ∀ (f : K ⟶ X),
        HasLiftingProperty a (sliceOver.restrictionComparison i f q) := by
  rw [← joinOverPushoutMap_right]
  constructor
  · intro h f
    exact (sliceOver.hasLiftingProperty_restrictionComparison_iff i a f q).mp
      ((CategoryTheory.Under.hasLiftingProperty_right_iff_forall
        (joinOverPushoutMap i a) q).mp h f)
  · intro h
    apply (CategoryTheory.Under.hasLiftingProperty_right_iff_forall
      (joinOverPushoutMap i a) q).mpr
    intro f
    exact (sliceOver.hasLiftingProperty_restrictionComparison_iff i a f q).mpr
      (h f)

/-- The under-oriented pushout join lifts against `q` exactly when `a` lifts
against every concrete under-slice restriction comparison. -/
theorem sliceUnder.hasLiftingProperty_pushoutJoin_iff_forall
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (q : X ⟶ S) :
    HasLiftingProperty (joinUnderPushoutObjObj i a).ι q ↔
      ∀ (f : K ⟶ X),
        HasLiftingProperty a (sliceUnder.restrictionComparison i f q) := by
  rw [← joinUnderPushoutMap_right]
  constructor
  · intro h f
    exact (sliceUnder.hasLiftingProperty_restrictionComparison_iff i a f q).mp
      ((CategoryTheory.Under.hasLiftingProperty_right_iff_forall
        (joinUnderPushoutMap i a) q).mp h f)
  · intro h
    apply (CategoryTheory.Under.hasLiftingProperty_right_iff_forall
      (joinUnderPushoutMap i a) q).mpr
    intro f
    exact (sliceUnder.hasLiftingProperty_restrictionComparison_iff i a f q).mpr
      (h f)

end SSet
