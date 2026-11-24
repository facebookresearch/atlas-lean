/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting

/-!
# Tests for structured pushout join and slice lifting
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

example {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    HasLiftingProperty (joinUnderPushoutMap i a) p ↔
      HasLiftingProperty a (sliceUnder.restrictionComparisonOfHom i p) :=
  sliceUnder.hasLiftingProperty_restrictionComparisonOfHom_iff i a p

example {K₀ K A B : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {P Q : Under K} {p : P ⟶ Q}
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (sliceUnder.restrictionArrowHomEquivOfHom i a p sq) :=
  sliceUnder.restrictionLiftStructEquivOfHom sq

example {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K)
    (f : K ⟶ X) (q : X ⟶ S) :
    sliceUnder.restrictionComparison i f q ≫
        pullback.fst (sliceUnder.map X (i ≫ f) q)
          (sliceUnder.restrict S (f ≫ q) i) =
      sliceUnder.restrict X f i := by
  simp

example {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    HasLiftingProperty (joinOverPushoutMap i a) p ↔
      HasLiftingProperty a (sliceOver.restrictionComparisonOfHom i p) :=
  sliceOver.hasLiftingProperty_restrictionComparisonOfHom_iff i a p

example {K₀ K A B : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {P Q : Under K} {p : P ⟶ Q}
    (sq : Arrow.mk (joinOverPushoutMap i a) ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (sliceOver.restrictionArrowHomEquivOfHom i a p sq) :=
  sliceOver.restrictionLiftStructEquivOfHom sq

example {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinOverPushoutMap i a).right = (joinOverPushoutObjObj i a).ι :=
  joinOverPushoutMap_right i a

example {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K)
    (f : K ⟶ X) (q : X ⟶ S) :
    sliceOver.restrictionComparison i f q ≫
        pullback.fst (sliceOver.map X (i ≫ f) q)
          (sliceOver.restrict S (f ≫ q) i) =
      sliceOver.restrict X f i := by
  simp

example {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    conjugateEquiv (joinOverAdjunction K)
        (joinOverRestrictionAdjunction i)
        (joinOverRestrictionNatTrans i) =
      sliceOver.restrictionNatTrans i :=
  joinOverRestrictionNatTrans_is_mate i


example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    (Arrow.mk (joinUnderPushoutMap i a) ⟶
        Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceUnder.restrictionComparison i f q)) :=
  sliceUnder.restrictionArrowHomEquiv i a f q

example {K₀ K A B X S : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {f : K ⟶ X} {q : X ⟶ S}
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (sliceUnder.restrictionArrowHomEquiv i a f q sq) :=
  sliceUnder.restrictionLiftStructEquiv sq

example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    HasLiftingProperty (joinUnderPushoutMap i a)
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ↔
      HasLiftingProperty a (sliceUnder.restrictionComparison i f q) :=
  sliceUnder.hasLiftingProperty_restrictionComparison_iff i a f q

example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    (Arrow.mk (joinOverPushoutMap i a) ⟶
        Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceOver.restrictionComparison i f q)) :=
  sliceOver.restrictionArrowHomEquiv i a f q

example {K₀ K A B X S : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {f : K ⟶ X} {q : X ⟶ S}
    (sq : Arrow.mk (joinOverPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (sliceOver.restrictionArrowHomEquiv i a f q sq) :=
  sliceOver.restrictionLiftStructEquiv sq

example {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    HasLiftingProperty (joinOverPushoutMap i a)
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ↔
      HasLiftingProperty a (sliceOver.restrictionComparison i f q) :=
  sliceOver.hasLiftingProperty_restrictionComparison_iff i a f q

end SSet
