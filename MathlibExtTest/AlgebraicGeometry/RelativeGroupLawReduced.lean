/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawReduced
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RelativeGroupLawReducedTest

/-- Consumer for reducedness in characteristic zero, with the original
binders. -/
theorem exactSource_isReduced_of_charZero
    (k : Type u) [Field k] [CharZero k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    IsReduced G :=
  L.isReduced_of_charZero k g

/-- Consumer for reducedness from the identity stalk over an algebraically
closed field, with the original binders. -/
theorem exactSource_isReduced_of_isReduced_stalk_one_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (he : _root_.IsReduced (G.presheaf.stalk
      ((L.one (𝟙 (Spec (CommRingCat.of k)))).left (IsLocalRing.closedPoint k)))) :
    IsReduced G :=
  L.isReduced_of_isReduced_stalk_one_of_isAlgClosed k g he

/-- Consumer for smoothness in characteristic zero, with the original
binders. -/
theorem exactSource_smooth_of_charZero
    (k : Type u) [Field k] [CharZero k] {G : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    Smooth g :=
  L.smooth_of_charZero k g

/-- The reducedness consumer in a higher universe. -/
theorem exactSource_isReduced_of_charZero_univ1
    (k : Type 1) [Field k] [CharZero k] {G : Scheme.{1}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    IsReduced G :=
  L.isReduced_of_charZero k g

/-- The smoothness consumer in a higher universe. -/
theorem exactSource_smooth_of_charZero_univ1
    (k : Type 1) [Field k] [CharZero k] {G : Scheme.{1}}
    (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    Smooth g :=
  L.smooth_of_charZero k g

/-- Boundary example: reducedness is not automatic for locally finite type
schemes over a field. The dual numbers give a locally finite type scheme
that is not reduced, so the group-law and characteristic-zero hypotheses
cannot simply be dropped. -/
example (k : Type u) [Field k] :
    ¬ IsReduced (Spec (CommRingCat.of (DualNumber k))) := by
  rw [affine_isReduced_iff]
  intro h
  haveI := h
  have h0 : (TrivSqZeroExt.inr (1 : k) : DualNumber k) = 0 :=
    IsReduced.eq_zero _ ⟨2, by ext <;> simp⟩
  have h1 : (1 : k) = 0 := by
    have h2 := congrArg (TrivSqZeroExt.snd (R := k) (M := k)) h0
    simpa using h2
  exact one_ne_zero h1

end RelativeGroupLawReducedTest
