/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IsUnitCard
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

open CategoryTheory

universe u

-- General consumer of the projectivity lemma.
example {k G : Type u} [CommRing k] [Group G] [Finite G] (h : IsUnit (Nat.card G : k)) :
    Projective (Rep.trivial k G k) :=
  Rep.trivial_projective_of_isUnit_natCard h

-- Over a field of characteristic zero every finite group order is a unit.
example {G : Type} [Group G] [Finite G] (A : Rep ℚ G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  groupCohomology.isZero_succ_of_isUnit_natCard
    (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 Nat.card_pos.ne')) A n

-- Concrete group of order 2 over `ZMod 3`, through the corollary.
example (A : Rep (ZMod 3) (Multiplicative (ZMod 2))) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  groupCohomology.isZero_succ_zmod_of_coprime_natCard
    (by rw [Nat.card_eq_fintype_card]; decide) A n

-- Concrete group of order 2 over `ℚ`, through the main theorem.
example (A : Rep ℚ (Multiplicative (ZMod 2))) :
    Limits.IsZero (groupCohomology A 1) :=
  groupCohomology.isZero_succ_of_isUnit_natCard
    (by rw [Nat.card_eq_fintype_card]; norm_num) A 0

-- `p` need not be prime: order 3 over `ZMod 4`.
example (A : Rep (ZMod 4) (Multiplicative (ZMod 3))) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  groupCohomology.isZero_succ_zmod_of_coprime_natCard
    (by rw [Nat.card_eq_fintype_card]; decide) A n

-- Projectivity for a concrete group over `ZMod 5`.
example : Projective (Rep.trivial (ZMod 5) (Multiplicative (ZMod 2)) (ZMod 5)) :=
  Rep.trivial_projective_of_isUnit_natCard
    ((ZMod.isUnit_iff_coprime _ _).2 (by rw [Nat.card_eq_fintype_card]; decide))
