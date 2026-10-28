/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2MonomialFamilies

/-! The actual root-line stabilizer acts on the original neighboring short labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine Leech isometries preserve the integer pairing before normalization. -/
theorem leechRootedA2_integral_pairing_action (e : leechIsomSubgroup)
    (u v : leechIntegral) :
    leechIntegralPairing (leechIntegralAction e u).val (leechIntegralAction e v).val =
      leechIntegralPairing u.val v.val := by
  have h := leechIntegralAction_squareSum e (u + v)
  simp only [map_add, Submodule.coe_add] at h
  rw [leechSquareSum_add, leechSquareSum_add, leechIntegralAction_squareSum,
    leechIntegralAction_squareSum] at h
  linarith

/-- The actual short-label neighbor condition is equivalent to its squared root pairing. -/
theorem leechRootedA2_neighbor_pairing_iff (r : GriessShortIndex) :
    leechRootedA2NeighborPredicate r ↔
      leechIntegralPairing leechRootedA2Root.val (griessShortLatticeVector r).val ^ 2 = 256 := by
  change _ ↔ leechIntegralPairing leechRootedA2RootIntegral (griessShortIntegral r) ^ 2 = 256
  rw [leechRootedA2RootIntegral_pairing]
  constructor
  · rintro (h | h) <;> rw [h] <;> norm_num
  · intro h
    have he : (griessShortIntegral r 0 + griessShortIntegral r 1) ^ 2 = (4 : ℤ) ^ 2 := by
      nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp he

/-- Every genuine root-line stabilizer preserves the original neighbor predicate. -/
theorem leechRootedA2_root_action_neighbor (e : leechIsomSubgroup)
    (he : leechRootedA2PreservesRootLine e) (r : GriessShortIndex)
    (hr : leechRootedA2NeighborPredicate r) :
    leechRootedA2NeighborPredicate (griessShortPermutation e r) := by
  apply (leechRootedA2_neighbor_pairing_iff _).mpr
  have hp := leechRootedA2_integral_pairing_action e leechRootedA2Root
    (griessShortLatticeVector r)
  have hn := (leechRootedA2_neighbor_pairing_iff r).mp hr
  rcases he with he | he <;>
    rcases leechRootedA2_short_integral_image e r with hi | hi <;>
    rw [he, hi] at hp <;>
    simp only [Submodule.coe_neg, leechIntegralPairing, Pi.neg_apply, neg_mul,
      mul_neg, neg_neg, Finset.sum_neg_distrib] at hp hn ⊢ <;>
    (have hs := congrArg (fun n : ℤ => n ^ 2) hp
     simpa only [neg_sq] using hs.trans hn)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
