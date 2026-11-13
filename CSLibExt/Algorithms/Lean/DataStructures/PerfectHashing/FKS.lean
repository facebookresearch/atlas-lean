/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# FKS perfect hashing: a good primary hash exists

The two-level scheme of Fredman, Komlós, and Szemerédi (`PerfectHashing`) sends `n` keys to
`n` primary buckets and gives bucket `b`, holding `n_b` keys, a secondary table of size
`n_b²`. The total secondary space `∑ b, n_b²` is linear in `n` when the primary hash has few
collisions. This file proves that a universal family (`IsUniversalOn`) contains such a
primary hash.

The *ordered collision count* of a hash is `∑ b, n_b (n_b - 1)`, the number of ordered pairs
of distinct keys it sends to one bucket. Summed over a universal family into `m` buckets it
is at most `|s| n (n - 1) / m`, because each of the `n (n - 1)` ordered pairs collides under
at most `|s| / m` members; so some member is at most the average.

## Main statements

* `exists_sum_bucketCollisions_mul_le`: some member of a universal family into `m` buckets
  has ordered collision count at most `n (n - 1) / m`, stated without division.
* `fks_exists_good_hash` (the primary level, `m = n`): some member has fewer than `n`
  ordered collisions, and therefore `∑ b, n_b² < 2 n`.

This is the expectation bound for the primary hash in CLRS, phrased as an average over the
finite index set rather than as a probability.

## References

* M. L. Fredman, J. Komlós, and E. Szemerédi, *Storing a sparse table with O(1) worst case
  access time*, J. ACM 31(3) (1984).
* T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  third edition, Section 11.5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashing

universe u v

variable {K : Type u} [Fintype K] {ι : Type v} {s : Finset ι}

/-- The ordered pairs of distinct keys that `h i` sends to one bucket, split by that bucket:
the pairs in bucket `b` are the off-diagonal of the keys hashed to `b`. -/
private theorem card_collidingPairs_eq_sum {m : ℕ} (h : ι → K → Fin m)
    (i : ι) :
    (Finset.univ.offDiag.filter fun p : K × K => h i p.1 = h i p.2).card =
      ∑ b, (Finset.univ.filter fun x => h i x = b).card *
        ((Finset.univ.filter fun x => h i x = b).card - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : K × K => h i p.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfiber : ((Finset.univ.offDiag.filter fun p : K × K => h i p.1 = h i p.2).filter
      fun p => h i p.1 = b) = (Finset.univ.filter fun x => h i x = b).offDiag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hne, hcol⟩, hb⟩
      exact ⟨hb, hcol.symm.trans hb, hne⟩
    · rintro ⟨h1, h2, hne⟩
      exact ⟨⟨hne, h1.trans h2.symm⟩, h1⟩
  rw [hfiber, Finset.offDiag_card, Nat.mul_sub_one]

/-- Summed over a universal family, the colliding ordered pairs number at most
`|s| n (n - 1) / m`: each ordered pair of distinct keys collides under at most `|s| / m`
members. -/
private theorem sum_card_collidingPairs_mul_le {m : ℕ} {h : ι → K → Fin m}
    (hu : IsUniversalOn s h) :
    (∑ i ∈ s, (Finset.univ.offDiag.filter fun p : K × K => h i p.1 = h i p.2).card) * m ≤
      s.card * (Fintype.card K * Fintype.card K - Fintype.card K) := by
  have hswap :
      (∑ i ∈ s, (Finset.univ.offDiag.filter fun p : K × K => h i p.1 = h i p.2).card) =
        ∑ p ∈ (Finset.univ : Finset K).offDiag, (s.filter fun i => h i p.1 = h i p.2).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  calc (∑ p ∈ (Finset.univ : Finset K).offDiag, (s.filter fun i => h i p.1 = h i p.2).card * m)
      ≤ ∑ _p ∈ (Finset.univ : Finset K).offDiag, s.card :=
        Finset.sum_le_sum fun p hp => hu.2.2 p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
    _ = s.card * (Fintype.card K * Fintype.card K - Fintype.card K) := by
        rw [Finset.sum_const, Finset.offDiag_card, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

/-- **A universal family has a member with few collisions.** For a universal family into
`m` buckets, some member has ordered collision count `∑ b, n_b (n_b - 1)` at most
`n (n - 1) / m`, stated without division, where `n_b` is the number of keys hashed to
bucket `b`. -/
theorem exists_sum_bucketCollisions_mul_le {m : ℕ} {h : ι → K → Fin m}
    (hu : IsUniversalOn s h) :
    ∃ i ∈ s, (∑ b, (Finset.univ.filter fun x => h i x = b).card *
        ((Finset.univ.filter fun x => h i x = b).card - 1)) * m ≤
      Fintype.card K * (Fintype.card K - 1) := by
  classical
  obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le hu.2.1
    (f := fun i => (Finset.univ.offDiag.filter fun p : K × K => h i p.1 = h i p.2).card * m)
    (g := fun _ => Fintype.card K * (Fintype.card K - 1)) (by
      rw [← Finset.sum_mul, Finset.sum_const, smul_eq_mul, Nat.mul_sub_one]
      exact sum_card_collidingPairs_mul_le hu)
  exact ⟨i, hi, by rw [← card_collidingPairs_eq_sum]; exact hle⟩

/-- **FKS primary hash** (CLRS, Section 11.5). A universal family hashing the keys `K` into
`n = |K|` buckets has a member with fewer than `n` ordered collisions
(`∑ b, n_b (n_b - 1) < n`), so its squared bucket sizes sum to less than `2 n`: with
secondary tables of sizes `n_b²`, the two-level scheme then uses linear total space. -/
theorem fks_exists_good_hash {h : ι → K → Fin (Fintype.card K)} (hu : IsUniversalOn s h) :
    ∃ i ∈ s,
      ∑ b, (Finset.univ.filter fun x => h i x = b).card *
          ((Finset.univ.filter fun x => h i x = b).card - 1) < Fintype.card K ∧
      ∑ b, (Finset.univ.filter fun x => h i x = b).card ^ 2 < 2 * Fintype.card K := by
  obtain ⟨i, hi, hle⟩ := exists_sum_bucketCollisions_mul_le hu
  have hpos : 0 < Fintype.card K := hu.1
  rw [Nat.mul_comm (Fintype.card K) (Fintype.card K - 1)] at hle
  have hcoll := Nat.le_of_mul_le_mul_right hle hpos
  refine ⟨i, hi, by omega, ?_⟩
  have hsum : ∑ b, (Finset.univ.filter fun x => h i x = b).card = Fintype.card K := by
    have hfib := Finset.card_eq_sum_card_fiberwise (f := h i) (s := (Finset.univ : Finset K))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at hfib
    exact hfib.symm
  have hsq : ∀ c : ℕ, c ^ 2 = c * (c - 1) + c := by
    intro c
    cases c with
    | zero => rfl
    | succ k =>
        rw [Nat.add_sub_cancel]
        ring
  rw [Finset.sum_congr rfl fun b _ => hsq _, Finset.sum_add_distrib, hsum]
  omega

end Cslib.Algorithms.Lean.UniversalHashing
