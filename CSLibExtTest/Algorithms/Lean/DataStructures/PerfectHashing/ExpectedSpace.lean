/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing.ExpectedSpace

/-!
# Smoke tests for the two-level expected-space bounds
-/

namespace Cslib.Algorithms.Lean

open PerfectHashing UniversalHashing

private def testTable : PerfectHashing ℕ ℕ id where
  bucketCount := 2
  bucketCount_pos := by decide
  secondarySize i := if i = 0 then 1 else 0
  secondaryHash _ _ := 0
  secondaryTable i := Vector.replicate (if i = 0 then 1 else 0) (some (0, 42))

-- A hit, a query into an empty bucket, and an absent key landing on an occupied cell.
example : lookupWithProbes 0 testTable = (some 42, 2) := by decide
example : lookupWithProbes 1 testTable = (none, 1) := by decide
example : lookupWithProbes 2 testTable = (none, 2) := by decide

example : (lookupWithProbes 2 testTable).1 = lookup 2 testTable :=
  (lookupWithProbes_spec 2 testTable).1

private def noSecondary (hk : (∅ : Finset ℕ).Nonempty) : Unit → ℕ → Fin 0 :=
  (Finset.not_nonempty_empty hk).elim

-- No trial, not even the initial one, is required for an empty bucket.
example : HasSum (fun t => (secondaryAttemptTail ∅ ∅ noSecondary t : ℝ)) 0 := by
  obtain ⟨_, draws, hsum, _, hzero, _, _⟩ :=
    secondary_sampling ∅ ∅ noSecondary (fun hk => (Finset.not_nonempty_empty hk).elim)
  rwa [hzero Finset.not_nonempty_empty] at hsum

private def singletonKeys : Finset (Fin 1) := {0}

private def singletonHash (_ : singletonKeys.Nonempty) (_ : Unit) (_ : Fin 1) :
    Fin (2 * singletonKeys.card ^ 2) := ⟨0, by decide⟩

-- A singleton always succeeds on the first trial, including the initial draw in the mean.
example : HasSum
    (fun t => (secondaryAttemptTail singletonKeys {()} singletonHash t : ℝ)) 1 := by
  have hnear (hk : singletonKeys.Nonempty) : IsNearUniversalOn singletonKeys {()} (singletonHash hk) :=
    ⟨by decide, Finset.singleton_nonempty _,
      fun x _ y _ hxy => (hxy (Subsingleton.elim x y)).elim⟩
  obtain ⟨_, draws, hsum, _, _, _, hone⟩ := secondary_sampling singletonKeys {()} singletonHash hnear
  rwa [hone (by decide)] at hsum

private def primary (_ : Unit) (_ : Fin 1) : Fin singletonKeys.card := ⟨0, by decide⟩

private theorem primaryNear : IsNearUniversalOn singletonKeys {()} primary :=
  ⟨by decide, Finset.singleton_nonempty _, fun x _ y _ hxy => (hxy (Subsingleton.elim x y)).elim⟩

-- Instantiate the whole construction, including the ordinary lookup of a stored value.
example : ∃ table : PerfectHashing (Fin 1) ℕ (fun x => (primary () x).val),
    table.Valid ∧ lookup 0 table = some 42 := by
  have hnear (i : Unit) (j : Fin singletonKeys.card)
      (hk : (bucketKeys singletonKeys (primary i) j).Nonempty) :
      IsNearUniversalOn (bucketKeys singletonKeys (primary i) j) {()} (fun (_ : Unit) (_ : Fin 1) =>
        (⟨0, by have := hk.card_pos; positivity⟩ :
          Fin (2 * (bucketKeys singletonKeys (primary i) j).card ^ 2))) :=
    ⟨by have := hk.card_pos; positivity, Finset.singleton_nonempty _,
      fun x _ y _ hxy => (hxy (Subsingleton.elim x y)).elim⟩
  obtain ⟨g, _, _, _, tables⟩ := two_level_expected_space singletonKeys (fun _ => 42)
    primaryNear (fun _ _ => {()}) (fun i j hk _ _ => ⟨0, by have := hk.card_pos; positivity⟩)
    (fun i _ j hk => hnear i j hk)
  obtain ⟨hvalid, hlookup⟩ := tables () (Finset.mem_singleton_self ())
  exact ⟨ofBucketHashes singletonKeys (fun _ => 42) primaryNear.1 (primary ()) (g ()),
    hvalid, (hlookup 0).1.trans (by decide)⟩

private def natHash (i : Bool) (x : ℕ) : Fin 3 :=
  if i then ⟨x % 3, Nat.mod_lt _ (by decide)⟩ else 0

-- On these three natural keys, each distinct pair collides for one of the two indices.
-- This needs the 2/m bound, not 1/m. Outside the set, 0 and 3 collide at both indices.
example : IsNearUniversalOn ({0, 1, 2} : Finset ℕ) Finset.univ natHash := by
  refine ⟨by decide, ⟨false, Finset.mem_univ _⟩, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;> decide

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def tripleKeys : Finset (ZMod 11) := {0, 1, 3}
private theorem triplePos : 0 < tripleKeys.card := by decide
private def primaryModPrime := modPrimeHashes 11 tripleKeys.card triplePos
private def indices : Finset (ModPrimeIndex 11) := Finset.univ

private def secondaryModPrime (i : ModPrimeIndex 11) (j : Fin tripleKeys.card)
    (hk : (bucketKeys tripleKeys (primaryModPrime i) j).Nonempty) :=
  modPrimeHashes 11 (2 * (bucketKeys tripleKeys (primaryModPrime i) j).card ^ 2)
    (by have := hk.card_pos; positivity)

-- Three keys into three buckets, using the existing 1/m bound for both families.
example : (∑ i ∈ indices, ∑ j, ((bucketKeys tripleKeys (primaryModPrime i) j).card : ℚ) ^ 2) /
    indices.card ≤ 7 := by
  have hnear : IsNearUniversalOn tripleKeys indices primaryModPrime :=
    (modPrime_isUniversalOn (p := 11) triplePos).isNearUniversalOn tripleKeys
  obtain ⟨_, _, hmean, _, _⟩ := two_level_expected_space tripleKeys ZMod.val hnear
    (fun _ _ => indices) secondaryModPrime (fun i _ j hk =>
      (modPrime_isUniversalOn (p := 11) (by have := hk.card_pos; positivity)).isNearUniversalOn
        (bucketKeys tripleKeys (primaryModPrime i) j))
  have hn : tripleKeys.card = 3 := by decide
  exact hmean.trans (by norm_num [hn])

-- The primary index (1, 0) puts 0 and 3 in the same bucket, giving eight secondary slots.
private def primaryIndex : ModPrimeIndex 11 := (⟨1, by decide⟩, 0)
private def zeroBucket : Fin tripleKeys.card := ⟨0, triplePos⟩
private def pairKeys := bucketKeys tripleKeys (primaryModPrime primaryIndex) zeroBucket
private theorem pairKeys_eq : pairKeys = ({0, 3} : Finset (ZMod 11)) := by decide
private theorem pairKeys_nonempty : pairKeys.Nonempty := by
  rw [pairKeys_eq]
  exact ⟨0, by decide⟩
private def pairHash (hk : pairKeys.Nonempty) := secondaryModPrime primaryIndex zeroBucket hk

-- The secondary index (1, 8) really fails on this pair, but the failure fraction is below 1/2.
private def badIndex : ModPrimeIndex 11 := (⟨1, by decide⟩, 8)

example : (¬ Set.InjOn (pairHash pairKeys_nonempty badIndex) (pairKeys : Set (ZMod 11))) ∧
    secondaryAttemptTail pairKeys indices pairHash 1 < 1 / 2 := by
  have hnear (hk : pairKeys.Nonempty) : IsNearUniversalOn pairKeys indices (pairHash hk) :=
    (modPrime_isUniversalOn (p := 11) (m := 2 * pairKeys.card ^ 2)
      (by have := hk.card_pos; positivity)).isNearUniversalOn pairKeys
  refine ⟨?_, ((secondary_sampling pairKeys indices pairHash hnear).1 pairKeys_nonempty).2.1⟩
  intro hinj
  have h0 : (0 : ZMod 11) ∈ (pairKeys : Set (ZMod 11)) := by rw [pairKeys_eq]; simp
  have h3 : (3 : ZMod 11) ∈ (pairKeys : Set (ZMod 11)) := by rw [pairKeys_eq]; simp
  exact (show (0 : ZMod 11) ≠ 3 by decide) (hinj h0 h3 (by decide))

end Cslib.Algorithms.Lean
