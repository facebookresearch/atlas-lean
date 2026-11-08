/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.XFastTrie

/-!
# Tests for the x-fast trie (and y-fast skeleton) API

Client examples for `w = 0`, empty and duplicate insertion, prefix levels,
membership, successor/predecessor boundaries, and representative/bucket
validity through the public API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.XFastTrieTests

open Cslib.Algorithms.Lean

/-- Keys are `w = 3` bit numbers throughout, cast from literals. -/
public def k (n : Nat) : Fin (2 ^ 3) := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

public def t0 : XFastTrie 3 := XFastTrie.empty
public def t1 : XFastTrie 3 := t0.insert (k 2)
public def t2 : XFastTrie 3 := (t1.insert (k 5)).insert (k 2)

example : t0.contents = ∅ := rfl
example : t0.Valid := XFastTrie.valid_empty
example : t0.member (k 0) = false := rfl

/-- At `w = 0` there is a single key (`0 : Fin 1`); insertion stores it. -/
example : ((XFastTrie.empty : XFastTrie 0).insert 0).member 0 = true := by
  have hv := XFastTrie.valid_insert (XFastTrie.empty : XFastTrie 0)
    XFastTrie.valid_empty 0
  rw [XFastTrie.member_iff _ hv]
  simp [XFastTrie.contents_insert, XFastTrie.empty]

example : t1.Valid :=
  XFastTrie.valid_insert t0 XFastTrie.valid_empty _

/-- Duplicate insertion does not duplicate contents. -/
example : t2.contents = {k 5, k 2} := by
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty]

example : t2.Valid :=
  XFastTrie.valid_insert _ (XFastTrie.valid_insert _
    (XFastTrie.valid_insert t0 XFastTrie.valid_empty _) _) _

example : t2.member (k 5) = true := by
  have hv : t2.Valid :=
    XFastTrie.valid_insert _ (XFastTrie.valid_insert _
      (XFastTrie.valid_insert t0 XFastTrie.valid_empty _) _) _
  rw [XFastTrie.member_iff t2 hv]
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty]

example : t2.member (k 3) = false := by
  have hv : t2.Valid :=
    XFastTrie.valid_insert _ (XFastTrie.valid_insert _
      (XFastTrie.valid_insert t0 XFastTrie.valid_empty _) _) _
  have hnot : ¬ k 3 ∈ t2.contents := by
    simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty, k]
  exact Bool.eq_false_iff.mpr (fun h => hnot ((XFastTrie.member_iff t2 hv _).mp h))

/-- Prefix levels: the root prefix is `0`, full prefix is the key. -/
example : XFastTrie.prefixOf 0 (k 5) = 0 := XFastTrie.prefixOf_zero _
example : XFastTrie.prefixOf 3 (k 5) = 5 := XFastTrie.prefixOf_full _
example : XFastTrie.prefixOf 1 (k 5) = 1 := rfl
example : XFastTrie.prefixOf 2 (k 5) = 2 := rfl
example : XFastTrie.prefixOf 2 (k 5) < 2 ^ 2 :=
  XFastTrie.prefixOf_lt (by decide) _

/-- `hasPrefix` at level `1`: stored keys `2 = 010`, `5 = 101` cover both
top bits; a level-`3` probe for an absent key sharing no full key fails. -/
example : t2.hasPrefix 1 (k 7) = true := by
  have hv : t2.Valid :=
    XFastTrie.valid_insert _ (XFastTrie.valid_insert _
      (XFastTrie.valid_insert t0 XFastTrie.valid_empty _) _) _
  rw [XFastTrie.hasPrefix_iff t2 hv]
  exact ⟨k 5, by simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty], rfl⟩

/-- Successor/predecessor boundaries on `{2, 5}`. -/
example : t2.successor (k 2) = some (k 5) := by
  rw [XFastTrie.successor_eq_some_iff]
  refine ⟨by simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty],
    by decide, ?_⟩
  intro z hz hxz
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty] at hz
  rcases hz with rfl | rfl
  · exact le_refl _
  · exact absurd hxz (lt_irrefl _)

example : t2.successor (k 5) = none := by
  rw [XFastTrie.successor_eq_none_iff]
  intro z hz
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty] at hz
  rcases hz with rfl | rfl <;> simp [k]

example : t2.predecessor (k 5) = some (k 2) := by
  rw [XFastTrie.predecessor_eq_some_iff]
  refine ⟨by simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty],
    by decide, ?_⟩
  intro z hz hzx
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty] at hz
  rcases hz with rfl | rfl
  · exact absurd hzx (lt_irrefl _)
  · exact le_refl _

example : t2.predecessor (k 0) = none := by
  rw [XFastTrie.predecessor_eq_none_iff]
  intro z hz
  simp [t2, t1, t0, XFastTrie.contents_insert, XFastTrie.empty] at hz
  rcases hz with rfl | rfl <;> simp [k]

/-- Successor on the empty trie is `none`. -/
example : t0.successor (k 0) = none := by
  rw [XFastTrie.successor_eq_none_iff]
  simp [t0, XFastTrie.empty]

/-- A y-fast skeleton with one representative bucket. -/
public def y1 : YFastTrie 3 where
  reps := (XFastTrie.empty : XFastTrie 3).insert (k 5)
  buckets := fun r => if r = k 5 then {k 3, k 5} else ∅

example : y1.contents = {k 3, k 5} := by
  rw [YFastTrie.contents, y1]
  simp [XFastTrie.contents_insert, XFastTrie.empty]

example : y1.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · exact XFastTrie.valid_insert _ XFastTrie.valid_empty _
  · intro r
    by_cases hr : r = k 5
    · subst hr
      simp [y1, XFastTrie.contents_insert, XFastTrie.empty]
    · have hmem : r ∉ y1.reps.contents := by
        simp [y1, XFastTrie.contents_insert, XFastTrie.empty]
        exact fun h => hr h
      have hbucket : y1.buckets r = ∅ := by simp [y1, hr]
      simp [hmem, hbucket]
  · intro r hr
    have hr5 : r = k 5 := by
      simpa [y1, XFastTrie.contents_insert, XFastTrie.empty] using hr
    subst hr5
    simp [y1]

example : (k 3) ∈ y1.contents ↔ ∃ r, k 3 ∈ y1.buckets r :=
  YFastTrie.mem_contents_iff_exists_of_valid (by
    refine ⟨?_, ?_, ?_⟩
    · exact XFastTrie.valid_insert _ XFastTrie.valid_empty _
    · intro r
      by_cases hr : r = k 5
      · subst hr
        simp [y1, XFastTrie.contents_insert, XFastTrie.empty]
      · have hmem : r ∉ y1.reps.contents := by
          simp [y1, XFastTrie.contents_insert, XFastTrie.empty]
          exact fun h => hr h
        have hbucket : y1.buckets r = ∅ := by simp [y1, hr]
        simp [hmem, hbucket]
    · intro r hr
      have hr5 : r = k 5 := by
        simpa [y1, XFastTrie.contents_insert, XFastTrie.empty] using hr
      subst hr5
      simp [y1]) _

/-- Insertion membership needs no validity hypothesis, even for a trie
whose levels are inconsistent with its contents. -/
example (t : XFastTrie 3) (x : Fin (2 ^ 3)) : (t.insert x).member x = true :=
  XFastTrie.member_insert_self t x

/-- Regression: a representative that is not itself stored is invalid,
even though it owns a nonempty bucket. -/
public def yBad : YFastTrie 3 where
  reps := (XFastTrie.empty : XFastTrie 3).insert (k 0)
  buckets := fun r => if r = k 0 then {k 1} else ∅

example : yBad.contents = {k 1} := by
  rw [YFastTrie.contents, yBad]
  simp [XFastTrie.contents_insert, XFastTrie.empty]

example : ¬ yBad.Valid := by
  intro h
  have hmem : k 0 ∈ yBad.reps.contents := by
    simp [yBad, XFastTrie.contents_insert, XFastTrie.empty]
  have hself := h.2.2 _ hmem
  simp [yBad, k] at hself

example {t : YFastTrie 3} (hv : t.Valid) {r : Fin (2 ^ 3)}
    (hr : r ∈ t.reps.contents) : r ∈ t.contents :=
  YFastTrie.rep_mem_contents_of_valid hv hr

#print axioms XFastTrie.member_iff
#print axioms XFastTrie.successor_eq_some_iff
#print axioms YFastTrie.mem_contents_iff_exists_of_valid

end Cslib.Algorithms.Lean.XFastTrieTests
