/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.VanEmdeBoas
public meta import CSLibExt.Algorithms.Lean.DataStructures.VanEmdeBoas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Finset.Card

/-!
# Tests for the two-level van Emde Boas API

Client examples over the universe `Fin 16` (`m = 4`) exercise empty and
singleton trees, duplicate insertion, membership, the `Finset`
abstraction, validity preservation, and same-cluster versus
cross-cluster successor and predecessor queries. Concrete query results
are established through the public `*_eq_some_iff_of_valid` and
`*_eq_none_iff` characterizations.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.VanEmdeBoasTests

/-- Elements of the `m = 4` universe, written by their value. -/
private def el (n : Nat) (h : n < 16 := by decide) : Fin (4 * 4) :=
  ⟨n, h⟩

private theorem el_val (n : Nat) (h : n < 16) : (el n h).val = n :=
  rfl

/-- Stored set `{2, 3, 9, 14}`: `2, 3` share cluster `0`, while `9`
and `14` sit in clusters `2` and `3`. -/
private def sample : VanEmdeBoas 4 :=
  VanEmdeBoas.insert (el 14)
    (VanEmdeBoas.insert (el 9)
      (VanEmdeBoas.insert (el 3)
        (VanEmdeBoas.insert (el 2) VanEmdeBoas.empty)))

private theorem valid_sample : sample.Valid :=
  VanEmdeBoas.valid_insert _ _
    (VanEmdeBoas.valid_insert _ _
      (VanEmdeBoas.valid_insert _ _
        (VanEmdeBoas.valid_insert _ _ VanEmdeBoas.valid_empty)))

private theorem member_sample {y : Fin (4 * 4)} :
    sample.member y = true ↔ y.val = 2 ∨ y.val = 3 ∨ y.val = 9 ∨ y.val = 14 := by
  simp only [sample, VanEmdeBoas.member_insert, VanEmdeBoas.member_empty,
    Bool.false_eq_true, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> simp [el_val]
  · rintro (h | h | h | h) <;>
      [exact Or.inr (Or.inr (Or.inr (Fin.ext h)));
       exact Or.inr (Or.inr (Or.inl (Fin.ext h)));
       exact Or.inr (Or.inl (Fin.ext h));
       exact Or.inl (Fin.ext h)]

example (x : Fin (4 * 4)) :
    (VanEmdeBoas.empty : VanEmdeBoas 4).member x = false :=
  VanEmdeBoas.member_empty x

example : (VanEmdeBoas.empty : VanEmdeBoas 4).Valid :=
  VanEmdeBoas.valid_empty

example : (VanEmdeBoas.empty : VanEmdeBoas 4).contents = ∅ :=
  VanEmdeBoas.contents_empty

example : (VanEmdeBoas.empty : VanEmdeBoas 4).min? = none :=
  VanEmdeBoas.min?_empty

example : (VanEmdeBoas.empty : VanEmdeBoas 4).max? = none :=
  VanEmdeBoas.max?_empty

example (x : Fin (4 * 4)) :
    (VanEmdeBoas.empty : VanEmdeBoas 4).successor x = none :=
  VanEmdeBoas.successor_empty x

example (x : Fin (4 * 4)) :
    (VanEmdeBoas.empty : VanEmdeBoas 4).predecessor x = none :=
  VanEmdeBoas.predecessor_empty x

example :
    (VanEmdeBoas.insert (el 9) VanEmdeBoas.empty).member (el 9) = true :=
  VanEmdeBoas.member_insert_self _ _

example :
    (VanEmdeBoas.insert (el 9) VanEmdeBoas.empty).member (el 8) = false := by
  rw [VanEmdeBoas.member_insert_of_ne (by
    intro h
    have := congrArg Fin.val h
    simp [el_val] at this)]
  exact VanEmdeBoas.member_empty _

example : (VanEmdeBoas.insert (el 5) VanEmdeBoas.empty).min? = some (el 5) :=
  VanEmdeBoas.min?_insert_empty _

example : (VanEmdeBoas.insert (el 5) VanEmdeBoas.empty).max? = some (el 5) :=
  VanEmdeBoas.max?_insert_empty _

example : sample.member (el 2) = true :=
  member_sample.mpr (by simp [el_val])

example : sample.member (el 3) = true :=
  member_sample.mpr (by simp [el_val])

example : sample.member (el 9) = true :=
  member_sample.mpr (by simp [el_val])

example : sample.member (el 14) = true :=
  member_sample.mpr (by simp [el_val])

example : sample.member (el 0) = false := by
  cases h : sample.member (el 0) with
  | false => rfl
  | true =>
      have hm := member_sample.mp h
      simp [el_val] at hm

example : sample.member (el 4) = false := by
  cases h : sample.member (el 4) with
  | false => rfl
  | true =>
      have hm := member_sample.mp h
      simp [el_val] at hm

example : sample.member (el 15) = false := by
  cases h : sample.member (el 15) with
  | false => rfl
  | true =>
      have hm := member_sample.mp h
      simp [el_val] at hm

example : sample.contents = {el 2, el 3, el 9, el 14} := by
  ext y
  simp only [VanEmdeBoas.mem_contents, Finset.mem_insert, Finset.mem_singleton]
  rw [member_sample]
  constructor
  · rintro (h | h | h | h) <;>
      [exact Or.inl (Fin.ext h); exact Or.inr (Or.inl (Fin.ext h));
       exact Or.inr (Or.inr (Or.inl (Fin.ext h)));
       exact Or.inr (Or.inr (Or.inr (Fin.ext h)))]
  · rintro (rfl | rfl | rfl | rfl) <;> simp [el_val]

/-- Duplicate insertion does not change the abstraction. -/
example : (VanEmdeBoas.insert (el 9) sample).contents = sample.contents := by
  rw [VanEmdeBoas.contents_insert]
  exact Finset.insert_eq_of_mem
    (VanEmdeBoas.mem_contents.mpr (member_sample.mpr (by simp [el_val])))

example (x : Fin (4 * 4)) (t : VanEmdeBoas 4) (hv : t.Valid) :
    (VanEmdeBoas.insert x t).Valid :=
  VanEmdeBoas.valid_insert x t hv

example (t : VanEmdeBoas 4) (x y : Fin (4 * 4)) :
    (VanEmdeBoas.insert x t).member y = true ↔ y = x ∨ t.member y = true :=
  VanEmdeBoas.member_insert t x y

example (x : Fin (4 * 4)) (t : VanEmdeBoas 4) :
    (VanEmdeBoas.insert x t).contents = Insert.insert x t.contents :=
  VanEmdeBoas.contents_insert x t

example : sample.min? = some (el 2) := by
  rw [VanEmdeBoas.min?_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), fun y hy => ?_⟩
  rw [member_sample] at hy
  simp only [el_val]
  omega

example : sample.max? = some (el 14) := by
  rw [VanEmdeBoas.max?_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), fun y hy => ?_⟩
  rw [member_sample] at hy
  simp only [el_val]
  omega

/-- Same-cluster successor: `3` follows `2` inside cluster `0`. -/
example : sample.successor (el 2) = some (el 3) := by
  rw [VanEmdeBoas.successor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

/-- Cross-cluster successor: after `3` the search must consult the
summary and land on `9` in cluster `2`. -/
example : sample.successor (el 3) = some (el 9) := by
  rw [VanEmdeBoas.successor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.successor (el 9) = some (el 14) := by
  rw [VanEmdeBoas.successor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.successor (el 14) = none := by
  rw [VanEmdeBoas.successor_eq_none_iff valid_sample]
  intro z hz
  rw [member_sample] at hz
  simp only [el_val]
  omega

example : sample.successor (el 0) = some (el 2) := by
  rw [VanEmdeBoas.successor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.successor (el 4) = some (el 9) := by
  rw [VanEmdeBoas.successor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

/-- Same-cluster predecessor: `2` precedes `3` inside cluster `0`. -/
example : sample.predecessor (el 3) = some (el 2) := by
  rw [VanEmdeBoas.predecessor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

/-- Cross-cluster predecessor: before `9` the search must consult the
summary and land on `3` in cluster `0`. -/
example : sample.predecessor (el 9) = some (el 3) := by
  rw [VanEmdeBoas.predecessor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.predecessor (el 14) = some (el 9) := by
  rw [VanEmdeBoas.predecessor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.predecessor (el 2) = none := by
  rw [VanEmdeBoas.predecessor_eq_none_iff valid_sample]
  intro z hz
  rw [member_sample] at hz
  simp only [el_val]
  omega

example : sample.predecessor (el 15) = some (el 14) := by
  rw [VanEmdeBoas.predecessor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example : sample.predecessor (el 8) = some (el 3) := by
  rw [VanEmdeBoas.predecessor_eq_some_iff_of_valid valid_sample]
  refine ⟨member_sample.mpr (by simp [el_val]), by simp [el_val],
    fun z hz hxz => ?_⟩
  rw [member_sample] at hz
  simp only [el_val] at hxz ⊢
  omega

example {x y : Fin (4 * 4)} (h : sample.successor x = some y) :
    sample.member y = true ∧ x.val < y.val :=
  ⟨VanEmdeBoas.successor_mem h, VanEmdeBoas.successor_gt h⟩

example {x y : Fin (4 * 4)} (h : sample.predecessor x = some y) :
    sample.member y = true ∧ y.val < x.val :=
  ⟨VanEmdeBoas.predecessor_mem h, VanEmdeBoas.predecessor_lt h⟩

example {y : Fin (4 * 4)} (h : sample.min? = some y) :
    y ∈ sample.contents :=
  VanEmdeBoas.mem_contents.mpr (VanEmdeBoas.min?_mem h)

example {y : Fin (4 * 4)} (h : sample.max? = some y) :
    y ∈ sample.contents :=
  VanEmdeBoas.mem_contents.mpr (VanEmdeBoas.max?_mem h)

/-- Larger-universe runtime test (`m = 64`, universe `Fin 4096`): the
forward scans behind `min?` and `successor` must stay stack-safe when the
first set bit sits near the end of the scanned range. -/
private def largeSample : VanEmdeBoas 64 :=
  VanEmdeBoas.insert ⟨4095, by decide⟩
    (VanEmdeBoas.insert ⟨4000, by decide⟩ VanEmdeBoas.empty)

#guard largeSample.min?.map Fin.val = some 4000

#guard (largeSample.successor ⟨0, by decide⟩).map Fin.val = some 4000

#guard largeSample.successor ⟨4095, by decide⟩ = none

#check VanEmdeBoas.empty
#check VanEmdeBoas.insert
#check VanEmdeBoas.member
#check VanEmdeBoas.Valid
#check VanEmdeBoas.contents
#check VanEmdeBoas.min?
#check VanEmdeBoas.max?
#check VanEmdeBoas.successor
#check VanEmdeBoas.predecessor
#check VanEmdeBoas.member_insert
#check VanEmdeBoas.valid_insert
#check VanEmdeBoas.contents_insert
#check VanEmdeBoas.min?_eq_some_iff_of_valid
#check VanEmdeBoas.max?_eq_some_iff_of_valid
#check VanEmdeBoas.successor_eq_some_iff_of_valid
#check VanEmdeBoas.predecessor_eq_some_iff_of_valid

#print axioms VanEmdeBoas.member_empty
#print axioms VanEmdeBoas.member_insert
#print axioms VanEmdeBoas.valid_empty
#print axioms VanEmdeBoas.valid_insert
#print axioms VanEmdeBoas.mem_contents
#print axioms VanEmdeBoas.contents_insert
#print axioms VanEmdeBoas.min?_mem
#print axioms VanEmdeBoas.min?_least
#print axioms VanEmdeBoas.min?_eq_some_iff_of_valid
#print axioms VanEmdeBoas.max?_mem
#print axioms VanEmdeBoas.max?_greatest
#print axioms VanEmdeBoas.max?_eq_some_iff_of_valid
#print axioms VanEmdeBoas.successor_mem
#print axioms VanEmdeBoas.successor_gt
#print axioms VanEmdeBoas.successor_eq_some_iff_of_valid
#print axioms VanEmdeBoas.predecessor_mem
#print axioms VanEmdeBoas.predecessor_lt
#print axioms VanEmdeBoas.predecessor_eq_some_iff_of_valid

end Cslib.Algorithms.Lean.VanEmdeBoasTests
