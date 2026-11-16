/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Testing.BoundedExhaustive

/-!
# Bounded-exhaustive tests

Unary-term instance exercising the bounded-exhaustive theorems: positive,
boundary, and discriminating negative checks. A passing bounded check here is
a proof only relative to the stated bound and exact support; it says nothing
about terms above the bound.
-/

namespace CSLibExtTest.Testing.BoundedExhaustiveTests

open CSLibExt.Testing.BoundedExhaustive

/-- Unary terms: `Z` is zero, `S t` is successor. -/
inductive UTerm where
  | Z : UTerm
  | S : UTerm → UTerm

/-- Size of a unary term: number of `S` constructors. -/
def usize : UTerm → Nat
  | .Z => 0
  | .S t => usize t + 1

/-- Canonical term of a given size. -/
def termOfNat : Nat → UTerm
  | 0 => .Z
  | k + 1 => .S (termOfNat k)

theorem usize_termOfNat (k : Nat) : usize (termOfNat k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [termOfNat, usize, ih]

#print axioms usize_termOfNat

theorem termOfNat_usize (t : UTerm) : termOfNat (usize t) = t := by
  induction t with
  | Z => rfl
  | S t ih => simp only [usize, termOfNat, ih]

#print axioms termOfNat_usize

/-- Bounded enumeration of unary terms: all terms of size at most `n`. -/
def uenum : Nat → List UTerm := fun n => (List.range (n + 1)).map termOfNat

/-- Exact support for `uenum`, proved from `usize_termOfNat`,
`termOfNat_usize`, `List.mem_map`, and `List.mem_range` (not definitional). -/
theorem uenum_exact (n : Nat) (t : UTerm) : t ∈ uenum n ↔ usize t ≤ n := by
  unfold uenum
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [List.mem_range] at hk
    rw [usize_termOfNat]
    omega
  · intro hle
    refine ⟨usize t, ?_, termOfNat_usize t⟩
    rw [List.mem_range]
    omega

#print axioms uenum_exact

/-- Predicate: size at most 2. -/
def p1 : UTerm → Bool := fun t => decide (usize t ≤ 2)

#guard (uenum 2).all p1 = true
#guard (uenum 3).all p1 = false

theorem u1_all_true : (uenum 2).all p1 = true := rfl

#print axioms u1_all_true

theorem u1_all_false : (uenum 3).all p1 = false := rfl

#print axioms u1_all_false

/-- Bounded validity at bound 2, via B1. -/
theorem u1_valid : ∀ t, usize t ≤ 2 → p1 t = true :=
  (all_iff_forall_le p1 2 (uenum_exact 2)).mp u1_all_true

#print axioms u1_valid

/-- No bounded validity at bound 3, via B1 (witness: size-3 term). -/
theorem u1_not_valid3 : ¬ ∀ t, usize t ≤ 3 → p1 t = true := by
  intro h
  have hall := (all_iff_forall_le p1 3 (uenum_exact 3)).mpr h
  rw [u1_all_false] at hall
  contradiction

#print axioms u1_not_valid3

/-- Broken enumerator omitting the size-1 term. This enumerator lacks bounded
completeness at bound 1, so B1/B2 do not apply. -/
def badOmit : Nat → List UTerm := fun _ => [UTerm.Z]

/-- Predicate: size is not 1. -/
def p2 : UTerm → Bool := fun t => decide (usize t ≠ 1)

#guard (badOmit 1).all p2 = true

/-- Passing does not imply bounded validity (witness: size-1 term). -/
theorem u2_not_valid : ¬ ∀ t, usize t ≤ 1 → p2 t = true := by
  intro h
  have hle : usize (UTerm.S UTerm.Z) ≤ 1 := Nat.le_refl 1
  have h1 := h (UTerm.S UTerm.Z) hle
  have h_contra : p2 (UTerm.S UTerm.Z) = false := rfl
  rw [h_contra] at h1
  contradiction

#print axioms u2_not_valid

/-- Broken enumerator including a size-2 term at every bound. Support
soundness fails at bound 1 (a size-2 element is enumerated), so validity need
not imply passing. -/
def badExtra : Nat → List UTerm :=
  fun _ => [UTerm.Z, UTerm.S UTerm.Z, UTerm.S (UTerm.S UTerm.Z)]

/-- Predicate: size at most 1. -/
def p3 : UTerm → Bool := fun t => decide (usize t ≤ 1)

/-- Bounded validity holds at bound 1. -/
theorem u3_valid : ∀ t, usize t ≤ 1 → p3 t = true := by
  intro t hle
  exact decide_eq_true hle

#print axioms u3_valid

#guard (badExtra 1).all p3 = false

/-- The pair of two size-1 terms is not emitted at bound 1. -/
theorem u4_not_mem :
    (termOfNat 1, termOfNat 1) ∉ enumProd usize uenum uenum 1 := by
  rw [mem_enumProd_iff uenum_exact uenum_exact]
  simp [usize_termOfNat]

#print axioms u4_not_mem

/-- Pairs within budget are emitted. -/
theorem u4_mem_01 :
    (termOfNat 0, termOfNat 1) ∈ enumProd usize uenum uenum 1 := by
  rw [mem_enumProd_iff uenum_exact uenum_exact]
  simp [usize_termOfNat]

#print axioms u4_mem_01

theorem u4_mem_10 :
    (termOfNat 1, termOfNat 0) ∈ enumProd usize uenum uenum 1 := by
  rw [mem_enumProd_iff uenum_exact uenum_exact]
  simp [usize_termOfNat]

#print axioms u4_mem_10

#guard ((enumProd usize uenum uenum 1).map (fun q => (usize q.1, usize q.2))) =
  [(0, 0), (0, 1), (1, 0)]

#print axioms CSLibExt.Testing.BoundedExhaustive.all_iff_forall_le

#print axioms CSLibExt.Testing.BoundedExhaustive.forall_le_of_all

#print axioms CSLibExt.Testing.BoundedExhaustive.mem_of_mem_le

#print axioms CSLibExt.Testing.BoundedExhaustive.enumProd

#print axioms CSLibExt.Testing.BoundedExhaustive.mem_enumProd_iff

end CSLibExtTest.Testing.BoundedExhaustiveTests
