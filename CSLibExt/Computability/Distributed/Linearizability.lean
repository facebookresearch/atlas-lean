/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Linearizability and the projection direction of locality

A concurrent history is a list of completed operations (`OpRec`), each with the positions of its
invocation and response in the global event order. It is linearizable against a sequential
specification when some permutation of its operations respects the real-time order and is legal
for every object (`Linearizable`). `linearizable_project` proves the projection direction of
Herlihy and Wing's locality: the projection of a linearizable history onto one object is
linearizable, provided the empty sequence is legal for every object.

## References

* M. P. Herlihy and J. M. Wing, *Linearizability: a correctness condition for concurrent
  objects*, ACM Transactions on Programming Languages and Systems 12(3) (1990), 463–492.
-/

@[expose] public section

namespace Cslib.Distributed.Linearizability

/-- One completed operation in a concurrent history: object,
operation, argument, return value, and the positions `lo < hi`
of its invocation and response in the global event order
(positions are abstract; only their order matters). -/
structure OpRec where
  /-- The object the operation acts on. -/
  obj : ℕ
  /-- The operation. -/
  op : ℕ
  /-- The argument. -/
  arg : ℕ
  /-- The return value. -/
  ret : ℕ
  /-- The position of the invocation. -/
  lo : ℕ
  /-- The position of the response. -/
  hi : ℕ
  /-- The invocation precedes the response. -/
  lo_lt_hi : lo < hi
deriving DecidableEq, Repr

/-- A sequential specification: for each object, the set of
legal `(op, arg, ret)` sequences. -/
abbrev SeqSpec := ℕ → List (ℕ × ℕ × ℕ) → Prop

/-- A linearization respects the real-time order: no operation
responds before an earlier operation of `lin` is invoked. The
condition is on positions of `lin`, not on record values, so
repeated records are ordered occurrence by occurrence;
`respectsRT_iff` states it with indices. -/
def RespectsRT (lin : List OpRec) : Prop :=
  lin.Pairwise fun a b => ¬ b.hi < a.lo

/-- `RespectsRT` with indices: if the operation at position `i`
responds before the operation at position `j` is invoked, then
`i < j`. -/
theorem respectsRT_iff (lin : List OpRec) :
    RespectsRT lin ↔ ∀ (i j : ℕ) (hi : i < lin.length) (hj : j < lin.length),
      lin[i].hi < lin[j].lo → i < j := by
  rw [RespectsRT, List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact hlt
    · exact absurd (lt_trans lin[i].lo_lt_hi hij) (lt_irrefl _)
    · exact absurd hij (h j i hj hi hgt)
  · intro h i j hi hj hij hji
    exact absurd (h j i hj hi hji) (Nat.lt_asymm hij)

/-- The projection of a history onto one object. -/
def proj (H : List OpRec) (o : ℕ) : List OpRec :=
  H.filter (fun r => r.obj = o)

/-- `H` is linearizable against `spec`: some permutation of
its operations respects real-time order and is legal for
every object. -/
def Linearizable (spec : SeqSpec) (H : List OpRec) : Prop :=
  ∃ lin, List.Perm lin H ∧ RespectsRT lin ∧
    ∀ o, spec o ((lin.filter (fun r => r.obj = o)).map
      (fun r => (r.op, r.arg, r.ret)))

/-- Herlihy-Wing locality, projection direction: a
linearizable history projects to a linearizable history on
every object, provided the empty sequence is legal for
every object. (The converse, merging per-object
linearizations, remains open in roadmap package DPA-16.) -/
theorem linearizable_project (spec : SeqSpec)
    (hspec : ∀ o, spec o []) (H : List OpRec)
    (o : ℕ) (h : Linearizable spec H) :
    Linearizable spec (proj H o) := by
  obtain ⟨lin, hperm, hrt, hleg⟩ := h
  refine ⟨lin.filter (fun r => r.obj = o), ?_, ?_, ?_⟩
  · show List.Perm _ (proj H o)
    unfold proj
    exact hperm.filter _
  · exact hrt.filter _
  · intro o'
    by_cases heq : o' = o
    · subst o'
      have hff : (lin.filter (fun r => decide (r.obj = o))).filter
          (fun r => decide (r.obj = o)) =
          lin.filter (fun r => decide (r.obj = o)) := by
        rw [List.filter_filter]
        simp only [Bool.and_self]
      rw [hff]
      exact hleg o
    · have hempty : (lin.filter (fun r => decide (r.obj = o))).filter
          (fun r => decide (r.obj = o')) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        rw [List.mem_filter] at hx
        obtain ⟨hxmem, hqx⟩ := hx
        have hxo : x.obj = o :=
          of_decide_eq_true (List.mem_filter.mp hxmem).2
        have hxo' : x.obj = o' := of_decide_eq_true hqx
        rw [hxo] at hxo'
        exact heq hxo'.symm
      rw [hempty]
      simpa using hspec o'

end Cslib.Distributed.Linearizability
