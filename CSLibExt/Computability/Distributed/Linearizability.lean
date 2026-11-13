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

/-- `a` occurs before `b` in the list `L`. -/
def Before (L : List OpRec) (a b : OpRec) : Prop :=
  ∃ l₁ l₂ l₃, L = l₁ ++ a :: l₂ ++ b :: l₃

/-- A linearization respects the real-time order: if `a`'s
response precedes `b`'s invocation in the history, `a` comes
first. -/
def RespectsRT (lin : List OpRec) : Prop :=
  ∀ a ∈ lin, ∀ b ∈ lin, a.hi < b.lo → Before lin a b

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
  · intro a ha b hb hlt
    have hao : a.obj = o := of_decide_eq_true (List.mem_filter.mp ha).2
    have hbo : b.obj = o := of_decide_eq_true (List.mem_filter.mp hb).2
    have haL : a ∈ lin := List.mem_of_mem_filter ha
    have hbL : b ∈ lin := List.mem_of_mem_filter hb
    obtain ⟨l₁, l₂, l₃, rfl⟩ := hrt a haL b hbL hlt
    exact ⟨l₁.filter (fun r => r.obj = o), l₂.filter (fun r => r.obj = o),
      l₃.filter (fun r => r.obj = o), by
      simp [List.filter_append, hao, hbo]⟩
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
