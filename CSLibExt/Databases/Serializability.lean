/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.TopologicalSort
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.NodupEquivFin

/-!
# Conflict serializability

Transactions are numbered `0, …, n - 1` (`Fin n`) and access data items of type `X`. A schedule
is a list of operations `Op n X`: a read or a write of an item by a transaction, labelled by an
occurrence identifier `step`. As in Bernstein, Hadzilacos and Goodman, operations are distinct
occurrences: the identifier distinguishes repeated accesses of a transaction to an item, and the
serializability results assume that a schedule lists each operation once (`List.Nodup`). The order
of a transaction's operations in the schedule is its program order; the identifiers carry no order.
That `a` occurs before `b` in a schedule `s` is written `[a, b] <+ s`.

* Two operations **conflict** (`Op.Conflicts`) when they belong to different transactions, access
  the same item, and at least one of them is a write.
* Schedules `s` and `s'` are **conflict-equivalent** (`ConflictEquiv`) when `s'` is a permutation
  of `s` that keeps the relative order of every pair of conflicting operations and of every pair
  of operations of the same transaction.
* A schedule is **serial** (`IsSerial`) when, for any two transactions, all operations of one
  precede all operations of the other; it is **conflict-serializable** (`ConflictSerializable`)
  when it is conflict-equivalent to a serial schedule.
* The **precedence graph** (`precedenceGraph`, on the vertices `Fin n`) has an edge `i → j` when
  an operation of `i` precedes a conflicting operation of `j` (`PrecedenceEdge`).

`conflictSerializable_iff_isAcyclic` is the **serializability theorem**: a schedule is
conflict-serializable exactly when its precedence graph is acyclic, in the sense of
`TopologicalSort.IsAcyclic` from CSLibExt's graph library. The serial schedule is constructive:
`serialize order s` stably sorts `s` by the position of each operation's transaction in `order`,
and `isSerial_serialize` and `conflictEquiv_serialize` show it is a conflict-equivalent serial
schedule whenever `order` is a topological order of the precedence graph, such as the one computed
by `TopologicalSort.sort`. `conflictSerializable_of_rank`: a schedule is conflict-serializable
when some numeric rank of the transactions increases along every edge of its precedence graph;
the two-phase locking theorem uses it.

## References

* P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database
  Systems*, Addison-Wesley, 1987, Chapter 2 (the serializability theorem).
* C. H. Papadimitriou, *The Theory of Database Concurrency Control*, Computer Science Press,
  1986.
-/

@[expose] public section

namespace Cslib.Databases

open Cslib.Algorithms.Lean
open scoped List

/-- Whether an operation reads or writes its item. -/
inductive Access
  /-- A read. -/
  | read
  /-- A write. -/
  | write
deriving DecidableEq

/-- An operation of a schedule: transaction `txn` reads or writes item `item`; `step` identifies the
occurrence among the operations of the transaction. -/
structure Op (n : ℕ) (X : Type*) where
  /-- The transaction performing the operation. -/
  txn : Fin n
  /-- An identifier of the occurrence (for instance its position in the transaction), which makes
  repeated accesses of a transaction to an item distinct operations. -/
  step : ℕ
  /-- Read or write. -/
  access : Access
  /-- The data item accessed. -/
  item : X
deriving DecidableEq

variable {n : ℕ} {X : Type*}

namespace Op

/-- Two operations conflict: different transactions access the same item, and at least one of the
accesses is a write. -/
def Conflicts (a b : Op n X) : Prop :=
  a.txn ≠ b.txn ∧ a.item = b.item ∧ (a.access = .write ∨ b.access = .write)

instance [DecidableEq X] (a b : Op n X) : Decidable (a.Conflicts b) := by
  unfold Conflicts
  infer_instance

theorem Conflicts.symm {a b : Op n X} (h : a.Conflicts b) : b.Conflicts a :=
  ⟨fun h' => h.1 h'.symm, h.2.1.symm, h.2.2.symm⟩

/-- The pairs whose relative order a conflict-equivalent schedule must keep: operations of the
same transaction, and conflicting operations. -/
def OrderMatters (a b : Op n X) : Prop := a.txn = b.txn ∨ a.Conflicts b

theorem OrderMatters.symm {a b : Op n X} (h : a.OrderMatters b) : b.OrderMatters a :=
  h.imp Eq.symm Conflicts.symm

end Op

variable [DecidableEq X]

/-- `s'` is conflict-equivalent to `s`: a permutation of `s` that keeps the relative order of
every pair of conflicting operations and of every pair of operations of one transaction. -/
def ConflictEquiv (s s' : List (Op n X)) : Prop :=
  s.Perm s' ∧ ∀ a b, a.OrderMatters b → ([a, b] <+ s ↔ [a, b] <+ s')

/-- Every operation of transaction `i` precedes every operation of transaction `j` in `s`. -/
def TxnBefore (s : List (Op n X)) (i j : Fin n) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a.txn = i → b.txn = j → [a, b] <+ s

/-- A serial schedule: for any two transactions, all operations of one precede all operations of
the other. -/
def IsSerial (s : List (Op n X)) : Prop := ∀ i j, i ≠ j → TxnBefore s i j ∨ TxnBefore s j i

instance (s : List (Op n X)) (i j : Fin n) : Decidable (TxnBefore s i j) := by
  unfold TxnBefore
  infer_instance

instance (s : List (Op n X)) : Decidable (IsSerial s) := by
  unfold IsSerial
  infer_instance

/-- A conflict-serializable schedule: conflict-equivalent to a serial schedule. -/
def ConflictSerializable (s : List (Op n X)) : Prop := ∃ s', IsSerial s' ∧ ConflictEquiv s s'

/-- An edge `i → j` of the precedence graph: an operation of `i` precedes a conflicting operation
of `j`. -/
def PrecedenceEdge (s : List (Op n X)) (i j : Fin n) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, a.txn = i ∧ b.txn = j ∧ a.Conflicts b ∧ [a, b] <+ s

instance (s : List (Op n X)) (i j : Fin n) : Decidable (PrecedenceEdge s i j) := by
  unfold PrecedenceEdge
  infer_instance

/-- The precedence (serialization) graph of a schedule, on the transactions `Fin n`. -/
def precedenceGraph (s : List (Op n X)) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency i := (List.finRange n).filter fun j => decide (PrecedenceEdge s i j)

theorem edge_precedenceGraph {s : List (Op n X)} {i j : Fin n} :
    (precedenceGraph s).Edge i j ↔ PrecedenceEdge s i j := by
  simp [precedenceGraph, DirectedAdjacency.Edge, List.mem_filter, List.mem_finRange]

/-- The serial schedule for the transaction order `order`: the operations of `s`, stably sorted by
the position of their transaction in `order`. -/
def serialize (order : List (Fin n)) (s : List (Op n X)) : List (Op n X) :=
  s.insertionSort fun a b => order.idxOf a.txn ≤ order.idxOf b.txn

/-! ### Order facts about duplicate-free lists -/

private theorem pair_sublist_total {α : Type*} {a b : α} :
    ∀ {l : List α}, a ∈ l → b ∈ l → a ≠ b → [a, b] <+ l ∨ [b, a] <+ l
  | [], ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, ha, hb, hab => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      exact Or.inl (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hb'))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr ha'))
      · rcases pair_sublist_total ha' hb' hab with h | h
        · exact Or.inl (List.sublist_cons_of_sublist c h)
        · exact Or.inr (List.sublist_cons_of_sublist c h)

private theorem not_pair_sublist_both {α : Type*} {a b : α} :
    ∀ {l : List α}, l.Nodup → [a, b] <+ l → [b, a] <+ l → False
  | [], _, h, _ => by simp at h
  | c :: l, hnd, h₁, h₂ => by
    have hc : c ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.sublist_cons_iff] at h₁ h₂
    rcases h₁ with h₁ | ⟨r, hr, h₁⟩
    · rcases h₂ with h₂ | ⟨r', hr', h₂⟩
      · exact not_pair_sublist_both (List.nodup_cons.mp hnd).2 h₁ h₂
      · simp only [List.cons.injEq] at hr'
        obtain ⟨rfl, rfl⟩ := hr'
        exact hc (h₁.subset (by simp))
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rcases h₂ with h₂ | ⟨r', hr', -⟩
      · exact hc (h₂.subset (by simp))
      · simp only [List.cons.injEq] at hr'
        obtain ⟨rfl, rfl⟩ := hr'
        exact hc (List.singleton_sublist.mp h₁)

private theorem exists_lt_of_pair_sublist {α : Type*} {a b : α} {l : List α} (h : [a, b] <+ l) :
    ∃ i j : ℕ, i < j ∧ l[i]? = some a ∧ l[j]? = some b := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp h
  exact ⟨f 0, f 1, f.strictMono Nat.zero_lt_one, by simpa using (hf 0).symm,
    by simpa using (hf 1).symm⟩

/-- A directed graph whose edges strictly increase a numeric rank is acyclic. -/
private theorem isAcyclic_of_rank {V : Type*} (g : DirectedAdjacency V) (rank : V → ℕ)
    (h : ∀ u v, g.Edge u v → rank u < rank v) : TopologicalSort.IsAcyclic g := by
  rintro ⟨cycle, hc⟩
  obtain ⟨hne, -, hchain, hclose, -⟩ :=
    (TopologicalSort.directedCycleIn_iff g g.vertices cycle).1 hc
  have hrankchain : cycle.IsChain (fun u v => rank u < rank v) :=
    hchain.imp (fun _ _ hedge => h _ _ hedge)
  have hrankclose : rank (cycle.getLast hne) < rank (cycle.head hne) := h _ _ hclose
  cases cycle with
  | nil => contradiction
  | cons x xs =>
    cases xs with
    | nil => simp at hrankclose
    | cons y ys =>
      have hfirstlast : rank x < rank ((x :: y :: ys).getLast (by simp)) := by
        apply hrankchain.rel_cons
        simp
      simp only [List.head_cons] at hrankclose
      omega

/-! ### The serializability theorem -/

/-- A conflict-serializable schedule has an acyclic precedence graph: the position of the first
operation of each transaction in the serial schedule increases along every edge. -/
theorem ConflictSerializable.isAcyclic {s : List (Op n X)} (hs : s.Nodup)
    (h : ConflictSerializable s) : TopologicalSort.IsAcyclic (precedenceGraph s) := by
  obtain ⟨s', hser, hperm, hord⟩ := h
  have hs' : s'.Nodup := hperm.nodup_iff.mp hs
  refine isAcyclic_of_rank _ (fun i => s'.findIdx fun c => decide (c.txn = i)) ?_
  intro i j hedge
  obtain ⟨a, ha, b, hb, rfl, rfl, hab, hsub⟩ := edge_precedenceGraph.mp hedge
  have hsub' : [a, b] <+ s' := (hord a b (Or.inr hab)).mp hsub
  have ha' : a ∈ s' := hperm.subset ha
  have hb' : b ∈ s' := hperm.subset hb
  have hbefore : TxnBefore s' a.txn b.txn := by
    rcases hser a.txn b.txn hab.1 with h | h
    · exact h
    · exact absurd (h b hb' a ha' rfl rfl) fun h' => not_pair_sublist_both hs' hsub' h'
  have hlt : (s'.findIdx fun c => decide (c.txn = b.txn)) < s'.length :=
    List.findIdx_lt_length_of_exists ⟨b, hb', by simp⟩
  have hck : (s'[s'.findIdx fun c => decide (c.txn = b.txn)]).txn = b.txn := by
    simpa using List.findIdx_getElem (w := hlt)
  obtain ⟨ia, ic, hiac, hia, hic⟩ :=
    exists_lt_of_pair_sublist (hbefore a ha' _ (List.getElem_mem hlt) rfl hck)
  obtain ⟨hicl, hic⟩ := List.getElem?_eq_some_iff.mp hic
  have hick : ic = s'.findIdx fun c => decide (c.txn = b.txn) := (hs'.getElem_inj_iff).mp hic
  obtain ⟨hial, hia⟩ := List.getElem?_eq_some_iff.mp hia
  have hka : (s'.findIdx fun c => decide (c.txn = a.txn)) ≤ ia := by
    by_contra hlt'
    have := List.not_of_lt_findIdx (Nat.lt_of_not_le hlt')
    simp [hia] at this
  change (s'.findIdx fun c => decide (c.txn = a.txn)) < s'.findIdx fun c => decide (c.txn = b.txn)
  omega

omit [DecidableEq X] in
/-- The schedule `serialize order s` is serial when `order` lists every transaction. -/
theorem isSerial_serialize (s : List (Op n X)) {order : List (Fin n)}
    (hocomp : ∀ i, i ∈ order) : IsSerial (serialize order s) := by
  have : Std.Total fun a b : Op n X => order.idxOf a.txn ≤ order.idxOf b.txn :=
    ⟨fun _ _ => le_total _ _⟩
  have : IsTrans (Op n X) fun a b => order.idxOf a.txn ≤ order.idxOf b.txn :=
    ⟨fun _ _ _ => le_trans⟩
  have hsorted := List.pairwise_insertionSort
    (fun a b : Op n X => order.idxOf a.txn ≤ order.idxOf b.txn) s
  have hpos : ∀ i j : Fin n, order.idxOf i < order.idxOf j → TxnBefore (serialize order s) i j := by
    intro i j hij a ha b hb hai hbj
    have hab : a ≠ b := by
      rintro rfl
      rw [← hai, ← hbj] at hij
      exact lt_irrefl _ hij
    rcases pair_sublist_total ha hb hab with h | h
    · exact h
    · have := List.pairwise_pair.mp (hsorted.sublist h)
      rw [hai, hbj] at this
      omega
  intro i j hij
  have hne : order.idxOf i ≠ order.idxOf j := fun h => hij ((List.idxOf_inj (hocomp i)).mp h)
  rcases lt_or_gt_of_ne hne with h | h
  exacts [Or.inl (hpos i j h), Or.inr (hpos j i h)]

/-- The schedule `serialize order s` is conflict-equivalent to `s` when `order` is a topological
order of the precedence graph of `s`. -/
theorem conflictEquiv_serialize {s : List (Op n X)} (hs : s.Nodup) {order : List (Fin n)}
    (horder : TopologicalSort.IsTopologicalOrder (precedenceGraph s) order) :
    ConflictEquiv s (serialize order s) := by
  obtain ⟨-, -, hofwd⟩ := horder
  have hperm : s.Perm (serialize order s) := (List.perm_insertionSort _ s).symm
  have hs' := hperm.nodup_iff.mp hs
  have hmono : ∀ a b, a.OrderMatters b → [a, b] <+ s → [a, b] <+ serialize order s := by
    rintro a b (h | h) hsub
    · exact List.pair_sublist_insertionSort (by rw [h]) hsub
    · refine List.pair_sublist_insertionSort (le_of_lt (hofwd a.txn b.txn ?_)) hsub
      exact edge_precedenceGraph.mpr ⟨a, hsub.subset (by simp), b, hsub.subset (by simp), rfl,
        rfl, h, hsub⟩
  refine ⟨hperm, fun a b hab => ⟨hmono a b hab, fun h' => ?_⟩⟩
  have ha : a ∈ s := hperm.symm.subset (h'.subset (by simp))
  have hb : b ∈ s := hperm.symm.subset (h'.subset (by simp))
  have hne : a ≠ b := by
    rintro rfl
    exact not_pair_sublist_both hs' h' h'
  rcases pair_sublist_total ha hb hne with h | h
  · exact h
  · exact absurd (hmono b a hab.symm h) fun h'' => not_pair_sublist_both hs' h' h''

/-- **The serializability theorem**: a schedule without duplicate operations is
conflict-serializable exactly when its precedence graph is acyclic. -/
theorem conflictSerializable_iff_isAcyclic {s : List (Op n X)} (hs : s.Nodup) :
    ConflictSerializable s ↔ TopologicalSort.IsAcyclic (precedenceGraph s) := by
  refine ⟨ConflictSerializable.isAcyclic hs, fun h => ?_⟩
  obtain ⟨order, horder⟩ := TopologicalSort.acyclic_implies_success _ h
  have htopo := TopologicalSort.success_isTopologicalOrder _ _ horder
  exact ⟨_, isSerial_serialize s fun i => (htopo.2.1 i).mpr (List.mem_finRange i),
    conflictEquiv_serialize hs htopo⟩

omit [DecidableEq X] in
/-- A schedule whose precedence graph increases a numeric rank of the transactions is
conflict-serializable. -/
theorem conflictSerializable_of_rank {s : List (Op n X)} (hs : s.Nodup) (rank : Fin n → ℕ)
    (h : ∀ i j, PrecedenceEdge s i j → rank i < rank j) : ConflictSerializable s := by
  classical
  exact (conflictSerializable_iff_isAcyclic hs).mpr
    (isAcyclic_of_rank _ rank fun i j hij => h i j (edge_precedenceGraph.mp hij))

end Cslib.Databases
