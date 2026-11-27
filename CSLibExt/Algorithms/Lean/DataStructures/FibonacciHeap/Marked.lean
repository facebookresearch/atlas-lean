/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Marked Fibonacci heaps in the unit-cost handle model

An address denotes the same node across cuts and links. Lists describe the contents of circular
sibling lists, functions the fields at each address, and finite sets the live addresses and mark
bits. These are extensional descriptions, **not** a cost model for evaluating Lean lists, sets or
functions. Removing a given sibling uses its handle, splicing two root lists uses their headers,
and the length of a child list is maintained by a degree field. Key comparison, direct array-bin
access, and each such local pointer operation take bounded time. The live set specifies ownership;
it is not a dictionary searched or copied by the pointer algorithm.

Children are listed oldest link first. Losing a first child marks an attached parent; losing a
second child cuts it. A newly linked child, or a child promoted to a root, starts unmarked. This
is distinct from the unmarked persistent `FibonacciHeap` and its unconditional path cut. Only the
rose-tree semantics of `FibonacciTree` is reused, for viewing a handle's descendants.

See K. Wayne, *Fibonacci Heaps*, slides 9–13, 17, 19–36, 39–58, 60–65 and 72.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkedFibonacci

universe u

/-- A marked Fibonacci forest with a cached minimum **address**. The ownership set and address
fields describe a pointer heap; legal states are obtained by histories from the empty forest. -/
structure Heap (α : Type u) where
  live : Finset Nat
  key : Nat → α
  parent : Nat → Option Nat
  children : Nat → List Nat
  roots : List Nat
  marked : Finset Nat
  minimum : Option Nat

namespace Heap

variable {α : Type u}

/-- Empty handle heap. The dummy key supplies the total key field only at unused addresses. -/
def empty (dummy : α) : Heap α := ⟨∅, fun _ => dummy, fun _ => none, fun _ => [], [], ∅, none⟩

/-- The rank of an address is the number of its current children. -/
def rank (h : Heap α) (x : Nat) : Nat := (h.children x).length

/-- One credit per root and two per marked node, before scaling to primitive-cost units. -/
def potential (h : Heap α) : Nat := h.roots.length + 2 * h.marked.card

/-- A finite tree view rooted at an address expands exactly the child pointers at every node,
in link order. Its stored degrees are determined by the corresponding lists, not free labels. -/
inductive View (h : Heap α) : FibonacciTree Nat → Prop where
  | node {x : Nat} {cs : List (FibonacciTree Nat)}
      (fields : cs.map FibonacciTree.root = h.children x)
      (below : ∀ t ∈ cs, View h t) : View h (.node cs.length x cs)

private theorem mem_child_elements {cs : List (FibonacciTree Nat)} {c : FibonacciTree Nat}
    {y : Nat} (hc : c ∈ cs) (hy : y ∈ c.elements) : y ∈ (cs.map FibonacciTree.elements).sum := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    rw [List.map_cons, List.sum_cons, Multiset.mem_add]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl hy
    · exact Or.inr (ih hc)

-- Telescoping child-size lower bounds starting at zero-based position `i`.
private theorem fib_children (cs : List (FibonacciTree Nat)) (i : Nat)
    (sizes : ∀ (j : Nat) (hj : j < cs.length), Nat.fib (i + j + 1) ≤ cs[j].elements.card) :
    Nat.fib (i + cs.length + 2) ≤ Nat.fib (i + 2) + (cs.map FibonacciTree.elements).sum.card := by
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    have head := sizes 0 (by simp)
    have tail := ih (i + 1) fun j hj => by
      have h := sizes (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have fibStep : Nat.fib (i + 1 + 2) = Nat.fib (i + 1) + Nat.fib (i + 2) :=
      Nat.fib_add_two (n := i + 1)
    simp only [Nat.add_zero, List.getElem_cons_zero] at head
    simp only [List.length_cons, List.map_cons, List.sum_cons, Multiset.card_add]
    rw [show i + (cs.length + 1) + 2 = i + 1 + cs.length + 2 by omega]
    omega

/-- **Fibonacci subtree size from link order.** In a finite tree view, suppose that everywhere
in the subtree, the child at zero-based link position `i` has current rank at least `i - 1`.
Then the number of nodes in the view, counting its root, is at least Fibonacci number `k + 2`
for root rank `k`. The positional hypothesis, not heap order alone, drives this implication. -/
theorem View.fib_le_card {h : Heap α} {t : FibonacciTree Nat} (view : h.View t)
    (ordered : ∀ x ∈ t.elements, ∀ (i : Nat) (hi : i < (h.children x).length),
      i ≤ h.rank (h.children x)[i] + 1) : Nat.fib (h.rank t.root + 2) ≤ t.elements.card := by
  induction view with
  | @node x cs fields below ih =>
    have hlen : h.rank x = cs.length := by simp [rank, ← fields]
    have bound := fib_children cs 0 fun j hj => by
      have pos := ordered x (FibonacciTree.root_mem_elements _) j (by simpa [← fields] using hj)
      simp only [← fields, List.getElem_map] at pos
      have child := ih cs[j] (List.getElem_mem ..) fun y hy => ordered y (by
        rw [FibonacciTree.elements]
        exact Multiset.mem_cons_of_mem (mem_child_elements (List.getElem_mem ..) hy))
      exact (Nat.fib_mono (show 0 + j + 1 ≤ h.rank cs[j].root + 2 by omega)).trans child
    simpa [FibonacciTree.root, FibonacciTree.elements, hlen, Nat.add_comm] using bound

def cheaper [LinearOrder α] (key : Nat → α) : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => if key b < key a then some b else some a

/-- Allocate a singleton at a fresh handle, splice it into the roots, and compare cached minima.
Freshness is a precondition of the insertion step. -/
def insert [LinearOrder α] (h : Heap α) (x : Nat) (k : α) : Heap α :=
  let key' := Function.update h.key x k
  { h with live := Insert.insert x h.live, key := key', parent := Function.update h.parent x none,
           children := Function.update h.children x [], roots := x :: h.roots,
           minimum := cheaper key' h.minimum (some x) }

/-- Splice two disjoint heaps and compare their cached minima. Field selection denotes disjoint
union of already allocated storage, not an address-by-address copy. The history rule consumes
both inputs, including the work of creating each. -/
def meld [LinearOrder α] (h g : Heap α) : Heap α :=
  let key' := fun x => if x ∈ h.live then h.key x else g.key x
  ⟨h.live ∪ g.live, key', fun x => if x ∈ h.live then h.parent x else g.parent x,
    fun x => if x ∈ h.live then h.children x else g.children x, h.roots ++ g.roots,
    h.marked ∪ g.marked, cheaper key' h.minimum g.minimum⟩

/-- Melding adds the two potentials when the sets of marked handles are disjoint: no mark
changes and splicing adds the numbers of roots. -/
theorem potential_meld [LinearOrder α] (h g : Heap α) (sep : Disjoint h.marked g.marked) :
    (h.meld g).potential = h.potential + g.potential := by
  simp only [potential, meld, List.length_append, Finset.card_union_of_disjoint sep]
  omega

def cut (h : Heap α) (x p : Nat) : Heap α :=
  { h with roots := x :: h.roots, parent := Function.update h.parent x none,
           children := Function.update h.children p ((h.children p).erase x),
           marked := h.marked.erase x }

/-- After a child loss at `x`, stop at a root, mark an unmarked non-root, or cut a marked node
and continue at its old parent. The second output counts precisely these additional cuts. -/
def cascade (h : Heap α) (x : Nat) : Heap α × Nat :=
  match h.parent x with
  | none => (h, 0)
  | some p =>
    if _hm : x ∈ h.marked then
      let (h', c) := cascade (cut h x p) p
      (h', c + 1)
    else ({ h with marked := Insert.insert x h.marked }, 0)
termination_by h.marked.card
decreasing_by exact Finset.card_erase_lt_of_mem _hm

/-- Lower the key at a live handle. Only a strict parent-order violation initiates a cut and a
cascade. The cached minimum is updated by comparison, and the second output counts all cuts,
including the initiating one. The step rule requires that the new key not exceed the old. -/
def decrease [LinearOrder α] (h : Heap α) (x : Nat) (k : α) : Heap α × Nat :=
  let key' := Function.update h.key x k
  let s := { h with key := key', minimum := cheaper key' h.minimum (some x) }
  match h.parent x with
  | none => (s, 0)
  | some p =>
    if k < h.key p then
      let (h', c) := cascade (cut s x p) p
      (h', c + 1)
    else (s, 0)

def attach (h : Heap α) (winner loser : Nat) : Heap α :=
  { h with parent := Function.update h.parent loser (some winner),
           children := Function.update h.children winner (h.children winner ++ [loser]),
           marked := h.marked.erase loser }

-- Only called on a rank-bin collision. Both candidates have already left the input root list.
def link [LinearOrder α] (h : Heap α) (x y : Nat) : Heap α × Nat :=
  if h.key x ≤ h.key y then (attach h x y, x) else (attach h y x, y)

-- `slots` starts at the candidate's rank. An occupied slot is cleared, and exactly one link
-- carries to the next slot. The number in the result counts collisions, not a guessed bound.
def carry [LinearOrder α] (h : Heap α) (x : Nat) :
    List (Option Nat) → Heap α × List (Option Nat) × Nat
  | [] => (h, [some x], 0)
  | none :: more => (h, some x :: more, 0)
  | some y :: more =>
    let (h', z) := link h x y
    let (s, bins, c) := carry h' z more
    (s, none :: bins, c + 1)

def scan [LinearOrder α] (h : Heap α) (bins : List (Option Nat)) :
    List Nat → Heap α × List (Option Nat) × Nat
  | [] => (h, bins, 0)
  | x :: xs =>
    let d := h.rank x
    -- Split at a direct array index; materialise new empty bins only when extending the table.
    let prefixBins := bins.take d ++ List.replicate (d - bins.length) none
    let (s, suffixBins, c) := carry h x (bins.drop d)
    let (s', bins', c') := scan s (prefixBins ++ suffixBins) xs
    (s', bins', c + c')

/-- Remove the cached minimum, promote its children, and consolidate in rank-indexed bins. Work
counts header removal, one visit per promoted child, an input-root visit and final bin placement
per candidate, one collision probe and link per carry, bin initialisation and final scan over
the whole width (empty bins included), and one minimum comparison per surviving root. Empty
extraction performs just the header check. These are bounded-cost groups of pointer operations. -/
def extract [LinearOrder α] (h : Heap α) : Heap α × Nat :=
  match h.minimum with
  | none => (h, 1)
  | some x =>
    let cs := h.children x
    let pending := cs ++ h.roots.erase x
    let s := cs.foldl (fun a y => { a with parent := Function.update a.parent y none,
                                           marked := a.marked.erase y })
      { h with live := h.live.erase x, children := Function.update h.children x [],
               roots := [], minimum := none }
    let (s', bins, links) := scan s [] pending
    let rs := bins.filterMap id
    let out := { s' with roots := rs,
                         minimum := rs.foldl (fun m y => cheaper s'.key m (some y)) none }
    (out, 1 + cs.length + 2 * pending.length + 2 * links + 2 * bins.length + rs.length)

private theorem cut_potential (h : Heap α) (x p : Nat) :
    (cut h x p).potential ≤ h.potential + 1 := by
  have := Finset.card_le_card (Finset.erase_subset x h.marked)
  simp only [potential, cut, List.length_cons]
  omega

/-- The potential released by the previously marked nodes in a cascade pays one credit per
additional cut; at most two credits are needed to mark the non-root where it stops. -/
theorem cascade_potential (h : Heap α) (x : Nat) :
    (h.cascade x).2 + (h.cascade x).1.potential ≤ h.potential + 2 := by
  rw [cascade]
  split
  · simp
  · rename_i p hp
    split
    · rename_i hm
      have ih := cascade_potential (cut h x p) p
      have card := Finset.card_erase_add_one hm
      simp only [potential, cut, List.length_cons] at ih ⊢
      omega
    · rename_i hm
      simp [potential, Finset.card_insert_of_notMem hm]
      omega
termination_by h.marked.card
decreasing_by exact Finset.card_erase_lt_of_mem ‹x ∈ h.marked›

/-- Counting the initiating cut as well as cascading ones, a decrease with `c` cuts has
`c + Φ(after) ≤ Φ(before) + 4`, including when no cut takes place. This uses the actual
mark erasures in the cascade, independently of any rank bound. -/
theorem decrease_potential [LinearOrder α] (h : Heap α) (x : Nat) (k : α) :
    (h.decrease x k).2 + (h.decrease x k).1.potential ≤ h.potential + 4 := by
  unfold decrease
  dsimp only
  split
  · simp [potential]
  · split
    · rename_i p _ _
      let s : Heap α := { h with
        key := Function.update h.key x k
        minimum := cheaper (Function.update h.key x k) h.minimum (some x) }
      change ((s.cut x p).cascade p).2 + 1 + ((s.cut x p).cascade p).1.potential ≤ s.potential + 4
      have ih := cascade_potential (s.cut x p) p
      have hc := cut_potential s x p
      omega
    · simp [potential]

end Heap

/-- A request on one heap. Minimum queries and extractions record the observed key, or absence.
Meld has its own two-input history rule. -/
inductive Op (α : Type u) where
  | insert (address : Nat) (key : α)
  | decrease (address : Nat) (key : α)
  | findMin (observed : Option α)
  | extractMin (observed : Option α)

namespace Op

variable {α : Type u}

/-- How many insertions this single request contributes. -/
def insertions : Op α → Nat
  | .insert .. => 1
  | _ => 0

/-- The single-heap operations in Wayne's sequence theorem (slide 3). -/
def core : Op α → Bool
  | .findMin _ => false
  | _ => true

/-- The logarithmic allowance is only for extraction. Binary log rounds down; the additive one
covers empty and singleton heaps. -/
def allowance (op : Op α) (size : Nat) : Nat :=
  match op with
  | .extractMin _ => 1 + size.log2
  | _ => 1

end Op

variable {α : Type u}

/-- A legal single-heap transition with its primitive work. Insertion charges allocation, splice
and minimum update; find-min reads the cache. Decrease charges three fixed units for the key,
parent-order and cache work and two per cut (splice/unmark and cascade test). -/
inductive Step [LinearOrder α] : Heap α → Op α → Heap α → Nat → Prop where
  | insert (h : Heap α) (x : Nat) (k : α) (fresh : x ∉ h.live) :
      Step h (.insert x k) (h.insert x k) 3
  | decrease (h : Heap α) (x : Nat) (k : α) (live : x ∈ h.live) (lower : k ≤ h.key x) :
      Step h (.decrease x k) (h.decrease x k).1 (3 + 2 * (h.decrease x k).2)
  | findMin (h : Heap α) : Step h (.findMin (h.minimum.map h.key)) h 1
  | extractMin (h : Heap α) :
      Step h (.extractMin (h.minimum.map h.key)) h.extract.1 h.extract.2

/-- Histories from empty heaps indexed by the resulting heap, operations, insertions and actual
work. In core mode there is one linear chain and only insert, extract-min and decrease-key.
Extended mode permits cached queries and destructive meld: the two disjoint input histories
are both charged and neither input remains available in the output. -/
inductive History (extended : Bool) [LinearOrder α] : Heap α → Nat → Nat → Nat → Prop where
  | empty (dummy : α) : History extended (.empty dummy) 0 0 0
  | next {h h' : Heap α} {m n w c : Nat} {op : Op α}
      (past : History extended h m n w) (allowed : extended = true ∨ op.core = true)
      (step : Step h op h' c) : History extended h' (m + 1) (n + op.insertions) (w + c)
  | meld {h g : Heap α} {m n w m' n' w' : Nat} (allowed : extended = true)
      (left : History extended h m n w) (right : History extended g m' n' w')
      (separate : Disjoint h.live g.live) :
      History extended (h.meld g) (m + m' + 1) (n + n') (w + w' + 2)

end Cslib.Algorithms.Lean.MarkedFibonacci
