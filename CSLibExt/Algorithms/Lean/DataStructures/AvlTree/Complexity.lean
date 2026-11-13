/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Delete
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Fib.Basic

/-!
# AVL height and operation counts

The Fibonacci bound gives logarithmic height for balanced trees with correct caches.
The counted operations mirror the existing AVL definitions, including the two separate
successor traversals in deletion. Their return values equal the existing functions.

The unit operations are key comparisons (`<`), visits to nonempty nodes in recursive
traversals, inspection of nonempty heavy children/grandchildren in rebalancing, and
node rebuilds (`mkNode`). Every executed unit has its own tick. Cached height reads,
height comparisons and arithmetic, pattern discrimination, bindings, projections,
recursive calls themselves, and returning existing subtrees are free. A traversal visit
is entry into its nonempty recursion equation; empty cases cost zero. Repeated visits
in separate traversals are charged separately. Each actual `mkNode` costs one, so a
rotation charges all of its rebuilds. Local rebuilds have constant count in this model
because cached-height reads and arithmetic are free.
These are operation counts, not CPU time or FinTM2/Turing complexity.

## Provenance and scope

Adapted from the `avl-height-complexity` bank in `fairinternal/formal-math`,
commit `1dda058818107a00c5aa4bc928e7d8fb1f584027`, original module blob
`82a2fd2a79b2928e60f586ac6ca408eb189370a5` (Lean 4.34.1). Its Git trailer credits
Codex `gpt-6.1-sol[1m]`, agentcloud session `004703a6-d776-4368-93bd-c52802f3ba6e`;
that is preserved declared provenance, not independent runtime attestation.
This scoped Lean 4.35 adaptation retains the floor base-2 logarithmic height and counted-operation
API over the current AVL implementation. The optional golden-ratio power and real-logarithm
results from that bank are omitted; this is not a verbatim or full-bank import.
`Valid` in the current parent module includes `CacheCorrect`: its second and third
conjuncts supply the two premises of the logarithmic bounds. Erasure lets clients reuse
`valid_insert`, `valid_delete`, and the existing membership and inorder theorems directly.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean.AvlTree

variable {α : Type u}

/-- The number of keys, ignoring height caches. -/
public def size (t : Tree α) : Nat := (toBinaryTree t).numNodes

/-- The empty tree has no keys. -/
@[simp] public theorem size_empty : size (.empty : Tree α) = 0 := rfl

/-- Node count is independent of the cached height. -/
@[simp] public theorem size_node (h : Nat) (l : Tree α) (x : α) (r : Tree α) :
    size (.node h l x r) = size l + size r + 1 := rfl

/-- Rebuilding a node adds one key to its two children. -/
@[simp] public theorem size_mkNode (l : Tree α) (x : α) (r : Tree α) :
    size (mkNode l x r) = size l + size r + 1 := rfl

/-- Correct caches give the structural binary-tree height. -/
public theorem height_eq_of_cacheCorrect {t : Tree α} (hc : CacheCorrect t) :
    height t = (toBinaryTree t).height := by
  induction t with
  | empty => rfl
  | node h l x r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    simpa only [height_node, toBinaryTree_node, BinaryTree.height, ← il hl, ← ir hr] using hh

private theorem fib_max_le {a b : Nat} (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    Nat.fib (max a b + 3) ≤ Nat.fib (a + 2) + Nat.fib (b + 2) := by
  wlog h : b ≤ a generalizing a b
  · simpa only [max_comm, Nat.add_comm] using this hba hab (by omega)
  rw [max_eq_left h]
  cases a with
  | zero =>
    have hb : b = 0 := by omega
    subst b
    decide
  | succ a =>
    rw [show a + 1 + 3 = (a + 2) + 2 by omega, Nat.fib_add_two]
    have hb' : Nat.fib (a + 2) ≤ Nat.fib (b + 2) := Nat.fib_mono (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    omega

/-- Every cache-correct balanced tree has at least `fib (height + 2) - 1` keys. -/
public theorem fib_le_size_succ {t : Tree α} (hc : CacheCorrect t) (hb : Balanced t) :
    Nat.fib (height t + 2) ≤ size t + 1 := by
  suffices ∀ n, ∀ t : Tree α, height t = n → CacheCorrect t → Balanced t →
      Nat.fib (height t + 2) ≤ size t + 1 from this (height t) t rfl hc hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t ht hc hb
    cases t with
    | empty => simp [size]
    | node cached l x r =>
      rcases hc with ⟨hl, hr, hh⟩
      rcases hb with ⟨bl, br, hab, hba⟩
      simp only [height_node] at ht hh
      have il := ih (height l) (by omega) l rfl hl bl
      have ir := ih (height r) (by omega) r rfl hr br
      have hf := fib_max_le hab hba
      simp only [size, toBinaryTree_node, BinaryTree.numNodes] at il ir ⊢
      rw [height_node, hh]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega

private theorem two_pow_le_fib (k : Nat) : 2 ^ k ≤ Nat.fib (2 * k + 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hf := Nat.fib_mono (show 2 * k + 2 ≤ 2 * k + 3 by omega)
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega, Nat.fib_add_two, pow_succ]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega

/-- A natural-number (floor base-2) logarithm bound, with multiplicative constant 2 and offset 1. -/
public theorem height_le_log2 {t : Tree α} (hc : CacheCorrect t) (hb : Balanced t) :
    height t ≤ 2 * Nat.log2 (size t + 1) + 1 := by
  have hf := fib_le_size_succ hc hb
  have hp : 2 ^ (height t / 2) ≤ size t + 1 :=
    (two_pow_le_fib (height t / 2)).trans
      ((Nat.fib_mono (by omega)).trans hf)
  have hl : height t / 2 ≤ Nat.log2 (size t + 1) :=
    (Nat.le_log2 (by omega)).mpr hp
  omega

/-- Count one node rebuild at the actual smart-constructor call. -/
public def mkNodeT (l : Tree α) (x : α) (r : Tree α) : TimeM Nat (Tree α) := do
  ✓ return mkNode l x r

/-- Count each inspected heavy node and each actual rebuild in `balance`. -/
public def balanceT (l : Tree α) (x : α) (r : Tree α) : TimeM Nat (Tree α) :=
  if height r + 1 < height l then
    match l with
    | .node _ ll lx lr => do
        TimeM.tick 1 -- inspect the heavy child
        if height lr ≤ height ll then
          let nr ← mkNodeT lr x r
          mkNodeT ll lx nr
        else
          match lr with
          | .node _ lrl lrx lrr => do
              TimeM.tick 1 -- inspect the inner grandchild
              let nl ← mkNodeT ll lx lrl
              let nr ← mkNodeT lrr x r
              mkNodeT nl lrx nr
          | .empty => mkNodeT l x r
    | .empty => mkNodeT l x r
  else if height l + 1 < height r then
    match r with
    | .node _ rl rx rr => do
        TimeM.tick 1 -- inspect the heavy child
        if height rl ≤ height rr then
          let nl ← mkNodeT l x rl
          mkNodeT nl rx rr
        else
          match rl with
          | .node _ rll rlx rlr => do
              TimeM.tick 1 -- inspect the inner grandchild
              let nl ← mkNodeT l x rll
              let nr ← mkNodeT rlr rx rr
              mkNodeT nl rlx nr
          | .empty => mkNodeT l x r
    | .empty => mkNodeT l x r
  else mkNodeT l x r

/-- Search, counting each nonempty visit and each executed key comparison. -/
public def containsT [LinearOrder α] (x : α) : Tree α → TimeM Nat Bool
  | .empty => pure false
  | .node _ l key r => do
      TimeM.tick 1 -- visit
      TimeM.tick 1 -- x < key
      if x < key then containsT x l
      else do
        TimeM.tick 1 -- key < x
        if key < x then containsT x r else pure true

/-- Insert, counting search visits, comparisons, and the actual rotation rebuilds. -/
public def insertT [LinearOrder α] (x : α) : Tree α → TimeM Nat (Tree α)
  | .empty => mkNodeT .empty x .empty
  | t@(.node _ l key r) => do
      TimeM.tick 1 -- visit
      TimeM.tick 1 -- x < key
      if x < key then
        let nl ← insertT x l
        balanceT nl key r
      else do
        TimeM.tick 1 -- key < x
        if key < x then
          let nr ← insertT x r
          balanceT l key nr
        else pure t

/-- Find the leftmost key, counting every nonempty visit, including repeated traversals. -/
public def minDT : α → Tree α → TimeM Nat α
  | default, .empty => pure default
  | _, .node _ l key _ => do
      ✓ minDT key l

/-- Remove the leftmost key, counting visits and the actual rebalancing rebuilds. -/
public def eraseMinT : Tree α → TimeM Nat (Tree α)
  | .empty => pure .empty
  | .node _ l key r => do
      TimeM.tick 1 -- visit
      match l with
      | .empty => pure r
      | .node _ _ _ _ => do
          let nl ← eraseMinT l
          balanceT nl key r

/-- Delete, counting both `minD` and `eraseMin` traversals in the two-child branch. -/
public def eraseT [LinearOrder α] (x : α) : Tree α → TimeM Nat (Tree α)
  | .empty => pure .empty
  | .node _ l key r => do
      TimeM.tick 1 -- visit
      TimeM.tick 1 -- x < key
      if x < key then
        let nl ← eraseT x l
        balanceT nl key r
      else do
        TimeM.tick 1 -- key < x
        if key < x then
          let nr ← eraseT x r
          balanceT l key nr
        else
          match l, r with
          | .empty, _ => pure r
          | _, .empty => pure l
          | _, _ => do
              let successor ← minDT key r
              let nr ← eraseMinT r
              balanceT l successor nr

/-- Counted deletion under the existing alternative name. -/
public def deleteT [LinearOrder α] (x : α) (t : Tree α) : TimeM Nat (Tree α) :=
  eraseT x t

/-- Erasing the tick of a smart constructor recovers `mkNode`. -/
@[simp] public theorem ret_mkNodeT (l : Tree α) (x : α) (r : Tree α) :
    (mkNodeT l x r).ret = mkNode l x r := by
  simp [mkNodeT]

/-- The counted rebalancer returns exactly the existing rebalancer, for all inputs. -/
@[simp] public theorem ret_balanceT (l : Tree α) (x : α) (r : Tree α) :
    (balanceT l x r).ret = balance l x r := by
  by_cases hl : height r + 1 < height l
  · cases l with
    | empty => simp at hl
    | node h ll lx lr =>
      simp only [height_node] at hl
      by_cases hs : height lr ≤ height ll
      · simp [balanceT, balance, mkNodeT, hl, hs]
      · cases lr <;> simp only [height_node, height_empty] at hs <;>
          simp [balanceT, balance, mkNodeT, hl, hs]
  · by_cases hr : height l + 1 < height r
    · cases r with
      | empty => simp at hr
      | node h rl rx rr =>
        simp only [height_node] at hl hr
        by_cases hs : height rl ≤ height rr
        · simp [balanceT, balance, mkNodeT, hl, hr, hs]
        · cases rl <;> simp only [height_node, height_empty] at hs <;>
            simp [balanceT, balance, mkNodeT, hl, hr, hs]
    · simp [balanceT, balance, mkNodeT, hl, hr]

/-- Every local rebalancing run costs at most five units, including double rotations. -/
public theorem time_balanceT_le (l : Tree α) (x : α) (r : Tree α) :
    (balanceT l x r).time ≤ 5 := by
  by_cases hl : height r + 1 < height l
  · cases l with
    | empty => simp at hl
    | node h ll lx lr =>
      simp only [height_node] at hl
      by_cases hs : height lr ≤ height ll
      · simp [balanceT, mkNodeT, hl, hs]
      · cases lr <;> simp only [height_node, height_empty] at hs <;>
          simp [balanceT, mkNodeT, hl, hs]
  · by_cases hr : height l + 1 < height r
    · cases r with
      | empty => simp at hr
      | node h rl rx rr =>
        simp only [height_node] at hl hr
        by_cases hs : height rl ≤ height rr
        · simp [balanceT, mkNodeT, hl, hr, hs]
        · cases rl <;> simp only [height_node, height_empty] at hs <;>
            simp [balanceT, mkNodeT, hl, hr, hs]
    · simp [balanceT, mkNodeT, hl, hr]

/-- Erasing search ticks recovers the existing search. -/
@[simp] public theorem ret_containsT [LinearOrder α] (x : α) (t : Tree α) :
    (containsT x t).ret = contains x t := by
  induction t with
  | empty => simp [containsT, contains]
  | node h l key r il ir =>
    by_cases hlt : x < key <;> by_cases hgt : key < x <;>
      simp [containsT, contains, hlt, hgt, il, ir]

/-- Erasing insertion ticks recovers the existing insertion, including duplicates. -/
@[simp] public theorem ret_insertT [LinearOrder α] (x : α) (t : Tree α) :
    (insertT x t).ret = insert x t := by
  induction t with
  | empty => simp [insertT, insert]
  | node h l key r il ir =>
    by_cases hlt : x < key <;> by_cases hgt : key < x <;>
      simp [insertT, insert, hlt, hgt, il, ir]

/-- Erasing minimum-search ticks recovers the existing `minD`. -/
@[simp] public theorem ret_minDT (default : α) (t : Tree α) :
    (minDT default t).ret = minD default t := by
  induction t generalizing default with
  | empty => simp [minDT, minD]
  | node h l key r il ir => simp [minDT, minD, il]

/-- Erasing minimum-deletion ticks recovers the existing `eraseMin`. -/
@[simp] public theorem ret_eraseMinT (t : Tree α) :
    (eraseMinT t).ret = eraseMin t := by
  induction t with
  | empty => simp [eraseMinT, eraseMin]
  | node h l key r il ir =>
    rw [eraseMinT.eq_def, eraseMin.eq_def]
    cases l <;> simp only [TimeM.ret_bind, TimeM.ret_pure, ret_balanceT, il]

/-- Erasing deletion ticks recovers `erase`, including both successor traversals. -/
@[simp] public theorem ret_eraseT [LinearOrder α] (x : α) (t : Tree α) :
    (eraseT x t).ret = erase x t := by
  induction t with
  | empty => simp [eraseT, erase]
  | node h l key r il ir =>
    rw [eraseT.eq_def, erase.eq_def]
    simp only [TimeM.ret_bind]
    split
    · simp [il]
    · split
      · simp [ir]
      · cases l <;> cases r <;> simp [deleteMin]

/-- Erasing counted `delete` recovers the existing `delete`. -/
@[simp] public theorem ret_deleteT [LinearOrder α] (x : α) (t : Tree α) :
    (deleteT x t).ret = delete x t := ret_eraseT x t

/-- Search costs at most three units per level: one visit and up to two comparisons. -/
public theorem time_containsT_le [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) : (containsT x t).time ≤ 3 * height t := by
  induction t with
  | empty => simp [containsT]
  | node h l key r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    have bl := il hl
    have br := ir hr
    rw [containsT]
    simp only [TimeM.time_bind, TimeM.time_tick]
    split
    · simp only [height_node] at hh ⊢; omega
    · simp only [TimeM.time_bind, TimeM.time_tick]
      split <;> simp only [TimeM.time_pure, height_node] at * <;> omega

/-- Insertion costs at most eight units per old level and one for the new leaf. -/
public theorem time_insertT_le [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) : (insertT x t).time ≤ 8 * height t + 1 := by
  induction t with
  | empty => simp [insertT, mkNodeT]
  | node h l key r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    have bl := il hl
    have br := ir hr
    have bbalL := time_balanceT_le (insertT x l).ret key r
    have bbalR := time_balanceT_le l key (insertT x r).ret
    rw [insertT]
    simp only [TimeM.time_bind, TimeM.time_tick]
    split
    · simp only [TimeM.time_bind, height_node] at *; omega
    · simp only [TimeM.time_bind, TimeM.time_tick]
      split <;> simp only [TimeM.time_bind, TimeM.time_pure, height_node] at * <;> omega

/-- Minimum search counts at most one visit per level. -/
public theorem time_minDT_le (default : α) {t : Tree α} (hc : CacheCorrect t) :
    (minDT default t).time ≤ height t := by
  induction t generalizing default with
  | empty => simp [minDT]
  | node h l key r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    have bl := il key hl
    rw [minDT]
    simp only [TimeM.time_bind, TimeM.time_tick, height_node]
    omega

/-- Minimum deletion counts one visit and at most five rebalancing units per level. -/
public theorem time_eraseMinT_le {t : Tree α} (hc : CacheCorrect t) :
    (eraseMinT t).time ≤ 6 * height t := by
  induction t with
  | empty => simp [eraseMinT]
  | node h l key r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    have bl := il hl
    have bbal := time_balanceT_le (eraseMinT l).ret key r
    rw [eraseMinT.eq_def]
    simp only [TimeM.time_bind, TimeM.time_tick]
    cases l <;> simp only [TimeM.time_bind, TimeM.time_pure, height_node, height_empty] at *
      <;> omega

/-- Deletion costs at most eight units per old level, charging both successor traversals. -/
public theorem time_eraseT_le [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) : (eraseT x t).time ≤ 8 * height t := by
  induction t with
  | empty => simp [eraseT]
  | node h l key r il ir =>
    rcases hc with ⟨hl, hr, hh⟩
    have bl := il hl
    have br := ir hr
    have bbalL := time_balanceT_le (eraseT x l).ret key r
    have bbalR := time_balanceT_le l key (eraseT x r).ret
    have bmin := time_minDT_le key hr
    have beraseMin := time_eraseMinT_le hr
    have bbalMin := time_balanceT_le l (minDT key r).ret (eraseMinT r).ret
    rw [eraseT.eq_def]
    simp only [TimeM.time_bind, TimeM.time_tick]
    split
    · simp only [TimeM.time_bind, height_node] at *; omega
    · simp only [TimeM.time_bind, TimeM.time_tick]
      split
      · simp only [TimeM.time_bind, height_node] at *; omega
      · cases l <;> cases r <;>
          simp only [TimeM.time_bind, TimeM.time_pure, height_node, height_empty] at * <;> omega

/-- The height bound also holds under the name `deleteT`. -/
public theorem time_deleteT_le [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) : (deleteT x t).time ≤ 8 * height t :=
  time_eraseT_le x hc

/-- A counted search uses at most `6 * (log₂ (size + 1) + 1)` operations. -/
public theorem time_containsT_le_log2 [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) (hb : Balanced t) :
    (containsT x t).time ≤ 6 * (Nat.log2 (size t + 1) + 1) := by
  have := time_containsT_le x hc
  have := height_le_log2 hc hb
  omega

/-- A counted insertion uses at most `16 * (log₂ (size + 1) + 1)` operations. -/
public theorem time_insertT_le_log2 [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) (hb : Balanced t) :
    (insertT x t).time ≤ 16 * (Nat.log2 (size t + 1) + 1) := by
  have := time_insertT_le x hc
  have := height_le_log2 hc hb
  omega

/-- A counted deletion uses at most `16 * (log₂ (size + 1) + 1)` operations. -/
public theorem time_deleteT_le_log2 [LinearOrder α] (x : α) {t : Tree α}
    (hc : CacheCorrect t) (hb : Balanced t) :
    (deleteT x t).time ≤ 16 * (Nat.log2 (size t + 1) + 1) := by
  have := time_deleteT_le x hc
  have := height_le_log2 hc hb
  omega

end Cslib.Algorithms.Lean.AvlTree
