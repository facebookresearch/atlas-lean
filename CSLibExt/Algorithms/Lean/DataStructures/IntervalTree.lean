/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Order.RelClasses
public import Std.Data.TreeMap

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
# Balanced interval search trees

This module implements closed intervals in an AVL tree ordered by the low
endpoint and a stable occurrence identifier.  Each nonempty node stores its
subtree height, size, and maximum high endpoint.  A second balanced map locates
an existing identifier before replacement or deletion.
-/

namespace Cslib.Algorithms.Lean.IntervalTree

local instance : DecidableLE Int := Int.decLe
local instance : DecidableLT Int := Int.decLt
local instance : DecidableEq Int := Int.decEq

/-- A closed interval.  Public updates accept it only when `low ≤ high`. -/
structure Interval where
  low : Int
  high : Int
deriving Repr, DecidableEq

namespace Interval

/-- The endpoints of an interval are ordered. -/
def Valid (interval : Interval) : Prop :=
  interval.low ≤ interval.high

/-- Boolean validity check used by the executable update interface. -/
def valid (interval : Interval) : Bool :=
  letI : Decidable interval.Valid := Int.decLe _ _
  decide interval.Valid

/-- Closed-interval overlap; in particular, touching endpoints overlap. -/
def Overlaps (left right : Interval) : Prop :=
  left.low ≤ right.high ∧ right.low ≤ left.high

/-- Executable closed-interval overlap. -/
def overlaps (left right : Interval) : Bool :=
  match Int.decLe left.low right.high with
  | .isFalse _ => false
  | .isTrue _ =>
      match Int.decLe right.low left.high with
      | .isFalse _ => false
      | .isTrue _ => true

/-- Executable overlap together with the number of endpoint relations evaluated. -/
def overlapsWithCost (left right : Interval) : Bool × Nat :=
  match Int.decLe left.low right.high with
  | .isFalse _ => (false, 1)
  | .isTrue _ =>
      match Int.decLe right.low left.high with
      | .isFalse _ => (false, 2)
      | .isTrue _ => (true, 2)

/-- Instrumentation preserves the executable overlap result. -/
@[simp] theorem overlapsWithCost_fst (left right : Interval) :
    (left.overlapsWithCost right).1 = left.overlaps right := by
  unfold overlapsWithCost overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ => rfl
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> rfl

/-- Exactly one endpoint relation is skipped when the first relation is false. -/
theorem overlapsWithCost_snd (left right : Interval) :
    (left.overlapsWithCost right).2 = if left.low ≤ right.high then 2 else 1 := by
  unfold overlapsWithCost
  cases h₁ : Int.decLe left.low right.high with
  | isFalse h => simp [h]
  | isTrue h =>
      cases h₂ : Int.decLe right.low left.high <;> simp [h]

theorem overlaps_eq_true {left right : Interval} :
    left.overlaps right = true ↔
      left.Overlaps right := by
  unfold overlaps Overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ => simp_all
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all

theorem overlaps_comm (left right : Interval) :
    left.overlaps right = right.overlaps left := by
  unfold overlaps
  cases h₁ : Int.decLe left.low right.high with
  | isFalse _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all
  | isTrue _ =>
      cases h₂ : Int.decLe right.low left.high <;> simp_all

end Interval

/-- One stored interval occurrence.  Identifiers, rather than endpoints, are unique. -/
structure Entry where
  id : Nat
  interval : Interval
deriving Repr, DecidableEq

namespace Entry

/-- Deterministic BST key: low endpoint first, stable identifier second. -/
def key (entry : Entry) : Int × Nat :=
  (entry.interval.low, entry.id)

end Entry

/-- Compare low endpoints first, then occurrence identifiers. -/
def compareKey (left right : Int × Nat) : Ordering :=
  if left.1 < right.1 then .lt
  else if right.1 < left.1 then .gt
  else if left.2 < right.2 then .lt
  else if right.2 < left.2 then .gt
  else .eq

/-- Counts performed by the executable branches of an operation.

The `maxCacheReads` field is deliberately narrow: it counts only the
cached-maximum reads performed by search pruning in `searchWithCost`, one
per visited node where the left subtree's cached maximum decides the
descent. Maintenance paths (`mkNode`, `rebalanceWithCost`, and the
rotations) read cached heights, sizes, and maxima through constructor
patterns while rebuilding nodes; those field projections are not
separately instrumented, and maintenance work is reported through
`cacheWrites`, `rotations`, and the remaining counters instead. -/
structure Cost where
  nodeVisits : Nat := 0
  keyComparisons : Nat := 0
  endpointComparisons : Nat := 0
  /-- Cached-maximum reads performed by search pruning only; see `Cost`. -/
  maxCacheReads : Nat := 0
  cacheWrites : Nat := 0
  rotations : Nat := 0
  indexOperations : Nat := 0
deriving Repr, DecidableEq

namespace Cost

protected def add (left right : Cost) : Cost where
  nodeVisits := left.nodeVisits + right.nodeVisits
  keyComparisons := left.keyComparisons + right.keyComparisons
  endpointComparisons := left.endpointComparisons + right.endpointComparisons
  maxCacheReads := left.maxCacheReads + right.maxCacheReads
  cacheWrites := left.cacheWrites + right.cacheWrites
  rotations := left.rotations + right.rotations
  indexOperations := left.indexOperations + right.indexOperations

instance : Add Cost := ⟨Cost.add⟩

end Cost

/-- An AVL carrier with constant-time metadata fields at every nonempty node. -/
inductive Tree where
  | empty
  | node
      (height : Nat)
      (size : Nat)
      (maxHigh : Int)
      (left : Tree)
      (entry : Entry)
      (right : Tree)
deriving Repr, DecidableEq

namespace Tree

def height : Tree → Nat
  | .empty => 0
  | .node height _ _ _ _ _ => height

def size : Tree → Nat
  | .empty => 0
  | .node _ size _ _ _ _ => size

/-- A constant-time read of the cached maximum high endpoint. -/
def cachedMax? : Tree → Option Int
  | .empty => none
  | .node _ _ maxHigh _ _ _ => some maxHigh

/-- Include an optional subtree maximum without using a sentinel value. -/
def maxWith (fallback : Int) : Option Int → Int
  | none => fallback
  | some value => max fallback value

/-- Combine both cached child maxima with the root interval's high endpoint. -/
def nodeMax (left : Tree) (entry : Entry) (right : Tree) : Int :=
  maxWith (maxWith entry.interval.high left.cachedMax?) right.cachedMax?

/-- The sole ordinary node constructor; it repairs all metadata fields. -/
def mkNode (left : Tree) (entry : Entry) (right : Tree) : Tree :=
  .node (max left.height right.height + 1) (left.size + right.size + 1)
    (nodeMax left entry right) left entry right

def singleton (entry : Entry) : Tree :=
  mkNode .empty entry .empty

def entries : Tree → List (Entry)
  | .empty => []
  | .node _ _ _ left entry right => left.entries ++ entry :: right.entries

/-- Every cached field is exact, recursively: the cached maximum is an
attained upper bound, and the stored height and size equal the recursive
height (`max` of the child heights plus one) and size (sum of the child
sizes plus one) of the subtree. -/
def CacheInvariant : Tree → Prop
  | .empty => True
  | .node storedHeight storedSize maxHigh left entry right =>
      left.CacheInvariant ∧ right.CacheInvariant ∧
      (∀ stored ∈ left.entries ++ entry :: right.entries,
        stored.interval.high ≤ maxHigh) ∧
      (∃ stored ∈ left.entries ++ entry :: right.entries,
        stored.interval.high = maxHigh) ∧
      storedHeight = max left.height right.height + 1 ∧
      storedSize = left.size + right.size + 1

/-- Low endpoints respect the BST split at every node. -/
def LowOrdered : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.LowOrdered ∧ right.LowOrdered ∧
      (∀ stored ∈ left.entries, stored.interval.low ≤ entry.interval.low) ∧
      (∀ stored ∈ right.entries, entry.interval.low ≤ stored.interval.low)

/-- Every stored interval has ordered endpoints. -/
def ValidInvariant : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.ValidInvariant ∧ entry.interval.Valid ∧ right.ValidInvariant

def computedMax? : Tree → Option Int
  | .empty => none
  | .node _ _ _ left entry right =>
      some (maxWith (maxWith entry.interval.high left.computedMax?) right.computedMax?)

/-- A right rotation repairs the two affected nodes' metadata. -/
def rotateRight : Tree → Tree
  | .node _ _ _ (.node _ _ _ a x b) y c =>
      mkNode a x (mkNode b y c)
  | tree => tree

/-- A left rotation repairs the two affected nodes' metadata. -/
def rotateLeft : Tree → Tree
  | .node _ _ _ a x (.node _ _ _ b y c) =>
      mkNode (mkNode a x b) y c
  | tree => tree

/-- A left-right rotation repairs the three affected nodes' metadata. -/
def rotateLeftRight : Tree → Tree
  | .node _ _ _ (.node _ _ _ a x (.node _ _ _ b y c)) z d =>
      mkNode (mkNode a x b) y (mkNode c z d)
  | tree => tree

/-- A right-left rotation repairs the three affected nodes' metadata. -/
def rotateRightLeft : Tree → Tree
  | .node _ _ _ a x (.node _ _ _ (.node _ _ _ b y c) z d) =>
      mkNode (mkNode a x b) y (mkNode c z d)
  | tree => tree

/-- Rebalance one node and report the cache writes and rotations it performs. -/
def rebalanceWithCost (tree : Tree) : Tree × Cost :=
  match tree with
  | .empty => (.empty, {})
  | .node _ _ _ left _ right =>
      if left.height > right.height + 1 then
        match left with
        | .empty => (tree, {})
        | .node _ _ _ ll _ lr =>
            if ll.height ≥ lr.height then
              (rotateRight tree, { cacheWrites := 2, rotations := 1 })
            else
              (rotateLeftRight tree, { cacheWrites := 3, rotations := 2 })
      else if right.height > left.height + 1 then
        match right with
        | .empty => (tree, {})
        | .node _ _ _ rl _ rr =>
            if rr.height ≥ rl.height then
              (rotateLeft tree, { cacheWrites := 2, rotations := 1 })
            else
              (rotateRightLeft tree, { cacheWrites := 3, rotations := 2 })
      else
        (tree, {})

private def rebalance (tree : Tree) : Tree :=
  (rebalanceWithCost tree).1

/-- Keyed insertion or replacement, instrumented on its real execution path. -/
def insertKeyWithCost (newEntry : Entry) : Tree → Tree × Cost
  | .empty =>
      (singleton newEntry, { nodeVisits := 1, cacheWrites := 1 })
  | .node _ _ _ left entry right =>
      match compareKey newEntry.key entry.key with
      | .lt =>
          let (newLeft, childCost) := insertKeyWithCost newEntry left
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .eq =>
          (mkNode left newEntry right,
            { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 })
      | .gt =>
          let (newRight, childCost) := insertKeyWithCost newEntry right
          let (result, balanceCost) := rebalanceWithCost (mkNode left entry newRight)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)

def insertKey (tree : Tree) (entry : Entry) : Tree :=
  (tree.insertKeyWithCost entry).1

/-- Remove the leftmost entry, rebuilding and rebalancing its ancestor path. -/
def removeMinWithCost :
    Tree → Option (Entry × Tree × Cost)
  | .empty => none
  | .node _ _ _ .empty entry right =>
      some (entry, right, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      match removeMinWithCost left with
      | none => none
      | some (minimum, newLeft, childCost) =>
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          some (minimum, result,
            childCost + { nodeVisits := 1, cacheWrites := 1 } + balanceCost)

/-- Keyed deletion, instrumented on its real execution path. -/
def eraseKeyWithCost (key : Int × Nat) : Tree → Tree × Cost
  | .empty => (.empty, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      match compareKey key entry.key with
      | .lt =>
          let (newLeft, childCost) := eraseKeyWithCost key left
          let (result, balanceCost) := rebalanceWithCost (mkNode newLeft entry right)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .gt =>
          let (newRight, childCost) := eraseKeyWithCost key right
          let (result, balanceCost) := rebalanceWithCost (mkNode left entry newRight)
          (result,
            childCost + { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
              balanceCost)
      | .eq =>
          match right.removeMinWithCost with
          | none =>
              (left, { nodeVisits := 1, keyComparisons := 1 })
          | some (successor, newRight, childCost) =>
              let (result, balanceCost) := rebalanceWithCost (mkNode left successor newRight)
              (result,
                childCost +
                  { nodeVisits := 1, keyComparisons := 1, cacheWrites := 1 } +
                  balanceCost)

def eraseKey (tree : Tree) (key : Int × Nat) : Tree :=
  (tree.eraseKeyWithCost key).1

@[simp] theorem entries_mkNode (left : Tree) (entry : Entry) (right : Tree) :
    (mkNode left entry right).entries = left.entries ++ entry :: right.entries :=
  rfl

theorem entries_rotateRight (tree : Tree) :
    tree.rotateRight.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases left with
      | empty => rfl
      | node _ _ _ a x b =>
          simp [rotateRight, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateLeft (tree : Tree) :
    tree.rotateLeft.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases right with
      | empty => rfl
      | node _ _ _ b y c =>
          simp [rotateLeft, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateLeftRight (tree : Tree) :
    tree.rotateLeftRight.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases left with
      | empty => rfl
      | node _ _ _ a x lr =>
          cases lr with
          | empty => rfl
          | node _ _ _ b y c =>
              simp [rotateLeftRight, entries_mkNode, entries, List.append_assoc]

theorem entries_rotateRightLeft (tree : Tree) :
    tree.rotateRightLeft.entries = tree.entries := by
  cases tree with
  | empty => rfl
  | node _ _ _ left entry right =>
      cases right with
      | empty => rfl
      | node _ _ _ rl y c =>
          cases rl with
          | empty => rfl
          | node _ _ _ b z d =>
              simp [rotateRightLeft, entries_mkNode, entries, List.append_assoc]

theorem entries_rebalanceWithCost (tree : Tree) :
    (tree.rebalanceWithCost).1.entries = tree.entries := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | rfl
      | simp [entries_rotateRight, entries_rotateLeft,
          entries_rotateLeftRight, entries_rotateRightLeft]


/-- Cache-pruned overlap search and its faithful primitive trace. -/
def searchWithCost (query : Interval) : Tree → Option Entry × Cost
  | .empty => (none, { nodeVisits := 1 })
  | .node _ _ _ left entry right =>
      let (overlap, endpointCost) := entry.interval.overlapsWithCost query
      if overlap then
        (some entry, { nodeVisits := 1, endpointComparisons := endpointCost })
      else
        match left.cachedMax? with
        | none =>
            let (answer, childCost) := searchWithCost query right
            (answer, childCost + { nodeVisits := 1, endpointComparisons := endpointCost })
        | some leftMax =>
            if query.low ≤ leftMax then
              let (answer, childCost) := searchWithCost query left
              (answer, childCost +
                { nodeVisits := 1, endpointComparisons := endpointCost + 1, maxCacheReads := 1 })
            else
              let (answer, childCost) := searchWithCost query right
              (answer, childCost +
                { nodeVisits := 1, endpointComparisons := endpointCost + 1, maxCacheReads := 1 })

/-- An empty search performs its terminal visit and no endpoint comparisons. -/
@[simp] theorem searchWithCost_empty (query : Interval) :
    searchWithCost query .empty = (none, { nodeVisits := 1 }) := rfl

/-- A singleton search records its short-circuit endpoint count and any empty visit. -/
theorem searchWithCost_singleton (entry : Entry) (query : Interval) :
    searchWithCost query (singleton entry) =
      if entry.interval.overlaps query then
        (some entry,
          { nodeVisits := 1
            endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 })
      else
        (none,
          { nodeVisits := 2
            endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 }) := by
  by_cases rootMatches : entry.interval.overlaps query = true
  · simp [singleton, mkNode, searchWithCost, rootMatches, Interval.overlapsWithCost_snd]
  · simp only [singleton, mkNode, searchWithCost,
      Interval.overlapsWithCost_fst, cachedMax?, rootMatches, Bool.false_eq_true, ite_false,
      Interval.overlapsWithCost_snd]
    change ((none : Option Entry), Cost.add { nodeVisits := 1 }
      { nodeVisits := 1,
        endpointComparisons := if entry.interval.low ≤ query.high then 2 else 1 }) = _
    simp [Cost.add]

/-- Production overlap search; definitionally the answer from `searchWithCost`. -/
def search (tree : Tree) (query : Interval) : Option Entry :=
  (tree.searchWithCost query).1

/-- A separate full-traversal oracle used only by specifications and tests. -/
def oracleSearch (tree : Tree) (query : Interval) : Option Entry :=
  tree.entries.find? fun entry => entry.interval.overlaps query

theorem searchWithCost_fst (tree : Tree) (query : Interval) :
    (tree.searchWithCost query).1 = tree.search query := rfl

theorem search_sound {tree : Tree} {query : Interval}
    {entry : Entry} (found : tree.search query = some entry) :
    entry ∈ tree.entries ∧ entry.interval.overlaps query = true := by
  induction tree with
  | empty => simp [search, searchWithCost] at found
  | node height size maxHigh left root right leftIH rightIH =>
      simp only [search, searchWithCost] at found
      split at found
      · simp_all [entries]
      · split at found
        · exact ⟨by simp [entries, (rightIH found).1], (rightIH found).2⟩
        · split at found
          · exact ⟨by simp [entries, (leftIH found).1], (leftIH found).2⟩
          · exact ⟨by simp [entries, (rightIH found).1], (rightIH found).2⟩

/-- Under the structural cache/order invariants, every overlap is found. -/
theorem search_complete {tree : Tree} {query : Interval} {witness : Entry}
    (cache : tree.CacheInvariant) (ordered : tree.LowOrdered)
    (member : witness ∈ tree.entries)
    (overlap : witness.interval.Overlaps query) :
    ∃ found, tree.search query = some found := by
  induction tree generalizing query witness with
  | empty => simp [entries] at member
  | node height size maxHigh left root right leftIH rightIH =>
      simp only [CacheInvariant] at cache
      simp only [LowOrdered] at ordered
      rcases cache with ⟨leftCache, rightCache, _, _⟩
      rcases ordered with ⟨leftOrdered, rightOrdered, leftLow, rightLow⟩
      have memberCases :
          witness ∈ left.entries ∨ witness = root ∨ witness ∈ right.entries := by
        simpa [entries, or_assoc] using member
      by_cases rootMatches : root.interval.overlaps query = true
      · exact ⟨root, by simp [search, searchWithCost, rootMatches]⟩
      · cases left with
        | empty =>
            rcases memberCases with inLeft | atRoot | inRight
            · simp [entries] at inLeft
            · subst witness
              exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
            · rcases rightIH rightCache rightOrdered inRight overlap with
                ⟨found, foundEq⟩
              have foundCost : (right.searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?] using
                  foundCost⟩
        | node leftHeight leftSize leftMax leftLeft leftRoot leftRight =>
            simp only [CacheInvariant] at leftCache
            rcases leftCache with
              ⟨leftLeftCache, leftRightCache, leftUpper, leftWitness, leftHeightEq, leftSizeEq⟩
            by_cases inspectLeft : query.low ≤ leftMax
            · have leftHasOverlap :
                  ∃ candidate ∈
                      (Tree.node leftHeight leftSize leftMax leftLeft leftRoot
                        leftRight).entries,
                    candidate.interval.Overlaps query := by
                rcases memberCases with inLeft | atRoot | inRight
                · exact ⟨witness, inLeft, overlap⟩
                · subst witness
                  exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
                · rcases leftWitness with ⟨candidate, candidateMem, candidateHigh⟩
                  refine ⟨candidate, candidateMem, ?_, ?_⟩
                  · exact le_trans (leftLow candidate candidateMem)
                      (le_trans (rightLow witness inRight) overlap.1)
                  · simpa [candidateHigh] using inspectLeft
              rcases leftHasOverlap with
                ⟨candidate, candidateMem, candidateOverlap⟩
              rcases leftIH
                  ⟨leftLeftCache, leftRightCache, leftUpper, leftWitness,
                    leftHeightEq, leftSizeEq⟩
                  leftOrdered candidateMem candidateOverlap with
                ⟨found, foundEq⟩
              have foundCost :
                  ((Tree.node leftHeight leftSize leftMax leftLeft leftRoot
                    leftRight).searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?, inspectLeft]
                  using foundCost⟩
            · have inRight : witness ∈ right.entries := by
                rcases memberCases with inLeft | atRoot | inRight
                · have highLe : witness.interval.high ≤ leftMax :=
                    leftUpper witness inLeft
                  exact (inspectLeft (le_trans overlap.2 highLe)).elim
                · subst witness
                  exact (rootMatches (Interval.overlaps_eq_true.mpr overlap)).elim
                · exact inRight
              rcases rightIH rightCache rightOrdered inRight overlap with
                ⟨found, foundEq⟩
              have foundCost : (right.searchWithCost query).1 = some found := by
                simpa only [search] using foundEq
              exact ⟨found, by
                simpa [search, searchWithCost, rootMatches, cachedMax?, inspectLeft]
                  using foundCost⟩

/-- Failure is equivalent to the absence of an overlapping stored occurrence. -/
theorem search_eq_none_iff {tree : Tree} {query : Interval}
    (cache : tree.CacheInvariant) (ordered : tree.LowOrdered) :
    tree.search query = none ↔
      ∀ entry ∈ tree.entries, ¬entry.interval.Overlaps query := by
  constructor
  · intro none entry member overlap
    rcases search_complete cache ordered member overlap with ⟨found, foundEq⟩
    rw [none] at foundEq
    contradiction
  · intro noOverlap
    cases foundEq : tree.search query with
    | none => rfl
    | some entry =>
        have sound := search_sound foundEq
        exact (noOverlap entry sound.1
          (Interval.overlaps_eq_true.mp sound.2)).elim

/-- Recomputing all caches, used by the executable invariant checker only. -/
def cacheOK : Tree → Bool
  | .empty => true
  | .node storedHeight storedSize storedMax left entry right =>
      storedHeight == max left.height right.height + 1 &&
      storedSize == left.size + right.size + 1 &&
      storedMax == nodeMax left entry right &&
      left.cacheOK && right.cacheOK

/-- Check strict lower and upper key bounds when either bound is present. -/
def keyBetween
    (lower upper : Option (Int × Nat)) (key : Int × Nat) : Bool :=
  lower.all (fun value => compareKey value key == .lt) &&
    upper.all (fun value => compareKey key value == .lt)

/-- Check strict deterministic key ordering and interval validity. -/
def orderedValid :
    Option (Int × Nat) → Option (Int × Nat) → Tree → Bool
  | _, _, .empty => true
  | lower, upper, .node _ _ _ left entry right =>
      keyBetween lower upper entry.key && entry.interval.valid &&
      orderedValid lower (some entry.key) left &&
      orderedValid (some entry.key) upper right

/-- Check AVL balance and exact height metadata. -/
def balanced : Tree → Bool
  | .empty => true
  | .node storedHeight _ _ left _ right =>
      storedHeight == max left.height right.height + 1 &&
      left.height ≤ right.height + 1 && right.height ≤ left.height + 1 &&
      left.balanced && right.balanced

def uniqueIds (tree : Tree) : Bool :=
  decide (tree.entries.map (·.id)).Nodup

/-- Propositional AVL balance with exact height metadata. -/
def BalancedProp : Tree → Prop
  | .empty => True
  | .node storedHeight _ _ left _ right =>
      storedHeight = max left.height right.height + 1 ∧
      left.height ≤ right.height + 1 ∧ right.height ≤ left.height + 1 ∧
      left.BalancedProp ∧ right.BalancedProp

theorem balancedProp_of_balanced {tree : Tree} (h : tree.balanced = true) :
    tree.BalancedProp := by
  induction tree with
  | empty => trivial
  | node storedHeight _ _ left _ right leftIH rightIH =>
      simp only [balanced, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, leftIH h.1.2, rightIH h.2⟩

theorem compareKey_lt_low {a b : Int × Nat} (h : compareKey a b = .lt) :
    a.1 ≤ b.1 := by
  unfold compareKey at h
  by_cases hlt : a.1 < b.1
  · exact le_of_lt hlt
  · by_cases hgt : b.1 < a.1
    · simp [hlt, hgt] at h
    · have heq : a.1 = b.1 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      exact le_of_eq heq

theorem compareKey_lt_iff {a b : Int × Nat} :
    compareKey a b = .lt ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold compareKey
  split_ifs <;> simp_all <;> omega

/-- Full key ordering: every left-subtree key is below the node key and
every right-subtree key is above it. -/
def KeyOrdered : Tree → Prop
  | .empty => True
  | .node _ _ _ left entry right =>
      left.KeyOrdered ∧ right.KeyOrdered ∧
      (∀ e ∈ left.entries, compareKey e.key entry.key = .lt) ∧
      (∀ e ∈ right.entries, compareKey entry.key e.key = .lt)

theorem compareKey_lt_trans {a b c : Int × Nat} (h1 : compareKey a b = .lt)
    (h2 : compareKey b c = .lt) : compareKey a c = .lt := by
  rw [compareKey_lt_iff] at h1 h2 ⊢
  rcases h1 with h | ⟨h, h'⟩ <;> rcases h2 with g | ⟨g, g'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, by omega⟩


theorem keyOrdered_lowOrdered {tree : Tree} (h : tree.KeyOrdered) :
    tree.LowOrdered := by
  induction tree with
  | empty => trivial
  | node _ _ _ left entry right leftIH rightIH =>
      exact ⟨leftIH h.1, rightIH h.2.1,
        fun e he => compareKey_lt_low (h.2.2.1 e he),
        fun e he => compareKey_lt_low (h.2.2.2 e he)⟩

/-- The executable ordering check implies key ordering, with the
bound constraints threaded to every stored entry. -/
theorem keyOrdered_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.KeyOrdered ∧
      ∀ e ∈ tree.entries,
        (∀ v ∈ lower, compareKey v e.key = .lt) ∧
          ∀ v ∈ upper, compareKey e.key v = .lt := by
  induction tree generalizing lower upper with
  | empty => exact ⟨trivial, fun e he => by simp [entries] at he⟩
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [orderedValid, Bool.and_eq_true] at h
      have hbetween := h.1.1
      have hleft := h.1.2
      have hright := h.2
      rcases leftIH hleft with ⟨leftOrd, leftBounds⟩
      rcases rightIH hright with ⟨rightOrd, rightBounds⟩
      have hentry : (∀ v ∈ lower, compareKey v entry.key = .lt) ∧
          ∀ v ∈ upper, compareKey entry.key v = .lt := by
        have hb := hbetween
        rw [keyBetween] at hb
        simp only [Bool.and_eq_true, Option.all_eq_true] at hb
        constructor
        · intro v hv
          cases lower with
          | none => simp at hv
          | some x =>
              have hx : x = v := by simpa using hv
              exact beq_iff_eq.mp (hb.1.1 v (congrArg some hx))
        · intro v hv
          cases upper with
          | none => simp at hv
          | some x =>
              have hx : x = v := by simpa using hv
              exact beq_iff_eq.mp (hb.1.2 v (congrArg some hx))
      refine ⟨⟨leftOrd, rightOrd, ?_, ?_⟩, ?_⟩
      · intro stored hstored
        exact (leftBounds stored hstored).2 entry.key (by simp)
      · intro stored hstored
        exact (rightBounds stored hstored).1 entry.key (by simp)
      · intro e he
        simp only [entries, List.mem_append, List.mem_cons] at he
        rcases he with h | h | h
        · rcases leftBounds e h with ⟨hlo, hhi⟩
          exact ⟨hlo, fun v hv =>
            compareKey_lt_trans (hhi entry.key (by simp)) (hentry.2 v hv)⟩
        · subst h
          exact hentry
        · rcases rightBounds e h with ⟨hlo, hhi⟩
          exact ⟨fun v hv =>
            compareKey_lt_trans (hentry.1 v hv) (hlo entry.key (by simp)), hhi⟩

/-- The executable ordering check implies low-endpoint ordering, with the
bound constraints threaded to every stored entry. -/
theorem lowOrdered_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.LowOrdered ∧
      ∀ e ∈ tree.entries,
        (∀ v ∈ lower, compareKey v e.key = .lt) ∧
          ∀ v ∈ upper, compareKey e.key v = .lt :=
  ⟨keyOrdered_lowOrdered (keyOrdered_of_orderedValid h).1,
    (keyOrdered_of_orderedValid h).2⟩


/-- The executable ordering check also validates every stored interval. -/
theorem validInvariant_of_orderedValid {lower upper : Option (Int × Nat)}
    {tree : Tree} (h : tree.orderedValid lower upper = true) :
    tree.ValidInvariant := by
  induction tree generalizing lower upper with
  | empty => trivial
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [orderedValid, Bool.and_eq_true] at h
      exact ⟨leftIH h.1.2, by
        have hv := h.1.1.2
        unfold Interval.valid at hv
        exact @of_decide_eq_true _ (Int.decLe _ _) hv, rightIH h.2⟩

theorem key_nodup_of_id_nodup {tree : Tree}
    (h : (tree.entries.map (·.id)).Nodup) :
    (tree.entries.map Entry.key).Nodup := by
  have gen : ∀ l : List Entry, (l.map (·.id)).Nodup → (l.map Entry.key).Nodup := by
    intro l hl
    induction l with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.nodup_cons] at hl ⊢
        refine ⟨?_, ih hl.2⟩
        intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨y, hy, hkey⟩ := hmem
        have hid : y.id = x.id := congrArg Prod.snd hkey
        exact hl.1 (List.mem_map.mpr ⟨y, hy, hid⟩)
  exact gen tree.entries h

theorem compareKey_eq_iff {a b : Int × Nat} :
    compareKey a b = .eq ↔ a = b := by
  unfold compareKey
  split_ifs with h1 h2 h3 h4 <;> simp_all [Prod.ext_iff] <;> omega

theorem compareKey_gt {a b : Int × Nat} (h : compareKey a b = .gt) :
    compareKey b a = .lt := by
  unfold compareKey at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem compareKey_ne_of_lt {a b : Int × Nat} (h : compareKey a b = .lt) :
    a ≠ b := by
  intro hab
  subst hab
  simp [compareKey] at h

theorem mem_insertKeyWithCost (newEntry e : Entry) {tree : Tree}
    (huniq : (tree.entries.map Entry.key).Nodup) (hord : KeyOrdered tree) :
    e ∈ (tree.insertKeyWithCost newEntry).1.entries ↔
      e = newEntry ∨ (e ∈ tree.entries ∧ e.key ≠ newEntry.key) := by
  induction tree with
  | empty =>
      simp [insertKeyWithCost, singleton, entries_mkNode, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [entries, List.map_append, List.map_cons] at huniq
      rw [List.nodup_append] at huniq
      obtain ⟨hleft, hmid, hdisj⟩ := huniq
      have hentryR : entry.key ∉ right.entries.map Entry.key :=
        (List.nodup_cons.mp hmid).1
      have hright : (right.entries.map Entry.key).Nodup :=
        (List.nodup_cons.mp hmid).2
      have hdisj' : ∀ e ∈ left.entries, e.key ≠ entry.key := by
        intro x hx
        exact hdisj x.key (List.mem_map (f := Entry.key).mpr ⟨x, hx, rfl⟩)
          entry.key (List.mem_map (f := Entry.key).mpr
            ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩)
      have hdisjR : ∀ e ∈ right.entries, e.key ≠ entry.key := by
        intro x hx hkey
        exact hentryR (List.mem_map (f := Entry.key).mpr ⟨x, hx, hkey⟩)
      unfold insertKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft hord.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · rcases ih.mp he with rfl | ⟨he, hne⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨by simp [entries, he], hne⟩
          · subst he
            exact Or.inr ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hlt
              exact compareKey_ne_of_lt hlt rfl⟩
          · exact Or.inr ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hord.2.2.2 e he))
                hkey.symm⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp only [List.mem_append, List.mem_cons]
            exact Or.inl (ih.mpr (Or.inl rfl))
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl (ih.mpr (Or.inr ⟨he, hne⟩))
            · exact Or.inr (Or.inl he)
            · exact Or.inr (Or.inr he)
      · rename_i heq
        rw [entries_mkNode]
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact Or.inr ⟨by simp [entries, he], by
              intro hkey
              have hkk : newEntry.key = entry.key := compareKey_eq_iff.mp heq
              exact absurd (hkey.trans hkk) (hdisj' e he)⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨by simp [entries, he], by
              intro hkey
              have hkk : newEntry.key = entry.key := compareKey_eq_iff.mp heq
              exact absurd (hkey.trans hkk) (hdisjR e he)⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl he
            · subst he
              exact absurd (compareKey_eq_iff.mp heq).symm hne
            · exact Or.inr (Or.inr he)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright hord.2.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · exact Or.inr ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans (hord.2.2.1 e he) (compareKey_gt hgt))
                hkey⟩
          · subst he
            exact Or.inr ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hgt
              simp [compareKey] at hgt⟩
          · rcases ih.mp he with rfl | ⟨he, hne⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨by simp [entries, he], hne⟩
        · intro he
          rcases he with rfl | ⟨he, hne⟩
          · simp only [List.mem_append, List.mem_cons]
            exact Or.inr (Or.inr (ih.mpr (Or.inl rfl)))
          · simp only [entries, List.mem_append, List.mem_cons] at he ⊢
            rcases he with he | he | he
            · exact Or.inl he
            · exact Or.inr (Or.inl he)
            · exact Or.inr (Or.inr (ih.mpr (Or.inr ⟨he, hne⟩)))


theorem removeMinWithCost_spec {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (huniq : (tree.entries.map Entry.key).Nodup) :
    minimum ∈ tree.entries ∧
      ∀ e, e ∈ rest.entries ↔ e ∈ tree.entries ∧ e ≠ minimum := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          have hnotmem : minimum.key ∉ right.entries.map Entry.key := by
            have := huniq
            simp only [entries, List.map_append, List.map_cons] at this
            exact (List.nodup_cons.mp this).1
          refine ⟨by simp [entries], fun e => ?_⟩
          constructor
          · intro he
            exact ⟨by simp [entries, he], by
              intro hcon
              subst hcon
              exact hnotmem (List.mem_map (f := Entry.key).mpr ⟨e, he, rfl⟩)⟩
          · intro he
            rcases he with ⟨he, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at he
            rcases he with he | he | he
            · simp at he
            · subst he; exact absurd rfl hne
            · exact he
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            simp only [entries, List.map_append, List.map_cons] at huniq
            rw [List.nodup_append] at huniq
            have ih := leftIH hev (by simpa [entries] using huniq.1)
            rw [entries_rebalanceWithCost, entries_mkNode]
            have hminleft : minimum.key ∈
                List.map Entry.key ll.entries ++ le.key ::
                  List.map Entry.key lr.entries := by
              simpa [entries, List.map_append, List.map_cons] using
                (List.mem_map (f := Entry.key).mpr ⟨minimum, ih.1, rfl⟩)
            have hdisjLR : ∀ a ∈ List.map Entry.key ll.entries ++
                  le.key :: List.map Entry.key lr.entries,
                ∀ b ∈ (entry :: right.entries).map Entry.key, a ≠ b := huniq.2.2
            refine ⟨?_, fun e => ?_⟩
            · have h := ih.1
              simp only [entries, List.mem_append, List.mem_cons] at h ⊢
              rcases h with h | h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr (Or.inr h))
            · constructor
              · intro he
                simp only [List.mem_append, List.mem_cons] at he
                rcases he with he | he | he
                · rcases (ih.2 e).mp he with ⟨hmem, hne⟩
                  refine ⟨?_, hne⟩
                  have h := hmem
                  simp only [entries, List.mem_append, List.mem_cons] at h ⊢
                  rcases h with h | h | h
                  · exact Or.inl (Or.inl h)
                  · exact Or.inl (Or.inr (Or.inl h))
                  · exact Or.inl (Or.inr (Or.inr h))
                · exact ⟨by simp [entries, he], fun hcon =>
                    (hdisjLR minimum.key hminleft entry.key
                      (List.mem_map (f := Entry.key).mpr
                        ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩))
                      (by rw [← hcon, ← he])⟩
                · exact ⟨by simp [entries, he], fun hcon =>
                    (hdisjLR minimum.key hminleft minimum.key
                      (List.mem_map (f := Entry.key).mpr
                        ⟨e, List.mem_cons_of_mem entry he, congrArg Entry.key hcon⟩)) rfl⟩
              · intro he
                rcases he with ⟨hmem, hne⟩
                simp only [entries, List.mem_append, List.mem_cons] at hmem
                simp only [List.mem_append, List.mem_cons]
                rcases hmem with (he | rfl | he) | he | he
                · exact Or.inl ((ih.2 e).mpr ⟨List.mem_append_left _ he, hne⟩)
                · exact Or.inl ((ih.2 e).mpr
                    ⟨List.mem_append_right _ (List.mem_cons_self), hne⟩)
                · exact Or.inl ((ih.2 e).mpr
                    ⟨List.mem_append_right _ (List.mem_cons_of_mem _ he), hne⟩)
                · exact Or.inr (Or.inl he)
                · exact Or.inr (Or.inr he)

theorem removeMinWithCost_isSome {tree : Tree} (h : tree.entries ≠ []) :
    tree.removeMinWithCost.isSome := by
  induction tree with
  | empty => simp [entries] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty => simp [removeMinWithCost]
      | node hh ss mm ll le lr =>
          have ih := leftIH (by simp [entries])
          unfold removeMinWithCost
          split
          · rename_i hnone
            obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ih
            cases hnone.symm.trans hx
          · exact Option.isSome_some

theorem keyOrdered_mkNode {left right : Tree} {entry : Entry}
    (hleft : left.KeyOrdered) (hright : right.KeyOrdered)
    (hbl : ∀ e ∈ left.entries, compareKey e.key entry.key = .lt)
    (hbr : ∀ e ∈ right.entries, compareKey entry.key e.key = .lt) :
    (mkNode left entry right).KeyOrdered :=
  ⟨hleft, hright, hbl, hbr⟩

theorem keyOrdered_rotateRight {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateRight.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact h
      | node _ _ _ a x b =>
          obtain ⟨⟨ha, hb, hab, hxb⟩, hright, hleftb, hrightb⟩ := h
          change (mkNode a x (mkNode b entry right)).KeyOrdered
          apply keyOrdered_mkNode ha
          · apply keyOrdered_mkNode hb hright
            · intro e he
              exact hleftb e (by simp [entries, he])
            · exact hrightb
          · exact hab
          · intro e he
            simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact hxb e he
            · exact hleftb x (by simp [entries])
            · exact compareKey_lt_trans (hleftb x (by simp [entries])) (hrightb e he)

theorem keyOrdered_rotateLeft {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateLeft.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact h
      | node _ _ _ b y c =>
          obtain ⟨hleft, ⟨hb, hc, hby, hyc⟩, hleftb, hrightb⟩ := h
          change (mkNode (mkNode left entry b) y c).KeyOrdered
          apply keyOrdered_mkNode
          · apply keyOrdered_mkNode hleft hb
            · exact hleftb
            · intro e he
              exact hrightb e (by simp [entries, he])
          · exact hc
          · intro e he
            simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact compareKey_lt_trans (hleftb e he) (hrightb y (by simp [entries]))
            · exact hrightb y (by simp [entries])
            · exact hby e he
          · exact hyc

theorem keyOrdered_rotateLeftRight {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateLeftRight.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact h
      | node _ _ _ a x lr =>
          cases lr with
          | empty => exact h
          | node _ _ _ b y c =>
              obtain ⟨⟨ha, ⟨hb, hc, hbc, hcb⟩, hab, hxmid⟩, hright, hleftb, hrightb⟩ := h
              have hxy : compareKey x.key y.key = .lt :=
                hxmid y (by simp [entries])
              have hye : compareKey y.key entry.key = .lt :=
                hleftb y (by simp [entries])
              apply keyOrdered_mkNode
              · apply keyOrdered_mkNode ha hb hab
                intro e he
                exact hxmid e (by simp [entries, he])
              · apply keyOrdered_mkNode hc hright
                · intro e he
                  exact hleftb e (by simp [entries, he])
                · exact hrightb
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact compareKey_lt_trans (hab e he) hxy
                · exact hxy
                · exact hbc e he
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact hcb e he
                · exact hye
                · exact compareKey_lt_trans hye (hrightb e he)

theorem keyOrdered_rotateRightLeft {tree : Tree} (h : tree.KeyOrdered) :
    tree.rotateRightLeft.KeyOrdered := by
  cases tree with
  | empty => exact h
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact h
      | node _ _ _ rl y c =>
          cases rl with
          | empty => exact h
          | node _ _ _ b z d =>
              obtain ⟨hleft, ⟨⟨hb, hd, hbd, hdz⟩, hc, hmid, hzmid⟩, hleftb, hrightb⟩ := h
              have hzy : compareKey z.key y.key = .lt :=
                hmid z (by simp [entries])
              have hze : compareKey entry.key z.key = .lt :=
                hrightb z (by simp [entries])
              apply keyOrdered_mkNode
              · apply keyOrdered_mkNode hleft hb
                · exact hleftb
                · intro e he
                  exact hrightb e (by simp [entries, he])
              · apply keyOrdered_mkNode hd hc
                · intro e he
                  exact hmid e (by simp [entries, he])
                · exact hzmid
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact compareKey_lt_trans (hleftb e he) hze
                · exact hze
                · exact hbd e he
              · intro e he
                simp only [entries_mkNode, List.mem_append, List.mem_cons] at he
                rcases he with he | rfl | he
                · exact hdz e he
                · exact hzy
                · exact compareKey_lt_trans hzy (hzmid e he)

theorem keyOrdered_rebalance {tree : Tree} (h : tree.KeyOrdered) :
    (tree.rebalanceWithCost).1.KeyOrdered := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | exact h
      | exact keyOrdered_rotateRight h
      | exact keyOrdered_rotateLeft h
      | exact keyOrdered_rotateLeftRight h
      | exact keyOrdered_rotateRightLeft h

theorem mem_insertKeyWithCost_of_mem (newEntry e : Entry) (tree : Tree)
    (he : e ∈ (tree.insertKeyWithCost newEntry).1.entries) :
    e = newEntry ∨ e ∈ tree.entries := by
  induction tree with
  | empty =>
      exact Or.inl (by simpa [insertKeyWithCost, singleton, entries_mkNode,
        entries] using he)
  | node _ _ _ left entry right leftIH rightIH =>
      unfold insertKeyWithCost at he
      split at he
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · rcases leftIH he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
      · rw [entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | rfl | he
        · exact Or.inr (by simp [entries, he])
        · exact Or.inl rfl
        · exact Or.inr (by simp [entries, he])
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact Or.inr (by simp [entries, he])
        · exact Or.inr (by simp [entries, he])
        · rcases rightIH he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (by simp [entries, he])

theorem removeMinWithCost_min_mem {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) :
    minimum ∈ tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, -, -⟩ := h
          simp [entries]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, -, -⟩ := h
            have ih := leftIH hev
            simp only [entries, List.mem_append, List.mem_cons]
            simp only [entries, List.mem_append, List.mem_cons] at ih
            rcases ih with ih | ih | ih
            · exact Or.inl (Or.inl ih)
            · exact Or.inl (Or.inr (Or.inl ih))
            · exact Or.inl (Or.inr (Or.inr ih))

theorem mem_removeMinWithCost_of_mem {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) (e : Entry)
    (he : e ∈ rest.entries) : e ∈ tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH rightIH =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨-, rfl, -⟩ := h
          simp [entries, he]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨-, rfl, -⟩ := h
            rw [entries_rebalanceWithCost, entries_mkNode] at he
            simp only [List.mem_append, List.mem_cons] at he
            rcases he with he | he | he
            · have ih := leftIH hev he
              simp only [entries, List.mem_append, List.mem_cons]
              simp only [entries, List.mem_append, List.mem_cons] at ih
              rcases ih with ih | ih | ih
              · exact Or.inl (Or.inl ih)
              · exact Or.inl (Or.inr (Or.inl ih))
              · exact Or.inl (Or.inr (Or.inr ih))
            · simp [entries, he]
            · simp [entries, he]

theorem mem_eraseKeyWithCost_of_mem (key : Int × Nat) (e : Entry) (tree : Tree)
    (he : e ∈ (tree.eraseKeyWithCost key).1.entries) : e ∈ tree.entries := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries] at he
  | node _ _ _ left entry right leftIH rightIH =>
      unfold eraseKeyWithCost at he
      split at he
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact by simp [entries, leftIH he]
        · exact by simp [entries, he]
        · exact by simp [entries, he]
      · rw [entries_rebalanceWithCost, entries_mkNode] at he
        simp only [List.mem_append, List.mem_cons] at he
        rcases he with he | he | he
        · exact by simp [entries, he]
        · exact by simp [entries, he]
        · exact by simp [entries, rightIH he]
      · split at he
        · exact by simp [entries, he]
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode] at he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact by simp [entries, he]
          · exact by simp [entries, removeMinWithCost_min_mem hsome]
          · exact by simp [entries, mem_removeMinWithCost_of_mem hsome e he]

theorem mem_eraseKeyWithCost (key : Int × Nat) (e : Entry) {tree : Tree}
    (huniq : (tree.entries.map Entry.key).Nodup) (hord : KeyOrdered tree) :
    e ∈ (tree.eraseKeyWithCost key).1.entries ↔
      e ∈ tree.entries ∧ e.key ≠ key := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      simp only [entries, List.map_append, List.map_cons] at huniq
      rw [List.nodup_append] at huniq
      obtain ⟨hleft, hmid, hdisj⟩ := huniq
      have hright : (right.entries.map Entry.key).Nodup :=
        (List.nodup_cons.mp hmid).2
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft hord.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · rcases ih.mp he with ⟨hmem, hne⟩
            exact ⟨by simp [entries, hmem], hne⟩
          · subst he
            exact ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hlt
              exact compareKey_ne_of_lt hlt rfl⟩
          · exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt
                (hord.2.2.2 e he)) hkey.symm⟩
        · intro he
          rcases he with ⟨hmem, hne⟩
          simp only [entries, List.mem_append, List.mem_cons] at hmem
          simp only [List.mem_append, List.mem_cons]
          rcases hmem with he | he | he
          · exact Or.inl (ih.mpr ⟨he, hne⟩)
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr he)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright hord.2.1
        constructor
        · intro he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | he | he
          · exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (compareKey_lt_trans (hord.2.2.1 e he) (compareKey_gt hgt))
                hkey⟩
          · subst he
            exact ⟨by simp [entries], by
              intro hkey; rw [← hkey] at hgt
              simp [compareKey] at hgt⟩
          · rcases ih.mp he with ⟨hmem, hne⟩
            exact ⟨by simp [entries, hmem], hne⟩
        · intro he
          rcases he with ⟨hmem, hne⟩
          simp only [entries, List.mem_append, List.mem_cons] at hmem
          simp only [List.mem_append, List.mem_cons]
          rcases hmem with he | he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl he)
          · exact Or.inr (Or.inr (ih.mpr ⟨he, hne⟩))
      · rename_i heq
        have hkeyeq : key = entry.key := compareKey_eq_iff.mp heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          constructor
          · intro he
            exact ⟨by simp [entries, he], fun hkey =>
              compareKey_ne_of_lt (hord.2.2.1 e he) (by rw [hkey, hkeyeq])⟩
          · intro he
            rcases he with ⟨hmem, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at hmem
            rcases hmem with he | he | he
            · exact he
            · subst he; exact absurd hkeyeq.symm hne
            · simp at he
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode]
          have hspec := removeMinWithCost_spec hsome hright
          have hsuccmem : successor ∈ right.entries := hspec.1
          have hsucckey : successor.key ≠ key := by
            intro hkey
            have hlt : compareKey entry.key successor.key = .lt :=
              hord.2.2.2 successor hsuccmem
            rw [← hkeyeq] at hlt
            rw [hkey] at hlt
            simp [compareKey] at hlt
          constructor
          · intro he
            simp only [List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact ⟨by simp [entries, he], by
                intro hkey
                exact absurd (hkey.trans hkeyeq) (by
                  have hdisj2 : ∀ e ∈ left.entries, e.key ≠ entry.key := by
                    intro x hx
                    exact hdisj x.key (List.mem_map (f := Entry.key).mpr ⟨x, hx, rfl⟩)
                      entry.key (List.mem_map (f := Entry.key).mpr
                        ⟨entry, (by simp : entry ∈ entry :: right.entries), rfl⟩)
                  exact hdisj2 e he)⟩
            · exact ⟨by simp [entries, hsuccmem], hsucckey⟩
            · rcases (hspec.2 e).mp he with ⟨hmem, hne⟩
              exact ⟨by simp [entries, hmem], by
                intro hkey
                have hlt : compareKey entry.key e.key = .lt := hord.2.2.2 e hmem
                rw [← hkeyeq, hkey] at hlt
                simp [compareKey] at hlt⟩
          · intro he
            rcases he with ⟨hmem, hne⟩
            simp only [entries, List.mem_append, List.mem_cons] at hmem
            simp only [List.mem_append, List.mem_cons]
            rcases hmem with he | he | he
            · exact Or.inl he
            · subst he; exact absurd hkeyeq.symm hne
            · by_cases hsucc : e = successor
              · subst hsucc; exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr ((hspec.2 e).mpr ⟨he, hsucc⟩))

/-- Removing the minimum permutes the entry list by deleting exactly
that entry from the front of the remaining entries. -/
theorem removeMinWithCost_entries_perm {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost)) :
    (minimum :: rest.entries).Perm tree.entries := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          simp [entries]
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            rw [entries_rebalanceWithCost, entries_mkNode]
            have ih := leftIH hev
            simp only [entries] at ih ⊢
            exact List.Perm.append_right _ ih

/-- Insertion permutes the entry list by consing the new entry onto the
old entries with any same-key entry filtered out. -/
theorem insertKeyWithCost_entries_perm (newEntry : Entry) {tree : Tree}
    (hord : tree.KeyOrdered) :
    ((tree.insertKeyWithCost newEntry).1.entries).Perm
      (newEntry :: tree.entries.filter (fun e => e.key ≠ newEntry.key)) := by
  induction tree with
  | empty =>
      simp [insertKeyWithCost, singleton, entries_mkNode, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hleft, hright, hbl, hbr⟩ := hord
      unfold insertKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft
        have hentry : entry.key ≠ newEntry.key := fun hk =>
          compareKey_ne_of_lt hlt (by rw [hk])
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries.filter (fun e => e.key ≠ newEntry.key) ++
              entry :: right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hbr e he)) hk.symm))]
          simp [hentry]
        exact (List.Perm.append_right _ ih).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i heq
        rw [entries_mkNode]
        have hkeyeq : newEntry.key = entry.key := compareKey_eq_iff.mp heq
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries ++ right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq]))),
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (hbr e he) (hk.trans hkeyeq).symm))]
          simp [hkeyeq]
        exact List.perm_middle.trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright
        have hentry : entry.key ≠ newEntry.key := fun hk => by
          have := compareKey_gt hgt
          rw [hk] at this
          exact compareKey_ne_of_lt this rfl
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ newEntry.key) =
            left.entries ++ entry ::
              right.entries.filter (fun e => e.key ≠ newEntry.key) := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ newEntry.key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans (hbl e he)
                (compareKey_gt hgt)) hk))]
          simp [hentry]
        exact (List.Perm.append_left _
            (List.Perm.cons entry ih)).trans
          ((List.Perm.append_left _ (List.Perm.swap _ _ _)).trans
            (List.perm_middle.trans
              (by simp only [entries, hfilter]; exact List.Perm.refl _)))

/-- Erasure permutes the entry list by filtering out the erased key. -/
theorem eraseKeyWithCost_entries_perm (key : Int × Nat) {tree : Tree}
    (hord : tree.KeyOrdered) :
    ((tree.eraseKeyWithCost key).1.entries).Perm
      (tree.entries.filter (fun e => e.key ≠ key)) := by
  induction tree with
  | empty => simp [eraseKeyWithCost, entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hleft, hright, hbl, hbr⟩ := hord
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := leftIH hleft
        have hentry : entry.key ≠ key := fun hk =>
          compareKey_ne_of_lt hlt hk.symm
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ key) =
            left.entries.filter (fun e => e.key ≠ key) ++
              entry :: right.entries := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans hlt (hbr e he)) hk.symm))]
          simp [hentry]
        exact (List.Perm.append_right _ ih).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i hgt
        rw [entries_rebalanceWithCost, entries_mkNode]
        have ih := rightIH hright
        have hentry : entry.key ≠ key := fun hk => by
          have h2 := compareKey_gt hgt
          rw [← hk] at h2
          exact compareKey_ne_of_lt h2 rfl
        have hfilter : (left.entries ++ entry :: right.entries).filter
            (fun e => e.key ≠ key) =
            left.entries ++ entry ::
              right.entries.filter (fun e => e.key ≠ key) := by
          rw [List.filter_append, List.filter_cons,
            (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
              compareKey_ne_of_lt (compareKey_lt_trans (hbl e he)
                (compareKey_gt hgt)) hk))]
          simp [hentry]
        exact (List.Perm.append_left _
            (List.Perm.cons entry ih)).trans
          (by simp only [entries, hfilter]; exact List.Perm.refl _)
      · rename_i heq
        have hkeyeq : key = entry.key := compareKey_eq_iff.mp heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          have hfilter : (left.entries ++ entry :: []).filter
              (fun e => e.key ≠ key) = left.entries := by
            rw [List.filter_append, List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq])))]
            simp [hkeyeq]
          exact (by simp only [entries, hfilter]; exact List.Perm.refl _)
        · rename_i successor newRight childCost hsome
          rw [entries_rebalanceWithCost, entries_mkNode]
          have hperm := removeMinWithCost_entries_perm hsome
          have hsucc : successor.key ≠ key := by
            intro hk
            have hlt : compareKey entry.key successor.key = .lt :=
              hbr successor (removeMinWithCost_min_mem hsome)
            rw [← hkeyeq, hk] at hlt
            simp [compareKey] at hlt
          have hpermR : (right.entries.filter (fun e => e.key ≠ key)).Perm
              (successor :: newRight.entries) := by
            have h1 : (right.entries.filter (fun e => e.key ≠ key)).Perm
                ((successor :: newRight.entries).filter
                  (fun e => e.key ≠ key)) :=
              List.Perm.filter _ hperm.symm
            rw [List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt
                  (hbr e (mem_removeMinWithCost_of_mem hsome e he))
                  (by rw [hk, hkeyeq])))] at h1
            simpa [hsucc] using h1
          have hfilter : (left.entries ++ entry :: right.entries).filter
              (fun e => e.key ≠ key) =
              left.entries ++ right.entries.filter (fun e => e.key ≠ key) := by
            rw [List.filter_append, List.filter_cons,
              (List.filter_eq_self (p := fun e => e.key ≠ key)).mpr (fun e he =>
              decide_eq_true_eq.mpr (fun hk =>
                compareKey_ne_of_lt (hbl e he) (by rw [hk, hkeyeq])))]
            simp [hkeyeq]
          exact (List.Perm.append_left _ hpermR.symm).trans
            (by simp only [entries, hfilter]; exact List.Perm.refl _)

/-- Strict key ordering implies the stored keys are duplicate-free. -/
theorem keyNodup_of_keyOrdered {tree : Tree} (hord : tree.KeyOrdered) :
    (tree.entries.map Entry.key).Nodup := by
  induction tree with
  | empty => simp [entries]
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      simp only [entries, List.map_append, List.map_cons]
      rw [List.nodup_append]
      refine ⟨leftIH hl, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun hmem => ?_, rightIH hr⟩
        simp only [List.mem_map] at hmem
        obtain ⟨e, he, hk⟩ := hmem
        have hlt := hbr e he
        rw [← hk] at hlt
        simp [compareKey] at hlt
      · intro a ha b hb hab
        simp only [List.mem_map] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        rcases List.mem_cons.mp hb with rfl | hb
        · exact compareKey_ne_of_lt (hbl x hx) hab
        · simp only [List.mem_map] at hb
          obtain ⟨y, hy, rfl⟩ := hb
          exact compareKey_ne_of_lt
            (compareKey_lt_trans (hbl x hx) (hbr y hy)) hab

/-- The entry removed by `removeMinWithCost` is below every other stored
entry in a key-ordered tree. -/
theorem removeMinWithCost_min_le {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hord : tree.KeyOrdered) :
    ∀ e ∈ tree.entries, e = minimum ∨
      compareKey minimum.key e.key = .lt := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          intro e he
          simp only [entries, List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · simp at he
          · exact Or.inl rfl
          · exact Or.inr (hord.2.2.2 e he)
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            have ih := leftIH hev hord.1
            have hminmem := removeMinWithCost_min_mem hev
            intro e he
            simp only [entries, List.mem_append, List.mem_cons] at he
            rcases he with he | rfl | he
            · exact ih e (by
                simp only [entries, List.mem_append, List.mem_cons]
                exact he)
            · exact Or.inr (hord.2.2.1 minimum hminmem)
            · have h1 : compareKey minimum.key entry.key = .lt :=
                hord.2.2.1 minimum hminmem
              exact Or.inr (compareKey_lt_trans h1 (hord.2.2.2 e he))

/-- Insertion preserves strict key ordering. -/
theorem keyOrdered_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (hord : tree.KeyOrdered) :
    (tree.insertKeyWithCost newEntry).1.KeyOrdered := by
  induction tree with
  | empty =>
      exact keyOrdered_mkNode trivial trivial
        (fun e he => by simp [entries] at he)
        (fun e he => by simp [entries] at he)
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      unfold insertKeyWithCost
      split
      · rename_i hlt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode (leftIH hl) hr
        · intro e he
          rcases mem_insertKeyWithCost_of_mem newEntry e left he with rfl | he
          · exact hlt
          · exact hbl e he
        · exact hbr
      · rename_i heq
        have hkeyeq : newEntry.key = entry.key := compareKey_eq_iff.mp heq
        apply keyOrdered_mkNode hl hr
        · intro e he
          rw [hkeyeq]
          exact hbl e he
        · intro e he
          rw [hkeyeq]
          exact hbr e he
      · rename_i hgt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode hl (rightIH hr)
        · exact hbl
        · intro e he
          rcases mem_insertKeyWithCost_of_mem newEntry e right he with rfl | he
          · exact compareKey_gt hgt
          · exact hbr e he

/-- Removing the minimum preserves strict key ordering. -/
theorem keyOrdered_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hord : tree.KeyOrdered) : rest.KeyOrdered := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hord.2.1
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            apply keyOrdered_rebalance
            apply keyOrdered_mkNode (leftIH hev hord.1) hord.2.1
            · intro e he
              exact hord.2.2.1 e (mem_removeMinWithCost_of_mem hev e he)
            · exact hord.2.2.2

/-- Erasure preserves strict key ordering. -/
theorem keyOrdered_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hord : tree.KeyOrdered) :
    (tree.eraseKeyWithCost key).1.KeyOrdered := by
  induction tree with
  | empty => exact hord
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, hr, hbl, hbr⟩ := hord
      unfold eraseKeyWithCost
      split
      · rename_i hlt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode (leftIH hl) hr
        · intro e he
          exact hbl e (mem_eraseKeyWithCost_of_mem key e left he)
        · exact hbr
      · rename_i hgt
        apply keyOrdered_rebalance
        apply keyOrdered_mkNode hl (rightIH hr)
        · exact hbl
        · intro e he
          exact hbr e (mem_eraseKeyWithCost_of_mem key e right he)
      · rename_i heq
        split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          exact hl
        · rename_i successor newRight childCost hsome
          apply keyOrdered_rebalance
          apply keyOrdered_mkNode hl
            (keyOrdered_removeMinWithCost hsome hr)
          · intro e he
            exact compareKey_lt_trans (hbl e he)
              (hbr successor (removeMinWithCost_min_mem hsome))
          · intro e he
            have hmem : e ∈ right.entries :=
              mem_removeMinWithCost_of_mem hsome e he
            have hne : e ≠ successor := fun hcon =>
              ((removeMinWithCost_spec hsome
                (keyNodup_of_keyOrdered hr)).2 e).mp he |>.2 hcon
            rcases removeMinWithCost_min_le hsome hr e hmem with rfl | hlt
            · exact absurd rfl hne
            · exact hlt

theorem height_mkNode (l r : Tree) (e : Entry) :
    (mkNode l e r).height = max l.height r.height + 1 := rfl

/-- Rebalancing a node whose children are balanced and whose child
heights differ by at most two restores AVL balance; the resulting height
is the unrebalanced height or one less. -/
theorem balancedProp_rebalance_node {sh ss : Nat} {mm : Int}
    {l : Tree} {e : Entry} {r : Tree}
    (hstored : sh = max l.height r.height + 1)
    (hl : l.BalancedProp) (hr : r.BalancedProp)
    (hbal : l.height ≤ r.height + 2 ∧ r.height ≤ l.height + 2) :
    (rebalanceWithCost (.node sh ss mm l e r)).1.BalancedProp ∧
      ((rebalanceWithCost (.node sh ss mm l e r)).1.height =
          max l.height r.height + 1 ∨
        (rebalanceWithCost (.node sh ss mm l e r)).1.height + 1 =
          max l.height r.height + 1) ∧
      ((rebalanceWithCost (.node sh ss mm l e r)).1.height + 1 =
          max l.height r.height + 1 →
        l.height = r.height + 2 ∨ r.height = l.height + 2) := by
  have hnode : (Tree.node sh ss mm l e r).height = sh := rfl
  by_cases leftHeavy : l.height > r.height + 1
  · have hl2 : l.height = r.height + 2 := by omega
    simp only [rebalanceWithCost, ite_eq_left leftHeavy]
    cases l with
    | empty =>
        simp only [height] at leftHeavy
        omega
    | node lsh lss lm ll x lr =>
        have hlH : (Tree.node lsh lss lm ll x lr).height =
            max ll.height lr.height + 1 := hl.1
        dsimp only
        by_cases hsub : ll.height ≥ lr.height
        · simp only [ite_eq_left hsub]
          simp only [rotateRight]
          have hmid : (mkNode lr e r).height =
              max lr.height r.height + 1 := rfl
          have hres : (mkNode ll x (mkNode lr e r)).height =
              max ll.height (mkNode lr e r).height + 1 := rfl
          obtain ⟨hsh, hle1, hle2, hllB, hlrB⟩ := hl
          rw [hlH]
          refine ⟨⟨rfl, by omega, by omega, hllB,
            ⟨rfl, by omega, by omega, hlrB, hr⟩⟩, by omega,
            fun _ => Or.inl (by omega)⟩
        · simp only [ite_eq_right hsub]
          cases lr with
          | empty =>
              simp only [height] at hsub
              omega
          | node bsh bss bm b y c =>
              have hlrH : (Tree.node bsh bss bm b y c).height =
                  max b.height c.height + 1 := hl.2.2.2.2.1
              obtain ⟨hsh, hle1, hle2, hllB, hlrB⟩ := hl
              obtain ⟨hlrSh, hble1, hble2, hbB, hcB⟩ := hlrB
              simp only [rotateLeftRight]
              have hL : (mkNode ll x b).height =
                  max ll.height b.height + 1 := rfl
              have hR : (mkNode c e r).height =
                  max c.height r.height + 1 := rfl
              have hres : (mkNode (mkNode ll x b) y (mkNode c e r)).height =
                  max (mkNode ll x b).height (mkNode c e r).height + 1 := rfl
              rw [hlH, hlrH]
              refine ⟨⟨rfl, by omega, by omega,
                ⟨rfl, by omega, by omega, hllB, hbB⟩,
                ⟨rfl, by omega, by omega, hcB, hr⟩⟩, by omega,
                fun _ => Or.inl (by omega)⟩
  · by_cases rightHeavy : r.height > l.height + 1
    · have hr2 : r.height = l.height + 2 := by omega
      simp only [rebalanceWithCost, ite_eq_right leftHeavy,
        ite_eq_left rightHeavy]
      cases r with
      | empty =>
          simp only [height] at rightHeavy
          omega
      | node rsh rss rm rl y rr =>
          have hrH : (Tree.node rsh rss rm rl y rr).height =
              max rl.height rr.height + 1 := hr.1
          dsimp only
          by_cases hsub : rr.height ≥ rl.height
          · simp only [ite_eq_left hsub]
            simp only [rotateLeft]
            have hmid : (mkNode l e rl).height =
                max l.height rl.height + 1 := rfl
            have hres : (mkNode (mkNode l e rl) y rr).height =
                max (mkNode l e rl).height rr.height + 1 := rfl
            obtain ⟨hsh, hre1, hre2, hrlB, hrrB⟩ := hr
            rw [hrH]
            refine ⟨⟨rfl, by omega, by omega,
              ⟨rfl, by omega, by omega, hl, hrlB⟩,
              hrrB⟩, by omega, fun _ => Or.inr (by omega)⟩
          · simp only [ite_eq_right hsub]
            cases rl with
            | empty =>
                simp only [height] at hsub
                omega
            | node bsh bss bm b z d =>
                have hrlH : (Tree.node bsh bss bm b z d).height =
                    max b.height d.height + 1 := hr.2.2.2.1.1
                obtain ⟨hsh, hre1, hre2, hrlB, hrrB⟩ := hr
                obtain ⟨hrlSh, hde1, hde2, hbB, hdB⟩ := hrlB
                simp only [rotateRightLeft]
                have hL : (mkNode l e b).height =
                    max l.height b.height + 1 := rfl
                have hR : (mkNode d y rr).height =
                    max d.height rr.height + 1 := rfl
                have hres : (mkNode (mkNode l e b) z (mkNode d y rr)).height =
                    max (mkNode l e b).height (mkNode d y rr).height + 1 := rfl
                rw [hrH, hrlH]
                refine ⟨⟨rfl, by omega, by omega,
                  ⟨rfl, by omega, by omega, hl, hbB⟩,
                  ⟨rfl, by omega, by omega, hdB, hrrB⟩⟩, by omega,
                  fun _ => Or.inr (by omega)⟩
    · simp only [rebalanceWithCost, ite_eq_right leftHeavy,
        ite_eq_right rightHeavy]
      refine ⟨⟨hstored, by omega, by omega, hl, hr⟩, Or.inl hstored,
        fun hdrop => by omega⟩

/-- Rebalancing an `mkNode` whose children are balanced and whose child
heights differ by at most two restores AVL balance. -/
theorem balancedProp_rebalance_mkNode {l : Tree} {e : Entry} {r : Tree}
    (hl : l.BalancedProp) (hr : r.BalancedProp)
    (hbal : l.height ≤ r.height + 2 ∧ r.height ≤ l.height + 2) :
    (rebalanceWithCost (mkNode l e r)).1.BalancedProp ∧
      ((rebalanceWithCost (mkNode l e r)).1.height =
          max l.height r.height + 1 ∨
        (rebalanceWithCost (mkNode l e r)).1.height + 1 =
          max l.height r.height + 1) ∧
      ((rebalanceWithCost (mkNode l e r)).1.height + 1 =
          max l.height r.height + 1 →
        l.height = r.height + 2 ∨ r.height = l.height + 2) :=
  balancedProp_rebalance_node rfl hl hr hbal

/-- Insertion preserves AVL balance; the height grows by at most one. -/
theorem balancedProp_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (hb : tree.BalancedProp) :
    (tree.insertKeyWithCost newEntry).1.BalancedProp ∧
      ((tree.insertKeyWithCost newEntry).1.height = tree.height ∨
        (tree.insertKeyWithCost newEntry).1.height = tree.height + 1) := by
  induction tree with
  | empty =>
      refine ⟨⟨rfl, by omega, by omega, trivial, trivial⟩, Or.inr rfl⟩
  | node sh ss mm left entry right leftIH rightIH =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      unfold insertKeyWithCost
      split
      · obtain ⟨ihB, ihH⟩ := leftIH hlB
        have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB
          ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode (insertKeyWithCost newEntry left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode (insertKeyWithCost newEntry left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height + 1
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · refine ⟨⟨rfl, hle1, hle2, hlB, hrB⟩, Or.inl ?_⟩
        have hmk : (mkNode left newEntry right).height =
            max left.height right.height + 1 := rfl
        rw [hmk]
        exact hsh.symm
      · obtain ⟨ihB, ihH⟩ := rightIH hrB
        have hres := balancedProp_rebalance_mkNode (e := entry) hlB ihB ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode left entry
            (insertKeyWithCost newEntry right).1)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode left entry
            (insertKeyWithCost newEntry right).1)).1.height =
            (Tree.node sh ss mm left entry right).height + 1
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- Removing the minimum preserves AVL balance; the height drops by at
most one. -/
theorem balancedProp_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hb : tree.BalancedProp) :
    rest.BalancedProp ∧
      (rest.height = tree.height ∨ rest.height + 1 = tree.height) := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node sh ss mm left entry right leftIH _ =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          refine ⟨hrB, Or.inr ?_⟩
          have hempty : (Tree.empty : Tree).height = 0 := rfl
          omega
      | node lsh lss lm ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            obtain ⟨ihB, ihH⟩ := leftIH hev hlB
            have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB ⟨by omega, by omega⟩
            refine ⟨hres.1, ?_⟩
            have hlH : (Tree.node lsh lss lm ll le lr).height =
                max ll.height lr.height + 1 := hlB.1
            rcases hres.2.1 with hh | hh
            · rcases ihH with ih | ih <;> omega
            · have hvy := hres.2.2 hh
              rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- Erasure preserves AVL balance; the height drops by at most one. -/
theorem balancedProp_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hb : tree.BalancedProp) :
    (tree.eraseKeyWithCost key).1.BalancedProp ∧
      ((tree.eraseKeyWithCost key).1.height = tree.height ∨
        (tree.eraseKeyWithCost key).1.height + 1 = tree.height) := by
  induction tree with
  | empty => exact ⟨hb, Or.inl rfl⟩
  | node sh ss mm left entry right leftIH rightIH =>
      obtain ⟨hsh, hle1, hle2, hlB, hrB⟩ := hb
      have hnode : (Tree.node sh ss mm left entry right).height = sh := rfl
      unfold eraseKeyWithCost
      split
      · obtain ⟨ihB, ihH⟩ := leftIH hlB
        have hres := balancedProp_rebalance_mkNode (e := entry) ihB hrB
          ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode (eraseKeyWithCost key left).1
            entry right)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode (eraseKeyWithCost key left).1
            entry right)).1.height + 1 =
            (Tree.node sh ss mm left entry right).height
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · obtain ⟨ihB, ihH⟩ := rightIH hrB
        have hres := balancedProp_rebalance_mkNode (e := entry) hlB ihB ⟨by omega, by omega⟩
        refine ⟨hres.1, ?_⟩
        change (rebalanceWithCost (mkNode left entry
            (eraseKeyWithCost key right).1)).1.height =
            (Tree.node sh ss mm left entry right).height ∨
          (rebalanceWithCost (mkNode left entry
            (eraseKeyWithCost key right).1)).1.height + 1 =
            (Tree.node sh ss mm left entry right).height
        rcases hres.2.1 with h | h
        · rcases ihH with ih | ih <;> omega
        · have hvy := hres.2.2 h
          rcases ihH with ih | ih <;> rcases hvy with hv | hv <;> omega
      · split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          refine ⟨hlB, Or.inr ?_⟩
          change left.height + 1 =
            (Tree.node sh ss mm left entry Tree.empty).height
          have hempty : (Tree.empty : Tree).height = 0 := rfl
          omega
        · rename_i successor newRight childCost hsome
          obtain ⟨rmB, rmH⟩ := balancedProp_removeMinWithCost hsome hrB
          have hres := balancedProp_rebalance_mkNode (e := successor) hlB rmB ⟨by omega, by omega⟩
          refine ⟨hres.1, ?_⟩
          change (rebalanceWithCost (mkNode left successor newRight)).1.height =
              (Tree.node sh ss mm left entry right).height ∨
            (rebalanceWithCost (mkNode left successor newRight)).1.height + 1 =
              (Tree.node sh ss mm left entry right).height
          rcases hres.2.1 with h | h
          · rcases rmH with ih | ih <;> omega
          · have hvy := hres.2.2 h
            rcases rmH with ih | ih <;> rcases hvy with hv | hv <;> omega

/-- A node built by `mkNode` inherits stored-interval validity. -/
theorem validInvariant_mkNode {left right : Tree} {entry : Entry}
    (hl : left.ValidInvariant) (he : entry.interval.Valid)
    (hr : right.ValidInvariant) :
    (mkNode left entry right).ValidInvariant :=
  ⟨hl, he, hr⟩

theorem validInvariant_rotateRight {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateRight.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact hv
      | node _ _ _ a x b =>
          obtain ⟨⟨hva, hx, hvb⟩, hy, hvc⟩ := hv
          exact validInvariant_mkNode hva hx
            (validInvariant_mkNode hvb hy hvc)

theorem validInvariant_rotateLeft {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateLeft.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact hv
      | node _ _ _ b y c =>
          obtain ⟨hl, hx, ⟨hvb, hy, hvc⟩⟩ := hv
          exact validInvariant_mkNode
            (validInvariant_mkNode hl hx hvb) hy hvc

theorem validInvariant_rotateLeftRight {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateLeftRight.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases left with
      | empty => exact hv
      | node _ _ _ a x lr =>
          cases lr with
          | empty => exact hv
          | node _ _ _ b y c =>
              obtain ⟨⟨hva, hx, ⟨hvb, hy, hvc⟩⟩, he, hr⟩ := hv
              exact validInvariant_mkNode
                (validInvariant_mkNode hva hx hvb) hy
                (validInvariant_mkNode hvc he hr)

theorem validInvariant_rotateRightLeft {tree : Tree}
    (hv : tree.ValidInvariant) : tree.rotateRightLeft.ValidInvariant := by
  cases tree with
  | empty => exact hv
  | node _ _ _ left entry right =>
      cases right with
      | empty => exact hv
      | node _ _ _ rl y c =>
          cases rl with
          | empty => exact hv
          | node _ _ _ b z d =>
              obtain ⟨hl, he, ⟨⟨hvb, hz, hvd⟩, hy, hvc⟩⟩ := hv
              exact validInvariant_mkNode
                (validInvariant_mkNode hl he hvb) hz
                (validInvariant_mkNode hvd hy hvc)

theorem validInvariant_rebalanceWithCost {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.rebalanceWithCost).1.ValidInvariant := by
  unfold rebalanceWithCost
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
    first
      | exact hv
      | exact validInvariant_rotateRight hv
      | exact validInvariant_rotateLeft hv
      | exact validInvariant_rotateLeftRight hv
      | exact validInvariant_rotateRightLeft hv

/-- Every stored entry of a validity-invariant tree is valid. -/
theorem validInvariant_mem {tree : Tree} (hv : tree.ValidInvariant)
    (e : Entry) (he : e ∈ tree.entries) : e.interval.Valid := by
  induction tree with
  | empty => simp [entries] at he
  | node _ _ _ l en r lIH rIH =>
      obtain ⟨hl, hen, hr⟩ := hv
      simp only [entries, List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact lIH hl he
      · exact hen
      · exact rIH hr he

/-- Insertion of a valid entry preserves stored-interval validity. -/
theorem validInvariant_insertKeyWithCost (newEntry : Entry)
    (hnew : newEntry.interval.Valid) {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.insertKeyWithCost newEntry).1.ValidInvariant := by
  induction tree with
  | empty => exact validInvariant_mkNode trivial hnew trivial
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, he, hr⟩ := hv
      unfold insertKeyWithCost
      split
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode (leftIH hl) he hr)
      · exact validInvariant_mkNode hl hnew hr
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode hl he (rightIH hr))

/-- Removing the minimum preserves stored-interval validity. -/
theorem validInvariant_removeMinWithCost {tree : Tree} {minimum : Entry}
    {rest : Tree} {cost : Cost}
    (h : tree.removeMinWithCost = some (minimum, rest, cost))
    (hv : tree.ValidInvariant) : rest.ValidInvariant := by
  induction tree generalizing rest cost with
  | empty => simp [removeMinWithCost] at h
  | node _ _ _ left entry right leftIH _ =>
      cases left with
      | empty =>
          simp only [removeMinWithCost] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact hv.2.2
      | node _ _ _ ll le lr =>
          simp only [removeMinWithCost] at h
          split at h
          · simp at h
          · rename_i minimum' newLeft childCost hev
            obtain ⟨rfl, rfl, -⟩ := h
            exact validInvariant_rebalanceWithCost
              (validInvariant_mkNode (leftIH hev hv.1) hv.2.1 hv.2.2)

/-- Erasure preserves stored-interval validity. -/
theorem validInvariant_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (hv : tree.ValidInvariant) :
    (tree.eraseKeyWithCost key).1.ValidInvariant := by
  induction tree with
  | empty => exact hv
  | node _ _ _ left entry right leftIH rightIH =>
      obtain ⟨hl, he, hr⟩ := hv
      unfold eraseKeyWithCost
      split
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode (leftIH hl) he hr)
      · exact validInvariant_rebalanceWithCost
          (validInvariant_mkNode hl he (rightIH hr))
      · split
        · rename_i hnone
          have hrempty : right = .empty := by
            cases right with
            | empty => rfl
            | node hh ss mm l2 e2 r2 =>
                have hsome := removeMinWithCost_isSome
                  (tree := Tree.node hh ss mm l2 e2 r2) (by simp [entries])
                rw [hnone] at hsome
                simp at hsome
          subst hrempty
          exact hl
        · rename_i successor newRight childCost hsome
          exact validInvariant_rebalanceWithCost
            (validInvariant_mkNode hl
              (validInvariant_mem hr successor
                (removeMinWithCost_min_mem hsome))
              (validInvariant_removeMinWithCost hsome hr))

end Tree
/-- The interval tree plus its balanced ID-to-low-endpoint index. -/
structure IndexedIntervalTree where
  root : Tree
  idIndex : Std.TreeMap Nat Int



namespace IndexedIntervalTree

def empty : IndexedIntervalTree :=
  ⟨.empty, .empty⟩

/-- Insert a new occurrence or replace the occurrence with the same identifier. -/
def insertWithCost
    (tree : IndexedIntervalTree) (entry : Entry) : Option IndexedIntervalTree × Cost :=
  if entry.interval.valid then
    let (withoutOld, eraseCost) :=
      match tree.idIndex.get? entry.id with
      | none => (tree.root, ({} : Cost))
      | some oldLow => tree.root.eraseKeyWithCost (oldLow, entry.id)
    let (newRoot, insertCost) := withoutOld.insertKeyWithCost entry
    (some ⟨newRoot, tree.idIndex.insert entry.id entry.interval.low⟩,
      eraseCost + insertCost +
        { endpointComparisons := 1, indexOperations := 2 })
  else
    (none, { endpointComparisons := 1 })

def insert (tree : IndexedIntervalTree) (entry : Entry) : Option IndexedIntervalTree :=
  (tree.insertWithCost entry).1

/-- Delete exactly the occurrence with this identifier; absent IDs are unchanged. -/
def eraseWithCost (tree : IndexedIntervalTree) (id : Nat) : IndexedIntervalTree × Cost :=
  match tree.idIndex.get? id with
  | none => (tree, { indexOperations := 1 })
  | some low =>
      let (newRoot, eraseCost) := tree.root.eraseKeyWithCost (low, id)
      (⟨newRoot, tree.idIndex.erase id⟩,
        eraseCost + { indexOperations := 2 })

def erase (tree : IndexedIntervalTree) (id : Nat) : IndexedIntervalTree :=
  (tree.eraseWithCost id).1

def searchWithCost
    (tree : IndexedIntervalTree) (query : Interval) : Option Entry × Cost :=
  if query.valid then
    let (answer, cost) := tree.root.searchWithCost query
    (answer, cost + { endpointComparisons := 1 })
  else (none, { endpointComparisons := 1 })

def search (tree : IndexedIntervalTree) (query : Interval) : Option Entry :=
  (tree.searchWithCost query).1

def oracleSearch (tree : IndexedIntervalTree) (query : Interval) : Option Entry :=
  if query.valid then tree.root.oracleSearch query else none

/-- Every stored occurrence agrees with its identifier-index entry. -/
def indexForwardOK (tree : IndexedIntervalTree) : Bool :=
  tree.root.entries.all fun entry =>
    tree.idIndex.get? entry.id == some entry.interval.low

/-- Every identifier-index entry is represented by a stored occurrence. -/
def indexBackwardOK (tree : IndexedIntervalTree) : Bool :=
  tree.idIndex.toList.all fun pair =>
    tree.root.entries.any fun entry =>
      entry.id == pair.1 && entry.interval.low == pair.2

/-- Executable representation checker, including cache/index correspondence. -/
def check (tree : IndexedIntervalTree) : Bool :=
  tree.root.cacheOK && tree.root.balanced &&
    tree.root.orderedValid none none && tree.root.uniqueIds &&
    tree.indexForwardOK && tree.indexBackwardOK

/-- Bundled representation invariant for the public indexed tree: exact
caches, strict composite-key BST ordering, stored-interval validity, AVL
balance, unique identifiers, and two-way identifier-index correspondence.
Low-endpoint ordering used by search is derived from the strict key
ordering via `Tree.keyOrdered_lowOrdered`. -/
def Invariant (tree : IndexedIntervalTree) : Prop :=
  tree.root.CacheInvariant ∧ tree.root.KeyOrdered ∧ tree.root.BalancedProp ∧
    tree.root.ValidInvariant ∧
    (tree.root.entries.map (·.id)).Nodup ∧
    (∀ e ∈ tree.root.entries, tree.idIndex.get? e.id = some e.interval.low) ∧
    ∀ p ∈ tree.idIndex.toList,
      ∃ e ∈ tree.root.entries, e.id = p.1 ∧ e.interval.low = p.2

end IndexedIntervalTree

end Cslib.Algorithms.Lean.IntervalTree

namespace Cslib.Algorithms.Lean.IntervalTree.Tree

private theorem le_maxWith (fallback : Int) (tree : Tree) :
    fallback ≤ maxWith fallback tree.cachedMax? := by
  cases tree <;> simp [maxWith, cachedMax?]

private theorem high_le_maxWith {tree : Tree} (cache : tree.CacheInvariant)
    {stored : Entry} (member : stored ∈ tree.entries) (fallback : Int) :
    stored.interval.high ≤ maxWith fallback tree.cachedMax? := by
  cases tree with
  | empty => simp [entries] at member
  | node height size maxHigh left entry right =>
      exact le_trans (cache.2.2.1 stored member) (le_max_right _ _)

private theorem maxWith_attained {tree : Tree} (cache : tree.CacheInvariant)
    (fallback : Int) :
    maxWith fallback tree.cachedMax? = fallback ∨
      ∃ stored ∈ tree.entries,
        stored.interval.high = maxWith fallback tree.cachedMax? := by
  cases tree with
  | empty => exact Or.inl rfl
  | node height size maxHigh left entry right =>
      by_cases bounded : maxHigh ≤ fallback
      · exact Or.inl (max_eq_left bounded)
      · rcases cache.2.2.2.1 with ⟨stored, member, attained⟩
        exact Or.inr ⟨stored, member, by
          simpa only [cachedMax?, maxWith, max_eq_right (le_of_not_ge bounded)] using
            attained⟩

/-- The smart constructor preserves recursively attained maximum caches. -/
theorem cacheInvariant_mkNode {left right : Tree} (entry : Entry)
    (leftCache : left.CacheInvariant) (rightCache : right.CacheInvariant) :
    (mkNode left entry right).CacheInvariant := by
  refine ⟨leftCache, rightCache, ?_, ?_, rfl, rfl⟩
  · intro stored member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with inLeft | atRoot | inRight
    · exact le_trans (high_le_maxWith leftCache inLeft entry.interval.high)
        (le_maxWith _ right)
    · subst stored
      exact le_trans (le_maxWith entry.interval.high left) (le_maxWith _ right)
    · exact high_le_maxWith rightCache inRight _
  · rcases maxWith_attained rightCache (maxWith entry.interval.high left.cachedMax?) with
      rootOrLeft | ⟨stored, member, attained⟩
    · rcases maxWith_attained leftCache entry.interval.high with
        atRoot | ⟨stored, member, attained⟩
      · exact ⟨entry, by simp, (rootOrLeft.trans atRoot).symm⟩
      · exact ⟨stored, by simp [member], attained.trans rootOrLeft.symm⟩
    · exact ⟨stored, by simp [member], attained⟩

/-- A successful executable metadata check supplies the recursive cache invariant. -/
theorem cacheInvariant_of_cacheOK {tree : Tree} (checked : tree.cacheOK = true) :
    tree.CacheInvariant := by
  induction tree with
  | empty => trivial
  | node height size maxHigh left entry right leftIH rightIH =>
      simp only [cacheOK, Bool.and_eq_true, beq_iff_eq] at checked
      have leftOK : left.cacheOK = true := checked.1.2
      have rightOK : right.cacheOK = true := checked.2
      have maximum : maxHigh = nodeMax left entry right := checked.1.1.2
      have heightEq : height = max left.height right.height + 1 := checked.1.1.1.1
      have sizeEq : size = left.size + right.size + 1 := checked.1.1.1.2
      have rebuilt := cacheInvariant_mkNode entry (leftIH leftOK) (rightIH rightOK)
      simpa only [mkNode, CacheInvariant, maximum, ← heightEq, ← sizeEq] using rebuilt

/-- A right rotation preserves attained maximum caches. -/
theorem cacheInvariant_rotateRight {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateRight.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases left with
      | empty => exact cache
      | node leftHeight leftSize leftMaximum a x b =>
          exact cacheInvariant_mkNode x cache.1.1
            (cacheInvariant_mkNode entry cache.1.2.1 cache.2.1)

/-- A left rotation preserves attained maximum caches. -/
theorem cacheInvariant_rotateLeft {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateLeft.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases right with
      | empty => exact cache
      | node rightHeight rightSize rightMaximum b y c =>
          exact cacheInvariant_mkNode y
            (cacheInvariant_mkNode entry cache.1 cache.2.1.1) cache.2.1.2.1

/-- A left-right rotation preserves attained maximum caches. -/
theorem cacheInvariant_rotateLeftRight {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateLeftRight.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases left with
      | empty => exact cache
      | node leftHeight leftSize leftMaximum a x middle =>
          cases middle with
          | empty => exact cache
          | node middleHeight middleSize middleMaximum b y c =>
              exact cacheInvariant_mkNode y
                (cacheInvariant_mkNode x cache.1.1 cache.1.2.1.1)
                (cacheInvariant_mkNode entry cache.1.2.1.2.1 cache.2.1)

/-- A right-left rotation preserves attained maximum caches. -/
theorem cacheInvariant_rotateRightLeft {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rotateRightLeft.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      cases right with
      | empty => exact cache
      | node rightHeight rightSize rightMaximum middle z d =>
          cases middle with
          | empty => exact cache
          | node middleHeight middleSize middleMaximum b y c =>
              exact cacheInvariant_mkNode y
                (cacheInvariant_mkNode entry cache.1 cache.2.1.1.1)
                (cacheInvariant_mkNode z cache.2.1.1.2.1 cache.2.1.2.1)

/-- Rebalancing preserves attained maximum caches on every selected branch. -/
theorem cacheInvariant_rebalanceWithCost {tree : Tree} (cache : tree.CacheInvariant) :
    tree.rebalanceWithCost.1.CacheInvariant := by
  cases tree with
  | empty => exact cache
  | node height size maximum left entry right =>
      by_cases leftHeavy : left.height > right.height + 1
      · simp only [rebalanceWithCost, ite_eq_left leftHeavy]
        cases left with
        | empty => exact cache
        | node leftHeight leftSize leftMaximum ll x lr =>
            dsimp only
            split
            · exact cacheInvariant_rotateRight cache
            · exact cacheInvariant_rotateLeftRight cache
      · simp only [rebalanceWithCost, ite_eq_right leftHeavy]
        by_cases rightHeavy : right.height > left.height + 1
        · simp only [ite_eq_left rightHeavy]
          cases right with
          | empty => exact cache
          | node rightHeight rightSize rightMaximum rl x rr =>
              dsimp only
              split
              · exact cacheInvariant_rotateLeft cache
              · exact cacheInvariant_rotateRightLeft cache
        · simpa only [ite_eq_right rightHeavy] using cache

/-- Key insertion preserves attained maximum caches, including replacement. -/
theorem cacheInvariant_insertKeyWithCost (newEntry : Entry) {tree : Tree}
    (cache : tree.CacheInvariant) :
    (tree.insertKeyWithCost newEntry).1.CacheInvariant := by
  induction tree with
  | empty => exact cacheInvariant_mkNode newEntry trivial trivial
  | node height size maximum left entry right leftIH rightIH =>
      unfold insertKeyWithCost
      split
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry (leftIH cache.1) cache.2.1)
      · exact cacheInvariant_mkNode newEntry cache.1 cache.2.1
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry cache.1 (rightIH cache.2.1))

/-- Removing the minimum preserves attained maximum caches in the returned tree. -/
theorem cacheInvariant_removeMinWithCost {tree : Tree} (cache : tree.CacheInvariant) :
    ∀ {minimum : Entry} {result : Tree} {cost : Cost},
      tree.removeMinWithCost = some (minimum, result, cost) → result.CacheInvariant := by
  induction tree with
  | empty =>
      intro minimum result cost returned
      simp only [removeMinWithCost, reduceCtorEq] at returned
  | node height size maximum left entry right leftIH rightIH =>
      intro minimum result cost returned
      cases left with
      | empty =>
          change some (entry, right, ({ nodeVisits := 1 } : Cost)) =
            some (minimum, result, cost) at returned
          cases returned
          exact cache.2.1
      | node leftHeight leftSize leftMaximum a x b =>
          unfold removeMinWithCost at returned
          split at returned
          · contradiction
          · rename_i removed newLeft childCost recursive
            cases returned
            exact cacheInvariant_rebalanceWithCost
              (cacheInvariant_mkNode entry (leftIH cache.1 recursive) cache.2.1)

/-- Key deletion preserves attained maximum caches, including absent keys. -/
theorem cacheInvariant_eraseKeyWithCost (key : Int × Nat) {tree : Tree}
    (cache : tree.CacheInvariant) : (tree.eraseKeyWithCost key).1.CacheInvariant := by
  induction tree with
  | empty => exact cache
  | node height size maximum left entry right leftIH rightIH =>
      unfold eraseKeyWithCost
      split
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry (leftIH cache.1) cache.2.1)
      · exact cacheInvariant_rebalanceWithCost
          (cacheInvariant_mkNode entry cache.1 (rightIH cache.2.1))
      · split
        · exact cache.1
        · rename_i successor newRight childCost removed
          exact cacheInvariant_rebalanceWithCost
            (cacheInvariant_mkNode successor cache.1
              (cacheInvariant_removeMinWithCost cache.2.1 removed))

end Cslib.Algorithms.Lean.IntervalTree.Tree

namespace Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree

/-- The executable checker is sound for the bundled invariant. -/
theorem invariant_of_check {tree : IndexedIntervalTree}
    (h : tree.check = true) : tree.Invariant := by
  simp only [check, Bool.and_eq_true] at h
  have hcache := h.1.1.1.1.1
  have hbal := h.1.1.1.1.2
  have hord := h.1.1.1.2
  have huniq := h.1.1.2
  have hfwd := h.1.2
  have hbwd := h.2
  refine ⟨Tree.cacheInvariant_of_cacheOK hcache,
    (Tree.keyOrdered_of_orderedValid hord).1,
    Tree.balancedProp_of_balanced hbal,
    Tree.validInvariant_of_orderedValid hord, ?_, ?_, ?_⟩
  · simpa [Tree.uniqueIds] using huniq
  · intro e he
    have := List.all_eq_true.mp hfwd e he
    simpa using this
  · intro p hp
    have := List.all_eq_true.mp hbwd p hp
    simp only [List.any_eq_true] at this
    obtain ⟨e, he, hboth⟩ := this
    simp only [Bool.and_eq_true, beq_iff_eq] at hboth
    exact ⟨e, he, hboth.1, hboth.2⟩

theorem empty_invariant : Invariant empty := by
  refine ⟨trivial, trivial, trivial, trivial, by decide, ?_, ?_⟩
  · intro e he
    change e ∈ ([] : List Entry) at he
    cases he
  · intro p hp
    change p ∈ ([] : List (Nat × Int)) at hp
    cases hp

/-- Public search soundness.  This holds for every indexed tree: the
bundled invariant is not needed, only the successful search equation. -/
theorem search_sound {tree : IndexedIntervalTree}
    {query : Interval} {found : Entry}
    (h : tree.search query = some found) :
    found ∈ tree.root.entries ∧ found.interval.Overlaps query := by
  have hroot : tree.root.search query = some found := by
    by_cases hv : query.valid
    · have : tree.search query = tree.root.search query := by
        simp [search, searchWithCost, hv, Tree.searchWithCost_fst]
      rwa [this] at h
    · simp [search, searchWithCost, hv] at h
  have hsound := Tree.search_sound hroot
  exact ⟨hsound.1, Interval.overlaps_eq_true.mp hsound.2⟩

/-- Public search completeness from the bundled invariant, for valid
queries: every overlapping stored occurrence is found. -/
theorem search_complete_of_invariant {tree : IndexedIntervalTree}
    (inv : tree.Invariant) {query : Interval} (hvalid : query.valid = true)
    {witness : Entry} (member : witness ∈ tree.root.entries)
    (overlap : witness.interval.Overlaps query) :
    ∃ found, tree.search query = some found := by
  rcases Tree.search_complete inv.1 (Tree.keyOrdered_lowOrdered inv.2.1)
    member overlap with ⟨found, hfound⟩
  refine ⟨found, ?_⟩
  have : tree.search query = tree.root.search query := by
    simp [search, searchWithCost, hvalid, Tree.searchWithCost_fst]
  rwa [this]

private theorem get?_insert_self (m : Std.TreeMap Nat Int) (k : Nat)
    (v : Int) : (m.insert k v).get? k = some v :=
  Std.TreeMap.getElem?_insert_self

private theorem get?_insert_of_ne {m : Std.TreeMap Nat Int} {k a : Nat}
    (h : k ≠ a) (v : Int) : (m.insert k v).get? a = m.get? a := by
  change (m.insert k v)[a]? = m[a]?
  rw [Std.TreeMap.getElem?_insert]
  simp [h]

private theorem get?_erase_of_ne {m : Std.TreeMap Nat Int} {k a : Nat}
    (h : k ≠ a) : (m.erase k).get? a = m.get? a := by
  change (m.erase k)[a]? = m[a]?
  rw [Std.TreeMap.getElem?_erase]
  simp [h]

private theorem mem_toList_iff_get? {m : Std.TreeMap Nat Int}
    {p : Nat × Int} : p ∈ m.toList ↔ m.get? p.1 = some p.2 :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- One insertion stage: inserting a valid entry whose identifier is
absent from a tree satisfying the tree-level invariants and the index
correspondence yields a tree satisfying the bundled invariant, contains
the new entry, and otherwise retains exactly the old entries. -/
private theorem insert_stage {root : Tree} {index : Std.TreeMap Nat Int}
    {entry : Entry}
    (hcache : root.CacheInvariant) (hord : root.KeyOrdered)
    (hbal : root.BalancedProp) (hval : root.ValidInvariant)
    (hnoid : (root.entries.map (·.id)).Nodup)
    (hfwd : ∀ e ∈ root.entries, index.get? e.id = some e.interval.low)
    (hbwd : ∀ p ∈ index.toList, p.1 ≠ entry.id →
      ∃ e ∈ root.entries, e.id = p.1 ∧ e.interval.low = p.2)
    (hvalidProp : entry.interval.Valid)
    (habsent : ∀ e ∈ root.entries, e.id ≠ entry.id) :
    (⟨(root.insertKeyWithCost entry).1,
      index.insert entry.id entry.interval.low⟩ :
        IndexedIntervalTree).Invariant ∧
      entry ∈ (root.insertKeyWithCost entry).1.entries ∧
      ∀ e, e ∈ (root.insertKeyWithCost entry).1.entries ↔
        e = entry ∨ (e ∈ root.entries ∧ e.id ≠ entry.id) := by
  have hkeyNodup : (root.entries.map Entry.key).Nodup :=
    Tree.keyNodup_of_keyOrdered hord
  have hmem : ∀ e, e ∈ (root.insertKeyWithCost entry).1.entries ↔
      e = entry ∨ (e ∈ root.entries ∧ e.key ≠ entry.key) :=
    fun e => Tree.mem_insertKeyWithCost entry e hkeyNodup hord
  have hperm := Tree.insertKeyWithCost_entries_perm entry hord
  have hfilterNodup :
      ((root.entries.filter (fun e => e.key ≠ entry.key)).map (·.id)).Nodup :=
    (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
  have hnoid' :
      ((root.insertKeyWithCost entry).1.entries.map (·.id)).Nodup := by
    apply (hperm.map (·.id)).nodup_iff.mpr
    rw [List.map_cons]
    apply List.nodup_cons.mpr
    refine ⟨fun hmem => ?_, hfilterNodup⟩
    rw [List.mem_map] at hmem
    obtain ⟨e, he, hid⟩ := hmem
    rw [List.mem_filter] at he
    exact habsent e he.1 hid
  refine ⟨⟨Tree.cacheInvariant_insertKeyWithCost entry hcache,
    Tree.keyOrdered_insertKeyWithCost entry hord,
    (Tree.balancedProp_insertKeyWithCost entry hbal).1,
    Tree.validInvariant_insertKeyWithCost entry hvalidProp hval,
    hnoid', ?_, ?_⟩, (hmem entry).mpr (Or.inl rfl), ?_⟩
  · intro e he
    rcases (hmem e).mp he with heq | ⟨hem, _⟩
    · rw [heq]
      exact get?_insert_self index entry.id entry.interval.low
    · rw [get?_insert_of_ne (k := entry.id)
        (Ne.symm (habsent e hem)) entry.interval.low]
      exact hfwd e hem
  · intro p hp
    have hpget : (index.insert entry.id entry.interval.low).get? p.1 =
        some p.2 := mem_toList_iff_get?.mp hp
    by_cases hpe : p.1 = entry.id
    · have hlow : p.2 = entry.interval.low := by
        rw [hpe, get?_insert_self] at hpget
        exact Option.some.inj hpget.symm
      exact ⟨entry, (hmem entry).mpr (Or.inl rfl), hpe.symm, hlow.symm⟩
    · have hold : index.get? p.1 = some p.2 := by
        rw [← get?_insert_of_ne (k := entry.id) (Ne.symm hpe)
          entry.interval.low]
        exact hpget
      obtain ⟨e, he, hid, hlow⟩ :=
        hbwd p (mem_toList_iff_get?.mpr hold) hpe
      refine ⟨e, (hmem e).mpr (Or.inr ⟨he, ?_⟩), hid, hlow⟩
      intro hk
      apply hpe
      have h2 := congrArg Prod.snd hk
      exact hid.symm.trans h2
  · intro e
    constructor
    · intro he
      rcases (hmem e).mp he with rfl | ⟨hem, _⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hem, habsent e hem⟩
    · intro he
      rcases he with heq | ⟨hem, hidne⟩
      · rw [heq]
        exact (hmem entry).mpr (Or.inl rfl)
      · apply (hmem e).mpr
        exact Or.inr ⟨hem, fun hk => hidne (congrArg Prod.snd hk)⟩

/-- Successful public insertion preserves the bundled invariant, stores
the new entry, and otherwise retains exactly the previously stored
entries (an existing entry with the same identifier is replaced). -/
theorem insert_spec {tree : IndexedIntervalTree} (inv : tree.Invariant)
    {entry : Entry} (hvalid : entry.interval.valid = true)
    {result : IndexedIntervalTree} (hres : tree.insert entry = some result) :
    result.Invariant ∧ entry ∈ result.root.entries ∧
      ∀ e, e ∈ result.root.entries ↔
        e = entry ∨ (e ∈ tree.root.entries ∧ e.id ≠ entry.id) := by
  obtain ⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩ := inv
  have hvalidProp : entry.interval.Valid :=
    @of_decide_eq_true _ (Int.decLe _ _) (by
      have h2 : entry.interval.valid = true := hvalid
      unfold Interval.valid at h2
      exact h2)
  cases hget : tree.idIndex.get? entry.id with
  | none =>
      have hresult : result = ⟨(tree.root.insertKeyWithCost entry).1,
          tree.idIndex.insert entry.id entry.interval.low⟩ := by
        have h1 : tree.insert entry =
            some ⟨(tree.root.insertKeyWithCost entry).1,
              tree.idIndex.insert entry.id entry.interval.low⟩ := by
          simp only [insert, insertWithCost, hvalid, hget, ite_true]
        rw [h1] at hres
        exact (Option.some.inj hres).symm
      subst hresult
      exact insert_stage hcache hord hbal hval hnoid hfwd
        (fun p hp _ => hbwd p hp) hvalidProp
        (fun e he hid => by
          have h1 := hfwd e he
          rw [hid, hget] at h1
          simp at h1)
  | some oldLow =>
      have hresult : result =
          ⟨((tree.root.eraseKeyWithCost (oldLow, entry.id)).1
              |>.insertKeyWithCost entry).1,
            tree.idIndex.insert entry.id entry.interval.low⟩ := by
        have h1 : tree.insert entry =
            some ⟨((tree.root.eraseKeyWithCost (oldLow, entry.id)).1
                |>.insertKeyWithCost entry).1,
              tree.idIndex.insert entry.id entry.interval.low⟩ := by
          simp only [insert, insertWithCost, hvalid, hget, ite_true]
        rw [h1] at hres
        exact (Option.some.inj hres).symm
      subst hresult
      have hkeyNodup : (tree.root.entries.map Entry.key).Nodup :=
        Tree.keyNodup_of_keyOrdered hord
      have hpermW := Tree.eraseKeyWithCost_entries_perm (oldLow, entry.id) hord
      have hnoidW :
          ((tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries.map
            (·.id)).Nodup := by
        apply (hpermW.map (·.id)).nodup_iff.mpr
        exact (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
      have hfwdW : ∀ e ∈ (tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries,
          tree.idIndex.get? e.id = some e.interval.low :=
        fun e he => hfwd e (Tree.mem_eraseKeyWithCost_of_mem _ e _ he)
      have hmemW : ∀ e,
          e ∈ (tree.root.eraseKeyWithCost (oldLow, entry.id)).1.entries ↔
          e ∈ tree.root.entries ∧ e.key ≠ (oldLow, entry.id) :=
        fun e => Tree.mem_eraseKeyWithCost (oldLow, entry.id) e hkeyNodup hord
      obtain ⟨hinv, hmemEntry, hothers⟩ := insert_stage
        (Tree.cacheInvariant_eraseKeyWithCost (oldLow, entry.id) hcache)
        (Tree.keyOrdered_eraseKeyWithCost (oldLow, entry.id) hord)
        (Tree.balancedProp_eraseKeyWithCost (oldLow, entry.id) hbal).1
        (Tree.validInvariant_eraseKeyWithCost (oldLow, entry.id) hval)
        hnoidW hfwdW
        (fun p hp hpe => by
          obtain ⟨e, he, hid, hlow⟩ := hbwd p hp
          refine ⟨e, (hmemW e).mpr ⟨he, ?_⟩, hid, hlow⟩
          intro hk
          apply hpe
          have h2 := congrArg Prod.snd hk
          exact hid.symm.trans h2)
        hvalidProp
        (fun e he hid => by
          have hem := (hmemW e).mp he
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = oldLow := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (oldLow, entry.id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩))
      refine ⟨hinv, hmemEntry, fun e => ?_⟩
      constructor
      · intro he
        rcases (hothers e).mp he with rfl | ⟨hew, hidne⟩
        · exact Or.inl rfl
        · exact Or.inr
            ⟨Tree.mem_eraseKeyWithCost_of_mem _ e _ hew, hidne⟩
      · intro he
        apply (hothers e).mpr
        rcases he with rfl | ⟨heT, hidne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨(hmemW e).mpr
            ⟨heT, fun hk => hidne (congrArg Prod.snd hk)⟩, hidne⟩

/-- Public erasure preserves the bundled invariant and deletes exactly
the occurrence with the given identifier; absent identifiers leave the
stored entries unchanged. -/
theorem erase_spec {tree : IndexedIntervalTree} (inv : tree.Invariant)
    (id : Nat) :
    (tree.erase id).Invariant ∧
      ∀ e, e ∈ (tree.erase id).root.entries ↔
        e ∈ tree.root.entries ∧ e.id ≠ id := by
  obtain ⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩ := inv
  have hkeyNodup : (tree.root.entries.map Entry.key).Nodup :=
    Tree.keyNodup_of_keyOrdered hord
  cases hget : tree.idIndex.get? id with
  | none =>
      have hte : tree.erase id = tree := by
        unfold erase eraseWithCost
        rw [hget]
      rw [hte]
      refine ⟨⟨hcache, hord, hbal, hval, hnoid, hfwd, hbwd⟩, ?_⟩
      intro e
      constructor
      · intro he
        refine ⟨he, ?_⟩
        intro hid
        have h1 := hfwd e he
        rw [hid, hget] at h1
        simp at h1
      · intro he
        exact he.1
  | some low =>
      have hte : tree.erase id =
          ⟨(tree.root.eraseKeyWithCost (low, id)).1,
            tree.idIndex.erase id⟩ := by
        unfold erase eraseWithCost
        rw [hget]
      rw [hte]
      have hmem : ∀ e, e ∈ (tree.root.eraseKeyWithCost (low, id)).1.entries ↔
          e ∈ tree.root.entries ∧ e.key ≠ (low, id) :=
        fun e => Tree.mem_eraseKeyWithCost (low, id) e hkeyNodup hord
      have hperm := Tree.eraseKeyWithCost_entries_perm (low, id) hord
      have hnoid' :
          ((tree.root.eraseKeyWithCost (low, id)).1.entries.map (·.id)).Nodup := by
        apply (hperm.map (·.id)).nodup_iff.mpr
        exact (List.filter_sublist.map (fun e : Entry => e.id)).nodup hnoid
      have hkeyne : ∀ e ∈ tree.root.entries, e.id ≠ id →
          e.key ≠ (low, id) := by
        intro e _ hne hk
        exact hne (congrArg Prod.snd hk)
      refine ⟨⟨Tree.cacheInvariant_eraseKeyWithCost (low, id) hcache,
        Tree.keyOrdered_eraseKeyWithCost (low, id) hord,
        (Tree.balancedProp_eraseKeyWithCost (low, id) hbal).1,
        Tree.validInvariant_eraseKeyWithCost (low, id) hval,
        hnoid', ?_, ?_⟩, ?_⟩
      · intro e he
        have hem := (hmem e).mp he
        have hne : e.id ≠ id := by
          intro hid
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = low := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (low, id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩)
        rw [get?_erase_of_ne (k := id) (Ne.symm hne)]
        exact hfwd e hem.1
      · intro p hp
        have hpget : (tree.idIndex.erase id).get? p.1 = some p.2 :=
          mem_toList_iff_get?.mp hp
        have hne : id ≠ p.1 := by
          intro hid
          have h1 : (tree.idIndex.erase id).get? p.1 = none := by
            change (tree.idIndex.erase id)[p.1]? = none
            rw [Std.TreeMap.getElem?_erase]
            simp [hid]
          rw [h1] at hpget
          simp at hpget
        have hold : tree.idIndex.get? p.1 = some p.2 := by
          rw [← get?_erase_of_ne (k := id) hne]
          exact hpget
        obtain ⟨e, he, hid, hlow⟩ :=
          hbwd p (mem_toList_iff_get?.mpr hold)
        refine ⟨e, (hmem e).mpr ⟨he, ?_⟩, hid, hlow⟩
        apply hkeyne e he
        intro hid2
        exact hne (hid2.symm.trans hid)
      · intro e
        constructor
        · intro he
          have hem := (hmem e).mp he
          refine ⟨hem.1, ?_⟩
          intro hid
          have h1 := hfwd e hem.1
          rw [hid, hget] at h1
          have hlow : e.interval.low = low := (Option.some.inj h1).symm
          exact hem.2 (by
            show e.key = (low, id)
            rw [Prod.ext_iff]
            exact ⟨hlow, hid⟩)
        · intro he
          exact (hmem e).mpr ⟨he.1, hkeyne e he.1 he.2⟩

end Cslib.Algorithms.Lean.IntervalTree.IndexedIntervalTree
