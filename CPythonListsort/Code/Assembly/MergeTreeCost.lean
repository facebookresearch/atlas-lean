/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.AccessTrace
import Code.Assembly.MergeCost

/-!
# Logical merge replay and final-collapse cost dominance

`MergeCost` defines the paper-facing merge tree, merge cost, weighted path
length, and their exact equality.  This module adds two pure pieces needed by
the implementation bridge:

* checked replay of the raw, pre-trim logical merge observations; and
* the exact length-and-cost semantics of CPython's `merge_force_collapse`,
  together with a proof that it costs no more than Algorithm 2's canonical
  top-pair completion.

The paper's Algorithm 2 always merges the top pair in its final loop.  CPython
has one additional branch: for a final triple `A, B, C`, it merges `A` with
`B` when `|A| < |C|`.  This is a cost-nonincreasing local tree rotation, not a
tree-equality fact.
-/

namespace CPythonListsort

/-! ## Checked replay of logical pre-trim merges -/

namespace RunSpan

/-- The first index after a run span. -/
def endIndex (span : RunSpan) : Nat :=
  span.base + span.len

/-- The right span begins exactly where the left span ends. -/
def Adjacent (left right : RunSpan) : Prop :=
  left.endIndex = right.base

instance (left right : RunSpan) : Decidable (Adjacent left right) :=
  inferInstanceAs (Decidable (left.endIndex = right.base))

/-- The span produced by a logical merge of two adjacent runs. -/
def merge (left right : RunSpan) : RunSpan :=
  { base := left.base, len := left.len + right.len }

end RunSpan

/-- A merge tree paired with the source interval occupied by its root. -/
structure SpannedMergeTree where
  span : RunSpan
  tree : MergeTree
  deriving DecidableEq, Repr

namespace SpannedMergeTree

/-- The tree's leaf weights account for exactly the paired source span. -/
def Valid (entry : SpannedMergeTree) : Prop :=
  entry.tree.totalLength = entry.span.len

/-- Initial forest entry for one implementation-formed run. -/
def leaf (span : RunSpan) : SpannedMergeTree :=
  { span := span, tree := .leaf span.len }

/-- Logical combination of two adjacent forest entries.  The supplied power
is a semantic label only and does not affect merge-cost accounting. -/
def merge (power : Nat) (left right : SpannedMergeTree) : SpannedMergeTree :=
  { span := left.span.merge right.span
    tree := .merge power left.tree right.tree }

@[simp]
theorem leaf_valid (span : RunSpan) : (leaf span).Valid := by
  simp [Valid, leaf, MergeTree.totalLength]

theorem merge_valid (power : Nat) {left right : SpannedMergeTree}
    (hleft : left.Valid) (hright : right.Valid) :
    (merge power left right).Valid := by
  simp only [Valid] at hleft hright ⊢
  simp only [merge, MergeTree.totalLength, RunSpan.merge]
  omega

end SpannedMergeTree

/-- A logical merge observation paired with the node-power label used in the
paper-facing tree.  The implementation trace supplies the raw event; the
PowerSort bridge supplies and verifies the label. -/
structure PoweredMergeReplayStep where
  event : LogicalMergeEvent
  power : Nat
  deriving DecidableEq, Repr

/-- Apply one checked logical merge to an ordered forest.  Replay verifies the
selected index, both historical pre-trim spans, and their adjacency before
constructing an internal node. -/
def applyPoweredMergeReplayStep? (forest : List SpannedMergeTree)
    (step : PoweredMergeReplayStep) : Option (List SpannedMergeTree) := do
  let left ← forest[step.event.index]?
  let right ← forest[step.event.index + 1]?
  if left.span = step.event.left ∧ right.span = step.event.right ∧
      step.event.left.Adjacent step.event.right then
    pure (forest.take step.event.index ++
      [left.merge step.power right] ++ forest.drop (step.event.index + 2))
  else
    none

/-- Replay chronological logical merge observations. -/
def replayPoweredMergeSteps? :
    List SpannedMergeTree → List PoweredMergeReplayStep →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, step :: steps => do
      let forest ← applyPoweredMergeReplayStep? forest step
      replayPoweredMergeSteps? forest steps

/-- A powered chronological trace completely merges the supplied formed runs
into the displayed result. -/
def CompleteMergeReplay (initial : List RunSpan)
    (steps : List PoweredMergeReplayStep) (result : SpannedMergeTree) : Prop :=
  replayPoweredMergeSteps? (initial.map .leaf) steps = some [result]

/-! ## Paper top-pair completion -/

/-- Every run length in a pending forest is positive. -/
def PositiveRunLengths (lengths : List Nat) : Prop :=
  ∀ length ∈ lengths, 0 < length

/-- Cost of Algorithm 2's final loop, which repeatedly merges the top two
pending runs.  Equivalently, this is the cost of the right-associated tree on
the listed open-subtree lengths. -/
def topPairCompletionCost : List Nat → Nat
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      first + (second :: rest).sum +
        topPairCompletionCost (second :: rest)

/-- The chronological internal-node costs paid by Algorithm 2's final loop.

The recursive definition of `topPairCompletionCost` is written from the
oldest root outward; execution merges the newest pair first, so the current
whole-forest cost is appended after the recursive suffix schedule. -/
def topPairCompletionMergeCosts : List Nat → List Nat
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      topPairCompletionMergeCosts (second :: rest) ++
        [(first :: second :: rest).sum]

/-- The explicit canonical completion schedule sums to its scalar cost. -/
theorem topPairCompletionMergeCosts_sum : ∀ lengths : List Nat,
    (topPairCompletionMergeCosts lengths).sum =
      topPairCompletionCost lengths
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest => by
      rw [topPairCompletionMergeCosts, List.sum_append,
        topPairCompletionMergeCosts_sum]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero,
        topPairCompletionCost]
      omega

private theorem topPairCompletionCost_cons_of_ne_nil
    (first : Nat) {rest : List Nat} (hrest : rest ≠ []) :
    topPairCompletionCost (first :: rest) =
      first + rest.sum + topPairCompletionCost rest := by
  cases rest with
  | nil => contradiction
  | cons second tail => rfl

/-- Adding a common prefix preserves a cost comparison between nonempty
suffixes of equal total length, including an already-paid local merge cost. -/
private theorem topPairCompletionCost_prefix_add_le
    (before : List Nat) {left right : List Nat} (extra : Nat)
    (hleft : left ≠ []) (hright : right ≠ [])
    (hsum : left.sum = right.sum)
    (hcost : extra + topPairCompletionCost left ≤
      topPairCompletionCost right) :
    extra + topPairCompletionCost (before ++ left) ≤
      topPairCompletionCost (before ++ right) := by
  induction before with
  | nil => simpa using hcost
  | cons first before ih =>
      have hbeforeLeft : before ++ left ≠ [] := by simp [hleft]
      have hbeforeRight : before ++ right ≠ [] := by simp [hright]
      change
        extra + topPairCompletionCost (first :: (before ++ left)) ≤
          topPairCompletionCost (first :: (before ++ right))
      rw [topPairCompletionCost_cons_of_ne_nil first hbeforeLeft,
        topPairCompletionCost_cons_of_ne_nil first hbeforeRight]
      have ih' := ih
      simp only [List.sum_append, hsum] at ih' ⊢
      omega

/-- Paying for the top-pair merge and then completing is exactly the
canonical top-pair completion cost. -/
theorem topPairCompletionCost_merge_top (before : List Nat) (left right : Nat) :
    left + right + topPairCompletionCost (before ++ [left + right]) =
      topPairCompletionCost (before ++ [left, right]) := by
  induction before with
  | nil => simp [topPairCompletionCost]
  | cons first before ih =>
      have hmerged : before ++ [left + right] ≠ [] := by simp
      have hpair : before ++ [left, right] ≠ [] := by simp
      change
        left + right +
            topPairCompletionCost (first :: (before ++ [left + right])) =
          topPairCompletionCost (first :: (before ++ [left, right]))
      rw [topPairCompletionCost_cons_of_ne_nil first hmerged,
        topPairCompletionCost_cons_of_ne_nil first hpair]
      simp only [List.sum_append, List.sum_cons, List.sum_nil]
      omega

/-- CPython's third-last choice is the tree rotation
`A + (B + C) -> (A + B) + C`.  Under its exact guard `|A| < |C|`, paying for
that rotation and then canonically completing cannot cost more than the
paper's top-pair completion. -/
theorem topPairCompletionCost_merge_thirdLast_le (before : List Nat)
    (a b c : Nat) (hselect : a < c) :
    a + b + topPairCompletionCost (before ++ [a + b, c]) ≤
      topPairCompletionCost (before ++ [a, b, c]) := by
  apply topPairCompletionCost_prefix_add_le before (extra := a + b)
  · simp
  · simp
  · simp
    omega
  · simp [topPairCompletionCost]
    omega

/-! ## CPython final-collapse cost relation -/

/-- Source-faithful length-and-cost semantics of `merge_force_collapse`.

For at least three pending runs, `a`, `b`, and `c` are the final three lengths.
The strict source guard chooses the third-last pair exactly when `a < c`;
otherwise the top pair is merged. -/
inductive CPythonForceCollapseCost : List Nat → Nat → Prop
  | empty : CPythonForceCollapseCost [] 0
  | singleton (length : Nat) : CPythonForceCollapseCost [length] 0
  | pair (left right : Nat) :
      CPythonForceCollapseCost [left, right] (left + right)
  | mergeTop (before : List Nat) (a b c tailCost : Nat)
      (hselect : ¬a < c)
      (tail : CPythonForceCollapseCost (before ++ [a, b + c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (b + c + tailCost)
  | mergeThirdLast (before : List Nat) (a b c tailCost : Nat)
      (hselect : a < c)
      (tail : CPythonForceCollapseCost (before ++ [a + b, c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (a + b + tailCost)

/-- Any collapse relation on at most one pending run has exact cost zero. -/
theorem CPythonForceCollapseCost.cost_eq_zero_of_length_le_one
    {lengths : List Nat} {cost : Nat}
    (hcollapse : CPythonForceCollapseCost lengths cost)
    (hlength : lengths.length ≤ 1) : cost = 0 := by
  induction hcollapse with
  | empty => rfl
  | singleton => rfl
  | pair left right => simp at hlength
  | mergeTop before a b c tailCost hselect tail ih =>
      simp at hlength
  | mergeThirdLast before a b c tailCost hselect tail ih =>
      simp at hlength

/-- Exact endpoint inversion: collapsing an empty stack has cost zero. -/
theorem CPythonForceCollapseCost.empty_cost_eq_zero {cost : Nat}
    (hcollapse : CPythonForceCollapseCost [] cost) : cost = 0 :=
  hcollapse.cost_eq_zero_of_length_le_one (by simp)

/-- Exact endpoint inversion: a singleton stack performs no merge. -/
theorem CPythonForceCollapseCost.singleton_cost_eq_zero
    {length cost : Nat}
    (hcollapse : CPythonForceCollapseCost [length] cost) : cost = 0 :=
  hcollapse.cost_eq_zero_of_length_le_one (by simp)

/-- CPython's complete final-collapse cost never exceeds Algorithm 2's
canonical top-pair completion cost on the same open-forest lengths. -/
theorem CPythonForceCollapseCost.le_topPairCompletionCost
    {lengths : List Nat} {cost : Nat}
    (hcollapse : CPythonForceCollapseCost lengths cost) :
    cost ≤ topPairCompletionCost lengths := by
  induction hcollapse with
  | empty => simp [topPairCompletionCost]
  | singleton length => simp [topPairCompletionCost]
  | pair left right => simp [topPairCompletionCost]
  | mergeTop before a b c tailCost hselect tail ih =>
      calc
        b + c + tailCost ≤
            b + c + topPairCompletionCost (before ++ [a, b + c]) := by
              omega
        _ = topPairCompletionCost (before ++ [a, b, c]) := by
          simpa [List.append_assoc] using
            topPairCompletionCost_merge_top (before ++ [a]) b c
  | mergeThirdLast before a b c tailCost hselect tail ih =>
      calc
        a + b + tailCost ≤
            a + b + topPairCompletionCost (before ++ [a + b, c]) := by
              omega
        _ ≤ topPairCompletionCost (before ++ [a, b, c]) :=
          topPairCompletionCost_merge_thirdLast_le before a b c hselect

/-- Source-domain corollary with the positive-run premise used by actual
pending stacks. -/
theorem cpythonForceCollapseCost_le_topPairCompletionCost
    {lengths : List Nat} {cost : Nat}
    (_hpositive : PositiveRunLengths lengths)
    (hcollapse : CPythonForceCollapseCost lengths cost) :
    cost ≤ topPairCompletionCost lengths :=
  hcollapse.le_topPairCompletionCost

/-! ## Exact branch-and-cost regression -/

/-- Kernel-checked regression for the reviewed adaptive-minrun counterexample
to literal final-tree equality.  The scan has already paid 213 and leaves
open-subtree lengths `[148, 36, 32, 32, 8]`.  Paper top-pair completion totals
476, whereas CPython's strict third-last branch lowers it to 472, giving
complete costs 689 and 685. -/
theorem forceCollapse_rotation_cost_regression :
    topPairCompletionCost [148, 36, 32, 32, 8] = 476 ∧
      CPythonForceCollapseCost [148, 36, 32, 32, 8] 472 ∧
      213 + 476 = 689 ∧
      213 + 472 = 685 := by
  refine ⟨by norm_num [topPairCompletionCost], ?_, by norm_num, by norm_num⟩
  apply CPythonForceCollapseCost.mergeTop [148, 36] 32 32 8 432
  · norm_num
  apply CPythonForceCollapseCost.mergeThirdLast [148] 36 32 40 364
  · norm_num
  apply CPythonForceCollapseCost.mergeTop [] 148 68 40 256
  · norm_num
  exact CPythonForceCollapseCost.pair 148 108

end CPythonListsort
