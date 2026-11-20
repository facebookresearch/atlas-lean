/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-!
# Merge-cost accounting

This module isolates the implementation-independent arithmetic behind the
Munro--Wild PowerSort merge-cost bound.  Run lengths and merge costs remain
natural numbers; entropy and the final inequality live in `ℝ`.

An empty `MergePlan` represents the empty input.  A nonempty plan is a binary
tree whose leaves are the runs, in input order.  Internal powers are retained
for the later PowerSort-policy bridge but do not affect merge-cost accounting.
-/

namespace CPythonListsort

/-- A positive run-length sequence with prescribed total length. -/
structure RunProfile (n : Nat) where
  lengths : List Nat
  sum_eq : lengths.sum = n
  positive : ∀ length ∈ lengths, 0 < length

namespace RunProfile

/-- The empty list is the only positive run profile of total length zero. -/
theorem lengths_eq_nil (profile : RunProfile 0) : profile.lengths = [] := by
  cases hlengths : profile.lengths with
  | nil => rfl
  | cons length rest =>
      have hpositive : 0 < length := profile.positive length (by simp [hlengths])
      have hsum : length + rest.sum = 0 := by
        simpa [hlengths] using profile.sum_eq
      omega

/-- A positive profile has no runs exactly when its prescribed total is zero. -/
theorem lengths_eq_nil_iff (profile : RunProfile n) :
    profile.lengths = [] ↔ n = 0 := by
  constructor
  · intro hlengths
    rw [← profile.sum_eq, hlengths]
    simp
  · intro hn
    subst n
    exact profile.lengths_eq_nil

/-- Real-valued run fractions, with Lean's totalized division convention at
total length zero. -/
noncomputable def fractions (profile : RunProfile n) : List ℝ :=
  profile.lengths.map fun length : Nat => (length : ℝ) / (n : ℝ)

end RunProfile

/-- One base-two Shannon entropy summand, using `0⁻¹ = 0` and
`Real.logb 2 0 = 0` at the zero endpoint. -/
noncomputable def binaryEntropyTerm (p : ℝ) : ℝ :=
  p * Real.logb 2 p⁻¹

/-- Base-two Shannon entropy of a finite real-valued weight list. -/
noncomputable def binaryEntropy (weights : List ℝ) : ℝ :=
  (weights.map binaryEntropyTerm).sum

/-- Base-two entropy of the fractions represented by a run profile. -/
noncomputable def RunProfile.entropy (profile : RunProfile n) : ℝ :=
  binaryEntropy profile.fractions

@[simp]
theorem binaryEntropy_nil : binaryEntropy [] = 0 := by
  simp [binaryEntropy]

@[simp]
theorem RunProfile.entropy_zero (profile : RunProfile 0) : profile.entropy = 0 := by
  rw [RunProfile.entropy, RunProfile.fractions, profile.lengths_eq_nil]
  simp

/-- A binary merge tree.  Leaves store run lengths and each internal node
retains its PowerSort node power for the later policy bridge. -/
inductive MergeTree where
  | leaf (length : Nat)
  | merge (power : Nat) (left right : MergeTree)
  deriving DecidableEq, Repr

namespace MergeTree

/-- Leaf lengths in left-to-right input order. -/
def runLengths : MergeTree → List Nat
  | .leaf length => [length]
  | .merge _ left right => left.runLengths ++ right.runLengths

/-- Total number of elements represented by a tree. -/
def totalLength : MergeTree → Nat
  | .leaf length => length
  | .merge _ left right => left.totalLength + right.totalLength

/-- Paper merge cost: merging two subtrees costs the size of their result. -/
def mergeCost : MergeTree → Nat
  | .leaf _ => 0
  | .merge _ left right =>
      left.mergeCost + right.mergeCost + left.totalLength + right.totalLength

/-- Leaf lengths paired with their depth below an ambient root depth. -/
def leavesWithDepth : Nat → MergeTree → List (Nat × Nat)
  | depth, .leaf length => [(length, depth)]
  | depth, .merge _ left right =>
      leavesWithDepth (depth + 1) left ++ leavesWithDepth (depth + 1) right

/-- The weighted external path length at an ambient root depth. -/
def weightedPathLengthAt (depth : Nat) (tree : MergeTree) : Nat :=
  ((tree.leavesWithDepth depth).map fun leaf => leaf.1 * leaf.2).sum

/-- The ordinary weighted external path length. -/
def weightedPathLength (tree : MergeTree) : Nat :=
  tree.weightedPathLengthAt 0

@[simp]
theorem sum_runLengths : ∀ tree : MergeTree,
    tree.runLengths.sum = tree.totalLength
  | .leaf _ => by simp [runLengths, totalLength]
  | .merge _ left right => by
      simp [runLengths, totalLength, sum_runLengths left, sum_runLengths right]

@[simp]
theorem leavesWithDepth_fst (depth : Nat) : ∀ tree : MergeTree,
    (tree.leavesWithDepth depth).map Prod.fst = tree.runLengths
  | .leaf _ => by simp [leavesWithDepth, runLengths]
  | .merge _ left right => by
      simp [leavesWithDepth, runLengths, leavesWithDepth_fst (depth + 1) left,
        leavesWithDepth_fst (depth + 1) right]

/-- Weighted path length at depth `d` is intrinsic merge cost plus `d` copies
of every leaf weight. -/
theorem weightedPathLengthAt_eq (depth : Nat) : ∀ tree : MergeTree,
    tree.weightedPathLengthAt depth =
      tree.mergeCost + depth * tree.totalLength
  | .leaf length => by
      simp [weightedPathLengthAt, leavesWithDepth, mergeCost, totalLength,
        Nat.mul_comm]
  | .merge power left right => by
      rw [weightedPathLengthAt, leavesWithDepth, List.map_append, List.sum_append,
        mergeCost, totalLength]
      change
        left.weightedPathLengthAt (depth + 1) +
            right.weightedPathLengthAt (depth + 1) =
          left.mergeCost + right.mergeCost + left.totalLength +
              right.totalLength +
            depth * (left.totalLength + right.totalLength)
      rw [weightedPathLengthAt_eq (depth + 1) left,
        weightedPathLengthAt_eq (depth + 1) right]
      ring

/-- The sum of merge-result sizes equals the run-length-weighted leaf depth. -/
theorem mergeCost_eq_weightedPathLength (tree : MergeTree) :
    tree.mergeCost = tree.weightedPathLength := by
  simpa [weightedPathLength] using (tree.weightedPathLengthAt_eq 0).symm

end MergeTree

/-- A full merge plan, including the empty-input case. -/
inductive MergePlan where
  | empty
  | tree (root : MergeTree)
  deriving DecidableEq, Repr

namespace MergePlan

def runLengths : MergePlan → List Nat
  | .empty => []
  | .tree root => root.runLengths

def mergeCost : MergePlan → Nat
  | .empty => 0
  | .tree root => root.mergeCost

def leavesWithDepth : MergePlan → List (Nat × Nat)
  | .empty => []
  | .tree root => root.leavesWithDepth 0

def weightedPathLength : MergePlan → Nat
  | .empty => 0
  | .tree root => root.weightedPathLength

@[simp]
theorem leavesWithDepth_fst (plan : MergePlan) :
    plan.leavesWithDepth.map Prod.fst = plan.runLengths := by
  cases plan with
  | empty => simp [leavesWithDepth, runLengths]
  | tree root => simp [leavesWithDepth, runLengths]

/-- Empty plans and nonempty merge trees satisfy the same exact cost identity. -/
theorem mergeCost_eq_weightedPathLength (plan : MergePlan) :
    plan.mergeCost = plan.weightedPathLength := by
  cases plan with
  | empty => rfl
  | tree root => exact root.mergeCost_eq_weightedPathLength

end MergePlan

/-- Casting the sum of profile lengths to `ℝ` recovers its prescribed total. -/
theorem RunProfile.sum_cast (profile : RunProfile n) :
    (List.map (fun length : Nat => (length : ℝ)) profile.lengths).sum =
      (n : ℝ) := by
  rw [← Nat.cast_list_sum, profile.sum_eq]

/-- For positive total length, the run fractions form a probability vector. -/
theorem RunProfile.fractions_sum (profile : RunProfile n) (hn : 0 < n) :
    profile.fractions.sum = 1 := by
  rw [RunProfile.fractions]
  simp only [div_eq_mul_inv]
  rw [List.sum_map_mul_right, profile.sum_cast]
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  exact mul_inv_cancel₀ hnreal

private theorem weightedDepthTerm_le
    {n length depth : Nat} (hn : 0 < n)
    (hdepth :
      (depth : ℝ) ≤
        Real.logb 2 ((n : ℝ) / (length : ℝ)) + 2) :
    ((length * depth : Nat) : ℝ) ≤
      (n : ℝ) * binaryEntropyTerm ((length : ℝ) / (n : ℝ)) +
        2 * (length : ℝ) := by
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  have hscale :
      (n : ℝ) * ((length : ℝ) / (n : ℝ)) = (length : ℝ) := by
    field_simp
  have hdepth' :
      (depth : ℝ) ≤
        Real.logb 2 (((length : ℝ) / (n : ℝ))⁻¹) + 2 := by
    simpa only [inv_div] using hdepth
  have hmul := mul_le_mul_of_nonneg_left hdepth' (Nat.cast_nonneg length)
  simp only [Nat.cast_mul, binaryEntropyTerm]
  rw [← mul_assoc, hscale]
  nlinarith

/-- The analytic summation step in the PowerSort bound.

If each leaf depth is at most `lg (1 / p) + 2`, then the weighted external path
length is at most `n * H₂(p) + 2n`.  This statement includes the `n = 0`,
zero-run case; its depth premise is then vacuous. -/
theorem weightedPathLength_le_entropy_add_two
    {n : Nat} (profile : RunProfile n) (leaves : List (Nat × Nat))
    (hlengths : leaves.map Prod.fst = profile.lengths)
    (hdepth : ∀ leaf ∈ leaves,
      (leaf.2 : ℝ) ≤
        Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
    (((leaves.map fun leaf => leaf.1 * leaf.2).sum : Nat) : ℝ) ≤
      (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
  by_cases hnzero : n = 0
  · subst n
    have hprofile : profile.lengths = [] := profile.lengths_eq_nil
    have hleaves : leaves = [] := by
      exact List.eq_nil_of_map_eq_nil (hlengths.trans hprofile)
    subst leaves
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hnzero
    rw [Nat.cast_list_sum]
    calc
      (List.map (↑) (leaves.map fun leaf => leaf.1 * leaf.2)).sum ≤
          (leaves.map fun leaf =>
            (n : ℝ) * binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ)) +
              2 * (leaf.1 : ℝ)).sum := by
        rw [List.map_map]
        apply List.sum_le_sum
        intro leaf hleaf
        simpa [Function.comp_apply] using
          weightedDepthTerm_le hn (hdepth leaf hleaf)
      _ = (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
        rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
        have hfractions :
            List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves =
              profile.fractions := by
          calc
            List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves =
              List.map (fun length : Nat => (length : ℝ) / (n : ℝ))
                  (List.map Prod.fst leaves) := by
              simp only [List.map_map, Function.comp_def]
            _ = List.map (fun length : Nat => (length : ℝ) / (n : ℝ))
                  profile.lengths := by
              rw [hlengths]
            _ = profile.fractions := rfl
        have hcastLengths :
            (List.map (fun leaf => (leaf.1 : ℝ)) leaves).sum = (n : ℝ) := by
          calc
            (List.map (fun leaf => (leaf.1 : ℝ)) leaves).sum =
                (List.map (fun length : Nat => (length : ℝ))
                  (List.map Prod.fst leaves)).sum := by
              simp only [List.map_map, Function.comp_def]
            _ = (List.map (fun length : Nat => (length : ℝ))
                  profile.lengths).sum := by
              rw [hlengths]
            _ = (n : ℝ) := profile.sum_cast
        have hentropy :
            (List.map (fun leaf =>
              binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ))) leaves).sum =
                profile.entropy := by
          calc
            (List.map (fun leaf =>
                binaryEntropyTerm ((leaf.1 : ℝ) / (n : ℝ))) leaves).sum =
                binaryEntropy
                  (List.map (fun leaf => (leaf.1 : ℝ) / (n : ℝ)) leaves) := by
              simp only [binaryEntropy, List.map_map, Function.comp_def]
            _ = binaryEntropy profile.fractions := congrArg binaryEntropy hfractions
            _ = profile.entropy := rfl
        rw [hentropy, hcastLengths]

/-- Tree-level wrapper for the generic entropy summation theorem.  Proving the
PowerSort theorem is thereby reduced to constructing a matching plan and
establishing its per-leaf depth bound. -/
theorem MergePlan.mergeCost_le_entropy_add_two
    {n : Nat} (plan : MergePlan) (profile : RunProfile n)
    (hlengths : plan.runLengths = profile.lengths)
    (hdepth : ∀ leaf ∈ plan.leavesWithDepth,
      (leaf.2 : ℝ) ≤
        Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
    (plan.mergeCost : ℝ) ≤
      (n : ℝ) * profile.entropy + 2 * (n : ℝ) := by
  rw [plan.mergeCost_eq_weightedPathLength]
  cases plan with
  | empty =>
      simpa only [MergePlan.weightedPathLength, List.map_nil, List.sum_nil,
        Nat.cast_zero] using
        weightedPathLength_le_entropy_add_two profile []
          (by simpa [MergePlan.runLengths] using hlengths) (by simp)
  | tree root =>
      simpa only [MergePlan.weightedPathLength, MergeTree.weightedPathLength,
        MergeTree.weightedPathLengthAt] using
          weightedPathLength_le_entropy_add_two profile (root.leavesWithDepth 0)
            (by simpa [MergePlan.runLengths] using hlengths) hdepth

/-- Source-order form of the Munro--Wild headline bound, `M ≤ H₂ · n + 2n`. -/
theorem MergePlan.mergeCost_le_entropy_mul_add_two
    {n : Nat} (plan : MergePlan) (profile : RunProfile n)
    (hlengths : plan.runLengths = profile.lengths)
    (hdepth : ∀ leaf ∈ plan.leavesWithDepth,
      (leaf.2 : ℝ) ≤
        Real.logb 2 ((n : ℝ) / (leaf.1 : ℝ)) + 2) :
    (plan.mergeCost : ℝ) ≤
      profile.entropy * (n : ℝ) + 2 * (n : ℝ) := by
  simpa only [mul_comm] using
    plan.mergeCost_le_entropy_add_two profile hlengths hdepth

end CPythonListsort
