/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Basic
import all CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Internal.Tree
import Mathlib.Basic.Real.Basic

/-!
# Optimal-BST correctness

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
The public facts describe the actual saved half-open key intervals, inclusive
dummy intervals, earliest tied roots, and attained minimum full tree objective.
The private normalized nonnegative `Real` bridge expresses that same all-key,
all-dummy objective as one plus probability-weighted depths (Equation 14.11).
No probability certificate or alternate optimizer is a public assumption.
-/

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators
namespace Cslib.Algorithms.Lean.OptimalBST
variable {R : Type u}

/-- The empty instance performs initialization but no candidate evaluation. -/
public theorem optimalBST_empty [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] (p : Vector R 0) (q : Vector R 1) :
    optimalBST p q =
      ⟨(Vector.ofFn (fun _ : Fin 1 => Vector.ofFn (fun _ : Fin 1 => q[0])),
        Vector.replicate 0 (Vector.replicate 0 (none : Option (Fin 0)))), 0⟩ := by
  simp [optimalBST, execute, Vector.ofFn_succ]

/-- Every meaningful table cell has the CLRS recurrence and the earliest attaining root. -/
public theorem optimalBST_table_spec [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] :
    ∀ (n : Nat) (p : Vector R n) (q : Vector R (n + 1)),
      (∀ a : Fin (n + 1), (optimalBST p q).ret.1[a.val][a.val] = q[a.val]) ∧
      (∀ (a : Fin n) (b : Fin (n + 1)) (h : a.val < b.val),
        ∃ r : Fin n, a.val ≤ r.val ∧ r.val < b.val ∧
          (optimalBST p q).ret.2[a.val][b.val - 1]'(by omega) = some r ∧
          (optimalBST p q).ret.1[a.val][b.val] =
            (optimalBST p q).ret.1[a.val][r.val] +
            (optimalBST p q).ret.1[r.val + 1][b.val] +
            ((∑ i : Fin n, if a.val ≤ i.val ∧ i.val < b.val then p[i.val] else 0) +
              ∑ i : Fin (n + 1), if a.val ≤ i.val ∧ i.val ≤ b.val then q[i.val] else 0) ∧
          ∀ t : Fin n, a.val ≤ t.val → t.val < b.val →
            ((optimalBST p q).ret.1[a.val][b.val] ≤
              (optimalBST p q).ret.1[a.val][t.val] +
              (optimalBST p q).ret.1[t.val + 1][b.val] +
              ((∑ i : Fin n, if a.val ≤ i.val ∧ i.val < b.val then p[i.val] else 0) +
                ∑ i : Fin (n + 1), if a.val ≤ i.val ∧ i.val ≤ b.val then q[i.val] else 0)) ∧
            (t.val < r.val → (optimalBST p q).ret.1[a.val][b.val] <
              (optimalBST p q).ret.1[a.val][t.val] +
              (optimalBST p q).ret.1[t.val + 1][b.val] +
              ((∑ i : Fin n, if a.val ≤ i.val ∧ i.val < b.val then p[i.val] else 0) +
                ∑ i : Fin (n + 1), if a.val ≤ i.val ∧ i.val ≤ b.val then q[i.val] else 0))) := by
  intro n p q
  have actual := execute_table_complete p q
  exact ⟨actual.1, actual.2.2⟩

/-- The full saved cost is attained and bounds every canonical ordered competitor. -/
public theorem optimalBST_minimal [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] :
    ∀ (n : Nat) (p : Vector R n) (q : Vector R (n + 1)),
      IsLeast {z : R | ∃ (tree : BinaryTree (Fin n))
        (h : inorder tree = List.finRange n), expectedSearchCost n p q tree h = z}
        (optimalBST p q).ret.1[0][n] := by
  intro n p q
  exact actual_tree_minimal p q

private def weightedKeyDepth {n : Nat} (p : Vector Real n) :
    Nat → BinaryTree (Fin n) → Real
  | _, .nil => 0
  | depth, .node key left right =>
      depth • p[key.val] + weightedKeyDepth p (depth + 1) left +
        weightedKeyDepth p (depth + 1) right

private theorem keyCost_eq_weightedKeyDepth_add_mass {n : Nat}
    (p : Vector Real n) (tree : BinaryTree (Fin n)) (depth : Nat)
    (a : Fin (n + 1)) :
    keyCost p depth tree = weightedKeyDepth p depth tree +
      treeMass p (Vector.replicate (n + 1) 0) a tree := by
  induction tree generalizing depth a with
  | nil => simp [keyCost, weightedKeyDepth, treeMass]
  | node key left right ihLeft ihRight =>
      simp only [keyCost, weightedKeyDepth, treeMass, add_nsmul, one_nsmul,
        ihLeft (depth + 1) a, ihRight (depth + 1) (afterKey key)]
      ac_rfl

private theorem keyCost_eq_weightedKeyDepth_add_sum {n : Nat}
    (p : Vector Real n) (tree : BinaryTree (Fin n))
    (complete : inorder tree = List.finRange n) :
    keyCost p 0 tree = weightedKeyDepth p 0 tree + ∑ i : Fin n, p[i.val] := by
  have hTree : IntervalTree (n := n) 0 n tree := by
    simpa [IntervalTree, rankInterval_full] using complete
  have hMass := treeMass_eq_intervalMass p (Vector.replicate (n + 1) 0)
    0 n (Nat.zero_le _) le_rfl tree hTree
  have hKeys : (∑ i : Fin n, if 0 ≤ i.val ∧ i.val < n then p[i.val] else 0) =
      ∑ i : Fin n, p[i.val] := by
    apply Finset.sum_congr rfl
    intro i _
    exact ite_eq_left ⟨Nat.zero_le _, i.isLt⟩
  have hMass' : treeMass p (Vector.replicate (n + 1) 0) ⟨0, by omega⟩ tree =
      ∑ i : Fin n, p[i.val] := by
    simpa [intervalMass, hKeys] using hMass
  rw [keyCost_eq_weightedKeyDepth_add_mass p tree 0 ⟨0, by omega⟩, hMass']

private theorem expectedSearchCost_eq_one_add_weightedDepth
    (n : Nat) (p : Vector Real n) (q : Vector Real (n + 1))
    (tree : BinaryTree (Fin n)) (complete : inorder tree = List.finRange n)
    (_pNonnegative : ∀ i : Fin n, 0 ≤ p[i.val])
    (_qNonnegative : ∀ i : Fin (n + 1), 0 ≤ q[i.val])
    (normalized : (∑ i : Fin n, p[i.val]) + ∑ i : Fin (n + 1), q[i.val] = 1) :
    expectedSearchCost n p q tree complete =
      1 + weightedKeyDepth p 0 tree +
        ∑ i : Fin (n + 1),
          ((dummyDepths tree 0).get ⟨i.val, by
            rw [dummyDepths_length, BinaryTree.numLeaves_eq_numNodes_succ,
              numNodes_eq_length_inorder, complete]
            simp⟩) • q[i.val] := by
  have hLength : (dummyDepths tree 0).length = n + 1 := by
    rw [dummyDepths_length, BinaryTree.numLeaves_eq_numNodes_succ,
      numNodes_eq_length_inorder, complete]
    simp
  rw [expectedSearchCost]
  change keyCost p 0 tree +
      (∑ i : Fin (n + 1), ((dummyDepths tree 0)[i.val]'(by omega) + 1) • q[i.val]) =
    1 + weightedKeyDepth p 0 tree +
      ∑ i : Fin (n + 1), ((dummyDepths tree 0)[i.val]'(by omega)) • q[i.val]
  rw [keyCost_eq_weightedKeyDepth_add_sum p tree complete]
  simp only [add_nsmul, one_nsmul, Finset.sum_add_distrib]
  calc
    _ = ((∑ i : Fin n, p[i.val]) + ∑ i : Fin (n + 1), q[i.val]) +
        weightedKeyDepth p 0 tree +
        ∑ i : Fin (n + 1), ((dummyDepths tree 0)[i.val]'(by omega)) • q[i.val] := by
          ac_rfl
    _ = _ := by rw [normalized]

end Cslib.Algorithms.Lean.OptimalBST
