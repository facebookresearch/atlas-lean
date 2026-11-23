/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PairingHeap
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Pairing-heap amortized-analysis tests

Concrete `sz` / `Φ` / `len` / `trees` computations, and the public
proof-interface statements for the amortized bounds (Theorem 23.1,
`A_insert` / `A_merge` / `A_delMin`, the `AmortizedData` instances, and
the framework's `t_sum_le_U_sum` for each variant). No total-runtime
claim is inferred from the `T_*` / potential bounds.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.PairingHeapAnalysisTests

open PairingHeap
open Cslib.Algorithms.Lean.Amortized

variable {α : Type u} [LinearOrder α]

/-- The singleton `List2` heap holding `a`. -/
def singleton2 (a : ℕ) : List2.Heap ℕ := some (List2.Hp.mk a [])

example : List2.szHeap (singleton2 0) = 1 := by
  simp [singleton2, List2.szHeap, List2.szHp, List2.szList]

example : List2.szHeap (List2.merge (singleton2 0) (singleton2 1)) = 2 := by
  simp [singleton2, List2.merge, List2.link, List2.szHeap, List2.szHp, List2.szList]

example : List2.phiHeap (singleton2 0) = 0 := by
  simp [singleton2, List2.phiHeap, List2.phiHp, List2.phiList, List2.szList]

example : List2.trees [List2.Hp.mk 0 [], List2.Hp.mk 1 []] =
    Tree.BTree.node Tree.BTree.leaf 0
      (Tree.BTree.node Tree.BTree.leaf 1 Tree.BTree.leaf) := by
  simp [List2.trees]

example : List2.treeHp (List2.Hp.mk 0 [List2.Hp.mk 1 []]) =
    Tree.BTree.node (Tree.BTree.node Tree.BTree.leaf 1 Tree.BTree.leaf) 0
      Tree.BTree.leaf := by
  simp [List2.treeHp, List2.trees]

/-- The singleton `Tree` heap holding `a`. -/
def singletonT (a : ℕ) : Tree.BTree ℕ :=
  Tree.BTree.node Tree.BTree.leaf a Tree.BTree.leaf

example : Tree.phiTree (singletonT 0) = 0 := by
  simp [singletonT, Tree.phiTree, Tree.sizeTree]

example : Tree.len (singletonT 0) = 1 := by
  simp [singletonT, Tree.len]

example : PairingHeap.arityOp (PairingHeap.Op.Merge : PairingHeap.Op ℕ) = 2 := rfl

example : List2.execOp (PairingHeap.Op.Insert 0) [singleton2 1] =
    List2.insert 0 (singleton2 1) :=
  List2.execOp_insert 0 _

example : List2.costOp (PairingHeap.Op.Empty : PairingHeap.Op ℕ) [] = 0 :=
  List2.costOp_empty _

example : List2.UOp (PairingHeap.Op.Empty : PairingHeap.Op ℕ) [] = 0 :=
  List2.UOp_empty _

-- Check the complete Lemma 23.2 statement.
example (hs : List (List2.Hp α)) :
    List2.phiList (List2.pass1 hs) - List2.phiList hs ≤
      2 * Real.logb 2 ((List2.szList hs : ℝ) + 1) - (hs.length : ℝ) + 2 :=
  List2.deltaPhi_pass1 hs

-- Check the complete Theorem 23.1 statement.
example (h : List2.Hp α) :
    List2.phiHeap (List2.delMin (some h)) - List2.phiHeap (some h) ≤
      2 * Real.logb 2 ((List2.szList (List2.hps h) : ℝ) + 1) -
        ((List2.hps h).length : ℝ) + 2 :=
  List2.deltaPhi_delMin h

-- Check the complete `A_insert` / `A_merge` / `A_delMin` statements.
example (x : α) (ho : List2.Heap α) :
    (List2.Tinsert x ho : ℝ) + List2.phiHeap (List2.insert x ho) -
      List2.phiHeap ho ≤ Real.logb 2 ((List2.szHeap ho : ℝ) + 1) :=
  List2.A_insert x ho

example (ho1 ho2 : List2.Heap α) :
    (List2.Tmerge ho1 ho2 : ℝ) + List2.phiHeap (List2.merge ho1 ho2) -
      List2.phiHeap ho1 - List2.phiHeap ho2 ≤
      2 * Real.logb 2 ((List2.szHeap ho1 : ℝ) + (List2.szHeap ho2 : ℝ) + 1) :=
  List2.A_merge ho1 ho2

example (ho : List2.Heap α) :
    (List2.TdelMin ho : ℝ) + List2.phiHeap (List2.delMin ho) -
      List2.phiHeap ho ≤ 2 * Real.logb 2 ((List2.szHeap ho : ℝ) + 1) + 4 :=
  List2.A_delMin ho

-- Check the complete §23.3 mapping statements.
example (hs : List (List2.Hp α)) :
    Tree.sizeTree (List2.trees hs) = List2.szList hs :=
  List2.sizeTree_trees hs

example (h : List2.Hp α) : List2.phiHp h = Tree.phiTree (List2.treeHp h) :=
  List2.phiHp_tree h

-- The `AmortizedData` instance for the book version is available, with the
-- expected `arity` field.
example : (List2.pairingAmortized (α := ℕ)).arity = PairingHeap.arityOp := rfl

-- The framework's `t_sum_le_U_sum`, specialised to pairing heaps.
example (ot : RoseTree (PairingHeap.Op ℕ))
    (hwf : wf List2.pairingAmortized ot) :
    cost_sum List2.pairingAmortized ot ≤ U_sum List2.pairingAmortized ot :=
  List2.pairing_t_sum_le_U_sum ot hwf

-- Check the complete Tree `ΔΦ_pass1` statement.
example (hs : Tree.BTree α) :
    Tree.phiTree (Tree.pass1 hs) - Tree.phiTree hs ≤
      2 * Real.logb 2 ((Tree.sizeTree hs : ℝ) + 1) - (Tree.len hs : ℝ) + 2 :=
  Tree.deltaPhi_pass1 hs

-- Check the complete Tree `A_delMin` statement.
example {h : Tree.BTree α} (hr : Tree.isRoot h) :
    (Tree.TdelMin h : ℝ) + Tree.phiTree (Tree.delMin h) - Tree.phiTree h ≤
      2 * Real.logb 2 ((Tree.sizeTree h : ℝ) + 1) + 4 :=
  Tree.A_delMin hr

-- Check the Tree time bound used by `A_delMin`.
example (hs : Tree.BTree α) :
    Tree.Tpass2 (Tree.pass1 hs) + Tree.Tpass1 hs ≤ Tree.len hs + 2 :=
  Tree.Tpass2_pass1_add_Tpass1 hs

-- The `AmortizedData` instance for the Tree variant is available, with the
-- expected `arity` field.
example : (Tree.pairingTreeAmortized (α := ℕ)).arity = PairingHeap.arityOp := rfl

-- The framework's `t_sum_le_U_sum`, specialised to the Tree variant.
example (ot : RoseTree (PairingHeap.Op ℕ))
    (hwf : wf Tree.pairingTreeAmortized ot) :
    cost_sum Tree.pairingTreeAmortized ot ≤
      U_sum Tree.pairingTreeAmortized ot :=
  Tree.pairingTree_t_sum_le_U_sum ot hwf

end PairingHeapAnalysisTests

end Cslib.Algorithms.Lean
