/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ProbabilisticTreeCylinders

/-!
# Tests for finite-tree cylinders

Leaf and binary-tree cylinders, two ordered three-leaf trees with the
same yield, and a consistent cylinder of measure zero at a boundary
probability.
-/

@[expose] public section

namespace Cslib.Language

/-- Tests (nonvacuity, leaf): the leaf tree has active set `{[]}`,
leaf set `{[]}`, its cylinder is the root-leaf event, and its
measure/weight is `1 - p`. -/
private theorem test_leaf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    CGTree.leaf.activeAddresses [] = {[]} ∧
      CGTree.leaf.leafAddresses [] = {[]} ∧
      CGTree.leaf.branchAddresses [] = ∅ ∧
      treeCylinder CGTree.leaf = BinaryTreeAddressLaw.leafAt [] ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder CGTree.leaf) =
        ENNReal.ofReal (1 - p) := by
  refine ⟨CGTree.activeAddresses_leaf [], CGTree.leafAddresses_leaf [],
    CGTree.branchAddresses_leaf [], treeCylinder_leaf, ?_⟩
  have hw : CGTree.leaf.weight p (1 - p) = 1 - p := rfl
  rw [treeCylinder_weight hp0 hp1, hw]

/-- Tests (descendants of a leaf unrestricted): the point that is
a leaf at the root and branches everywhere below the root still lies
in the leaf cylinder. -/
private theorem test_leaf_descendants_unrestricted :
    (fun a => if a = [] then false else true) ∈ treeCylinder CGTree.leaf := by
  rw [mem_treeCylinder]
  intro a ha
  rw [CGTree.activeAddresses_leaf, Finset.mem_singleton] at ha
  subst ha
  have hf : CGTree.leaf.branchAssignment [] [] = false := by
    have hnt : ¬ CGTree.leaf.branchAssignment [] [] = true := by
      rw [CGTree.branchAssignment_eq_true_iff, CGTree.branchAddresses_leaf]
      exact Finset.notMem_empty []
    cases hval : CGTree.leaf.branchAssignment [] [] with
    | false => exact hval
    | true => exact (hnt hval).elim
  show (if [] = [] then false else true) = CGTree.leaf.branchAssignment [] []
  simp [hf]

/-- Tests (nonvacuity, binary tree): `node leaf leaf` has branch
address `[]`, leaf addresses `[false]`, `[true]`, active set
`{[], [false], [true]}`, and measure/weight `p * (1 - p) * (1 - p)`
(in `ENNReal.ofReal` product form). -/
private theorem test_binary {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (CGTree.node CGTree.leaf CGTree.leaf).branchAddresses [] = {[]} ∧
      (CGTree.node CGTree.leaf CGTree.leaf).leafAddresses [] = {[false], [true]} ∧
      (CGTree.node CGTree.leaf CGTree.leaf).activeAddresses [] =
        {[], [false], [true]} ∧
      BinaryTreeAddressLaw.law p hp0 hp1 (treeCylinder (CGTree.node CGTree.leaf CGTree.leaf)) =
        ENNReal.ofReal p * ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 - p) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [treeCylinder_weight hp0 hp1]
  have hw : (CGTree.node CGTree.leaf CGTree.leaf).weight p (1 - p) =
      p * (1 - p) * (1 - p) := rfl
  rw [hw, ENNReal.ofReal_mul (mul_nonneg hp0 (sub_nonneg.mpr hp1)), ENNReal.ofReal_mul hp0]

/-- Tests (nonvacuity, two ordered three-leaf trees): the
right- and left-associated three-leaf `CGTree`s are distinct, have
the displayed disjoint branch sets over a shared leaf/address
skeleton, map under the existing `ofCGTree` to derivation trees of
the same terminal yield `[(), (), ()]` (namely the copied `ambT₁`,
`ambT₂`), have disjoint cylinders, and each has measure/weight
`p ^ 2 * (1 - p) ^ 3` in existing-weight form. -/
private theorem test_three_leaf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)) ≠
        (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf) ∧
      (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)).branchAddresses [] =
        {[], [true]} ∧
      (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf).branchAddresses [] =
        {[], [false]} ∧
      (ofCGTree (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf))).yieldOf =
        [(), (), ()] ∧
      (ofCGTree (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf)).yieldOf =
        [(), (), ()] ∧
      ofCGTree (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)) = ambT₁ ∧
      ofCGTree (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf) = ambT₂ ∧
      Disjoint
        (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)))
        (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf)) ∧
      BinaryTreeAddressLaw.law p hp0 hp1
          (treeCylinder (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf))) =
        ENNReal.ofReal ((CGTree.node CGTree.leaf
          (CGTree.node CGTree.leaf CGTree.leaf)).weight p (1 - p)) ∧
      BinaryTreeAddressLaw.law p hp0 hp1
          (treeCylinder (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf)) =
        ENNReal.ofReal ((CGTree.node (CGTree.node CGTree.leaf CGTree.leaf)
          CGTree.leaf).weight p (1 - p)) := by
  have hne : (CGTree.node CGTree.leaf (CGTree.node CGTree.leaf CGTree.leaf)) ≠
      (CGTree.node (CGTree.node CGTree.leaf CGTree.leaf) CGTree.leaf) := by decide
  refine ⟨hne, by decide, by decide, rfl, rfl, rfl, rfl,
    treeCylinder_disjoint_of_ne hne,
    treeCylinder_weight hp0 hp1 _, treeCylinder_weight hp0 hp1 _⟩

/-- Tests (same yield, `PDerivTree` form): the copied existing
trees `ambT₁`, `ambT₂` are distinct, share terminal yield
`[(), (), ()]`, have distinct shapes, and have disjoint cylinders;
under shape-only rule weights at `p = 2 / 3` (the Chi-Geman weights,
leaf weight `1 / 3 = 1 - p`) each cylinder's measure is its existing
`weightOf`. -/
private theorem test_amb_three_leaf (w : ContextFreeRule Unit ambG.NT → ℝ)
    (hw_node : ∀ A B C, w ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ = 2 / 3)
    (hw_leaf : ∀ A a, w ⟨A, [Symbol.terminal a]⟩ = 1 / 3) :
    ambT₁ ≠ ambT₂ ∧ ambT₁.yieldOf = [(), (), ()] ∧ ambT₂.yieldOf = [(), (), ()] ∧
      ambT₁.shape ≠ ambT₂.shape ∧ Disjoint ambT₁.treeCylinder ambT₂.treeCylinder ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) ambT₁.treeCylinder =
        ENNReal.ofReal (ambT₁.weightOf w) ∧
      BinaryTreeAddressLaw.law (2 / 3) (by norm_num) (by norm_num) ambT₂.treeCylinder =
        ENNReal.ofReal (ambT₂.weightOf w) := by
  have hshape : ambT₁.shape ≠ ambT₂.shape := by decide
  have h0 : (0 : ℝ) ≤ 2 / 3 := by norm_num
  have h1 : (2 / 3 : ℝ) ≤ 1 := by norm_num
  have hw_leaf' : ∀ A a, w ⟨A, [Symbol.terminal a]⟩ = 1 - 2 / 3 := by
    intro A a
    rw [hw_leaf A a]
    norm_num
  refine ⟨ambT_ne, ambT_yield.1, ambT_yield.2, hshape,
    PDerivTree.treeCylinder_disjoint_of_shape_ne hshape, ?_, ?_⟩
  · exact PDerivTree.treeCylinder_weight h0 h1 w hw_node hw_leaf' ambT₁
  · exact PDerivTree.treeCylinder_weight h0 h1 w hw_node hw_leaf' ambT₂

/-- Tests (boundary, consistent cylinder of measure zero): at
`p = 0` the binary tree's cylinder is nonempty (its own assignment
lies in it) but has measure/weight zero; at `p = 1` the same holds
for the leaf tree. No contradiction: measure zero is not emptiness. -/
private theorem test_boundary_zero :
    (CGTree.node CGTree.leaf CGTree.leaf).branchAssignment [] ∈
        treeCylinder (CGTree.node CGTree.leaf CGTree.leaf) ∧
      BinaryTreeAddressLaw.law 0 le_rfl zero_le_one (treeCylinder (CGTree.node CGTree.leaf CGTree.leaf)) = 0 ∧
      CGTree.leaf.branchAssignment [] ∈ treeCylinder CGTree.leaf ∧
      BinaryTreeAddressLaw.law 1 zero_le_one le_rfl (treeCylinder CGTree.leaf) = 0 := by
  refine ⟨CGTree.branchAssignment_mem_treeCylinder _,
    ?_, CGTree.branchAssignment_mem_treeCylinder _, ?_⟩
  · calc BinaryTreeAddressLaw.law 0 le_rfl zero_le_one
            (treeCylinder (CGTree.node CGTree.leaf CGTree.leaf))
        = ENNReal.ofReal ((CGTree.node CGTree.leaf CGTree.leaf).weight 0 (1 - 0)) :=
          treeCylinder_weight le_rfl zero_le_one _
      _ = 0 := by
          have hw0 : (CGTree.node CGTree.leaf CGTree.leaf).weight (0 : ℝ) (1 - 0) = 0 := by
            show (0 : ℝ) * (1 - 0) * (1 - 0) = 0
            norm_num
          rw [hw0, ENNReal.ofReal_zero]
  · calc BinaryTreeAddressLaw.law 1 zero_le_one le_rfl (treeCylinder CGTree.leaf)
        = ENNReal.ofReal (CGTree.leaf.weight 1 (1 - 1)) :=
          treeCylinder_weight zero_le_one le_rfl _
      _ = 0 := by
          have hw1 : CGTree.leaf.weight (1 : ℝ) (1 - 1) = 0 := by
            show (1 : ℝ) - 1 = 0
            norm_num
          rw [hw1, ENNReal.ofReal_zero]


end Cslib.Language
