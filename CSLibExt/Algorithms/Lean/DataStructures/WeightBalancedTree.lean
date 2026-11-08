/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Weight-balanced trees

This module develops weight-balanced binary search trees, the `BB[α]` trees of
Nievergelt and Reingold, following Demaine, *Advanced Data Structures*
(6.851), Lecture 3. The classical invariant is stated on subtree *weights*,
with external leaves counted: `w(nil) = 1` and, in the notation of this
module, `weight t = t.numNodes + 1`, so `weight` of a node is the sum of
the weights of its children. The `BB[1 / 4]` invariant is that each child
has weight at most `1 - α = 3 / 4` of the weight of its parent node, in
integer form `4 * weight child ≤ 3 * weight node`, i.e.

`4 * (child.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)`.

Counting only keys instead (`4 * child.numNodes ≤ 3 * node.numNodes`)
would be one unit weaker: it admits, for example, a four-key right spine,
whose root child has weight ratio `4 / 5 > 3 / 4`. The `Balanced`
predicate, the rotation tests in `balance`, and the height bound below
all use the weight form. `balanced_node_iff_weight` records the invariant
directly in terms of `weight`.

Insertion is ordinary BST insertion followed by rebalancing on the search
path: when one child has become too heavy, a single rotation is performed
if the inner grandchild contains at most twice as many keys as the outer
grandchild, and a double rotation otherwise. Insertion ignores an
already-present key.

The value `α = 1 / 4` is not arbitrary. A single insertion followed by one
single or double rotation per node on the search path can maintain `BB[α]`
only for `α ≤ 1 - 1 / √2 ≈ 0.293`. In particular the stronger `α = 1 / 3`
bound is not maintainable this way. The `α = 1 / 4` weight invariant with
the `2 : 1` grandchild criterion above is maintainable, and every case of
the rebalancing proof below is closed by linear arithmetic over the
subtree weights (written out as `numNodes + 1`).

`BinaryTree.numNodes`, and hence `weight`, is defined by recursion on the
tree, so the rebalancing tests as written take linear time in the subtree
size; the standard implementation caches subtree weights at each node
(compare `OrderStatisticTree`, which caches subtree sizes). Because the
cached variant differs only in how the weight is read, the invariants and
rotation proofs here are stated against the recursively defined weight.
Deletion, a cached-weight implementation, and amortized complexity bounds
are out of scope.

## Main definitions

* `WeightBalancedTree.weight` is the Nievergelt-Reingold subtree weight.
* `WeightBalancedTree.Balanced` is the `BB[1/4]` invariant.
* `WeightBalancedTree.insert` inserts a key with rebalancing.

## Main results

* `WeightBalancedTree.balanced_insert`: insertion preserves balance.
* `WeightBalancedTree.ordered_insert`: insertion preserves ordering.
* `WeightBalancedTree.mem_insert`: insertion adds exactly the new key.
* `WeightBalancedTree.height_le_log2`: the height is logarithmic in the
  number of keys, in the form
  `BinaryTree.height t ≤ Nat.log2 ((t.numNodes + 1) ^ 3) + 1`, proved from the
  exponential weight lower bound `pow_height_le`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace WeightBalancedTree

variable {α : Type u}

/-- The number of keys of the empty tree, for `BinaryTree.numNodes`. -/
@[simp] public theorem numNodes_empty :
    (BinaryTree.nil : BinaryTree α).numNodes = 0 :=
  rfl

/-- The number of keys of a node, for `BinaryTree.numNodes`. -/
@[simp] public theorem numNodes_node {left right : BinaryTree α} {key : α} :
    (BinaryTree.node key left right).numNodes =
      left.numNodes + right.numNodes + 1 :=
  rfl

/- Height statements below use Mathlib's `BinaryTree.height` directly:
the empty tree has height `0` and a node has height one more than the
taller child. -/

/-- The Nievergelt-Reingold weight of a tree: external leaves count, so the
empty tree has weight `1` and any tree has weight one more than its number
of keys. The weight of a node is the sum of the weights of its children
(`weight_node`). -/
public def weight (t : BinaryTree α) : Nat :=
  t.numNodes + 1

@[simp] public theorem weight_empty : weight (.nil : BinaryTree α) = 1 :=
  rfl

@[simp] public theorem weight_node {left right : BinaryTree α} {key : α} :
    weight (.node key left right) = weight left + weight right := by
  simp only [weight, numNodes_node]
  omega

/-- The weight-balance invariant `BB[1/4]`: at every node, each child has
weight at most three quarters of the weight of the node,
`4 * weight child ≤ 3 * weight node`, written out in key counts as
`4 * (child.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)`.
See `balanced_node_iff_weight` for the same statement using `weight`. -/
public def Balanced : BinaryTree α → Prop
  | .nil => True
  | .node _ left right =>
      Balanced left ∧ Balanced right ∧
        4 * (left.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2) ∧
          4 * (right.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)

@[simp] private theorem mem_nil {x : α} :
    x ∈ (BinaryTree.nil : BinaryTree α) ↔ False :=
  Iff.rfl

@[simp] private theorem mem_node {x key : α} {left right : BinaryTree α} :
    x ∈ BinaryTree.node key left right ↔ x ∈ left ∨ x = key ∨ x ∈ right :=
  Iff.rfl

/--
Rebuild a node from children that violate the weight invariant by at most
one inserted key, restoring balance. When the left child is too heavy, a
single right rotation is performed if the left-right grandchild is at most
twice as large as the left-left one, and a double left-right rotation
otherwise; the right-heavy case is symmetric. Children that already satisfy
the invariant are rebuilt without rotation.
-/
public def balance (left : BinaryTree α) (key : α) (right : BinaryTree α) : BinaryTree α :=
  if 3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1) then
    match left with
    | .node leftKey leftLeft leftRight =>
        if leftRight.numNodes ≤ 2 * leftLeft.numNodes then
          .node leftKey leftLeft (.node key leftRight right)
        else
          match leftRight with
          | .node leftRightKey leftRightLeft leftRightRight =>
              .node leftRightKey (.node leftKey leftLeft leftRightLeft)
                (.node key leftRightRight right)
          | .nil => .node key left right
    | .nil => .node key left right
  else if 3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1) then
    match right with
    | .node rightKey rightLeft rightRight =>
        if rightLeft.numNodes ≤ 2 * rightRight.numNodes then
          .node rightKey (.node key left rightLeft) rightRight
        else
          match rightLeft with
          | .node rightLeftKey rightLeftLeft rightLeftRight =>
              .node rightLeftKey (.node key left rightLeftLeft)
                (.node rightKey rightLeftRight rightRight)
          | .nil => .node key left right
    | .nil => .node key left right
  else .node key left right

/-- Insert a key, leaving an existing equal key unchanged and rebalancing
every node on the search path. -/
public def insert [LinearOrder α] (x : α) : BinaryTree α → BinaryTree α
  | .nil => .node x .nil .nil
  | tree@(.node key left right) =>
      if x < key then balance (insert x left) key right
      else if key < x then balance left key (insert x right)
      else tree

/-- Build a tree by inserting the list from right to left. -/
public def fromList [LinearOrder α] : List α → BinaryTree α
  | [] => .nil
  | x :: xs => insert x (fromList xs)

private theorem All_mono {p q : α → Prop} (h : ∀ a, p a → q a) (tree : BinaryTree α) :
    BinarySearchTree.All p tree → BinarySearchTree.All q tree := by
  induction tree with
  | nil => intro _; trivial
  | node key left right ihLeft ihRight =>
      rintro ⟨hLeft, hKey, hRight⟩
      exact ⟨ihLeft hLeft, h key hKey, ihRight hRight⟩

/-- A node whose children are balanced and satisfy the weight inequalities
is balanced. -/
public theorem balanced_node {key : α} {left right : BinaryTree α}
    (hLeft : Balanced left) (hRight : Balanced right)
    (hWeightLeft :
      4 * (left.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2))
    (hWeightRight :
      4 * (right.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)) :
    Balanced (.node key left right) :=
  ⟨hLeft, hRight, hWeightLeft, hWeightRight⟩

/-- The node case of `Balanced`, stated with `weight`: a node is balanced
exactly when its children are balanced and each child has weight at most
three quarters of the weight of the node. This is the classical
`BB[1/4]` invariant. -/
public theorem balanced_node_iff_weight {key : α} {left right : BinaryTree α} :
    Balanced (.node key left right) ↔
      Balanced left ∧ Balanced right ∧
        4 * weight left ≤ 3 * weight (.node key left right) ∧
          4 * weight right ≤ 3 * weight (.node key left right) := by
  simp only [weight, numNodes_node]
  constructor
  · rintro ⟨hLeft, hRight, hA, hB⟩
    exact ⟨hLeft, hRight, by omega, by omega⟩
  · rintro ⟨hLeft, hRight, hA, hB⟩
    exact ⟨hLeft, hRight, by omega, by omega⟩

private theorem ordered_node [LT α] {key : α} {left right : BinaryTree α}
    (hLeft : BinarySearchTree.Ordered left) (hRight : BinarySearchTree.Ordered right)
    (hAllLeft : BinarySearchTree.All (· < key) left) (hAllRight : BinarySearchTree.All (key < ·) right) :
    BinarySearchTree.Ordered (.node key left right) :=
  ⟨hLeft, hRight, hAllLeft, hAllRight⟩

private theorem balance_eq_node_of_le {key : α} {left right : BinaryTree α}
    (hLeft : 4 * (left.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2))
    (hRight : 4 * (right.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)) :
    balance left key right = .node key left right := by
  unfold balance
  simp only [show ¬(3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1)) by omega,
    show ¬(3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1)) by omega, ite_false]

private theorem balance_left_single {key leftKey : α}
    {leftLeft leftRight right : BinaryTree α}
    (hTall : 3 * (leftLeft.numNodes + leftRight.numNodes + 1 + right.numNodes + 2) <
      4 * (leftLeft.numNodes + leftRight.numNodes + 1 + 1))
    (hSingle : leftRight.numNodes ≤ 2 * leftLeft.numNodes) :
    balance (.node leftKey leftLeft leftRight) key right =
      .node leftKey leftLeft (.node key leftRight right) := by
  unfold balance
  simp only [numNodes_node, hTall, hSingle, ite_true]

private theorem balance_left_double {key leftKey leftRightKey : α}
    {leftLeft leftRightLeft leftRightRight right : BinaryTree α}
    (hTall : 3 * (leftLeft.numNodes + (leftRightLeft.numNodes + leftRightRight.numNodes + 1) +
        1 + right.numNodes + 2) <
      4 * (leftLeft.numNodes + (leftRightLeft.numNodes + leftRightRight.numNodes + 1) + 1 + 1))
    (hDouble : 2 * leftLeft.numNodes <
      leftRightLeft.numNodes + leftRightRight.numNodes + 1) :
    balance (.node leftKey leftLeft
        (.node leftRightKey leftRightLeft leftRightRight)) key right =
      .node leftRightKey (.node leftKey leftLeft leftRightLeft)
        (.node key leftRightRight right) := by
  unfold balance
  simp only [numNodes_node, hTall, ite_true,
    show ¬(leftRightLeft.numNodes + leftRightRight.numNodes + 1 ≤ 2 * leftLeft.numNodes) by
      omega, ite_false]

private theorem balance_right_single {key rightKey : α}
    {left rightLeft rightRight : BinaryTree α}
    (hTall : 3 * (left.numNodes + (rightLeft.numNodes + rightRight.numNodes + 1) + 2) <
      4 * (rightLeft.numNodes + rightRight.numNodes + 1 + 1))
    (hSingle : rightLeft.numNodes ≤ 2 * rightRight.numNodes) :
    balance left key (.node rightKey rightLeft rightRight) =
      .node rightKey (.node key left rightLeft) rightRight := by
  unfold balance
  simp only [numNodes_node,
    show ¬(3 * (left.numNodes + (rightLeft.numNodes + rightRight.numNodes + 1) + 2) <
      4 * (left.numNodes + 1)) by omega, ite_false, hTall, ite_true, hSingle]

private theorem balance_right_double {key rightKey rightLeftKey : α}
    {left rightLeftLeft rightLeftRight rightRight : BinaryTree α}
    (hTall : 3 * (left.numNodes +
        ((rightLeftLeft.numNodes + rightLeftRight.numNodes + 1) + rightRight.numNodes + 1) + 2) <
      4 * ((rightLeftLeft.numNodes + rightLeftRight.numNodes + 1) + rightRight.numNodes + 1 + 1))
    (hDouble : 2 * rightRight.numNodes <
      rightLeftLeft.numNodes + rightLeftRight.numNodes + 1) :
    balance left key (.node rightKey
        (.node rightLeftKey rightLeftLeft rightLeftRight) rightRight) =
      .node rightLeftKey (.node key left rightLeftLeft)
        (.node rightKey rightLeftRight rightRight) := by
  unfold balance
  simp only [numNodes_node,
    show ¬(3 * (left.numNodes +
        ((rightLeftLeft.numNodes + rightLeftRight.numNodes + 1) + rightRight.numNodes + 1) + 2) <
      4 * (left.numNodes + 1)) by omega, ite_false, hTall, ite_true,
    show ¬(rightLeftLeft.numNodes + rightLeftRight.numNodes + 1 ≤ 2 * rightRight.numNodes) by
      omega]

/-- Rebalancing does not change the number of keys. -/
public theorem numNodes_balance {key : α} {left right : BinaryTree α} :
    (balance left key right).numNodes = left.numNodes + right.numNodes + 1 := by
  by_cases hTallLeft : 3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1)
  · cases left with
    | nil => simp only [numNodes_empty] at hTallLeft; omega
    | node leftKey leftLeft leftRight =>
      simp only [numNodes_node] at hTallLeft
      by_cases hSingle : leftRight.numNodes ≤ 2 * leftLeft.numNodes
      · rw [balance_left_single hTallLeft hSingle]
        simp only [numNodes_node]
        omega
      · cases leftRight with
        | nil => simp only [numNodes_empty] at hSingle; omega
        | node leftRightKey leftRightLeft leftRightRight =>
          simp only [numNodes_node] at hTallLeft hSingle
          rw [balance_left_double hTallLeft (by omega)]
          simp only [numNodes_node]
          omega
  · by_cases hTallRight : 3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1)
    · cases right with
      | nil => simp only [numNodes_empty] at hTallRight; omega
      | node rightKey rightLeft rightRight =>
        simp only [numNodes_node] at hTallRight
        by_cases hSingle : rightLeft.numNodes ≤ 2 * rightRight.numNodes
        · rw [balance_right_single hTallRight hSingle]
          simp only [numNodes_node]
          omega
        · cases rightLeft with
          | nil => simp only [numNodes_empty] at hSingle; omega
          | node rightLeftKey rightLeftLeft rightLeftRight =>
            simp only [numNodes_node] at hTallRight hSingle
            rw [balance_right_double hTallRight (by omega)]
            simp only [numNodes_node]
            omega
    · rw [balance_eq_node_of_le (by omega) (by omega)]
      simp only [numNodes_node]

/-- Rebalancing children that violate the weight invariant by at most the
one-key weight slack
`4 * (child.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2) + 1`
produces a balanced tree. This is the precondition that one insertion
step maintains. -/
public theorem balanced_balance {key : α} {left right : BinaryTree α}
    (hBalLeft : Balanced left) (hBalRight : Balanced right)
    (hDiffLeft : 4 * (left.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2) + 1)
    (hDiffRight : 4 * (right.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2) + 1) :
    Balanced (balance left key right) := by
  by_cases hTallLeft : 3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1)
  · cases left with
    | nil => simp only [numNodes_empty] at hTallLeft; omega
    | node leftKey leftLeft leftRight =>
      obtain ⟨hBalLeftLeft, hBalLeftRight, hBalLeftA, hBalLeftB⟩ := hBalLeft
      simp only [numNodes_node] at hTallLeft hDiffLeft hDiffRight
      by_cases hSingle : leftRight.numNodes ≤ 2 * leftLeft.numNodes
      · rw [balance_left_single hTallLeft hSingle]
        refine balanced_node hBalLeftLeft
          (balanced_node hBalLeftRight hBalRight ?_ ?_) ?_ ?_ <;>
          (try simp only [numNodes_node]) <;> omega
      · cases leftRight with
        | nil => simp only [numNodes_empty] at hSingle; omega
        | node leftRightKey leftRightLeft leftRightRight =>
          obtain ⟨hBalLRL, hBalLRR, hBalLRA, hBalLRB⟩ := hBalLeftRight
          simp only [numNodes_node] at hTallLeft hDiffLeft hDiffRight hSingle hBalLeftA hBalLeftB
          rw [balance_left_double hTallLeft (by omega)]
          refine balanced_node (balanced_node hBalLeftLeft hBalLRL ?_ ?_)
            (balanced_node hBalLRR hBalRight ?_ ?_) ?_ ?_ <;>
            (try simp only [numNodes_node]) <;> omega
  · by_cases hTallRight : 3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1)
    · cases right with
      | nil => simp only [numNodes_empty] at hTallRight; omega
      | node rightKey rightLeft rightRight =>
        obtain ⟨hBalRightLeft, hBalRightRight, hBalRightA, hBalRightB⟩ := hBalRight
        simp only [numNodes_node] at hTallRight hDiffLeft hDiffRight
        by_cases hSingle : rightLeft.numNodes ≤ 2 * rightRight.numNodes
        · rw [balance_right_single hTallRight hSingle]
          refine balanced_node (balanced_node hBalLeft hBalRightLeft ?_ ?_)
            hBalRightRight ?_ ?_ <;> (try simp only [numNodes_node]) <;> omega
        · cases rightLeft with
          | nil => simp only [numNodes_empty] at hSingle; omega
          | node rightLeftKey rightLeftLeft rightLeftRight =>
            obtain ⟨hBalRLL, hBalRLR, hBalRLA, hBalRLB⟩ := hBalRightLeft
            simp only [numNodes_node] at hTallRight hDiffLeft hDiffRight hSingle hBalRightA hBalRightB
            rw [balance_right_double hTallRight (by omega)]
            refine balanced_node (balanced_node hBalLeft hBalRLL ?_ ?_)
              (balanced_node hBalRLR hBalRightRight ?_ ?_) ?_ ?_ <;>
              (try simp only [numNodes_node]) <;> omega
    · rw [balance_eq_node_of_le (by omega) (by omega)]
      exact balanced_node hBalLeft hBalRight (by omega) (by omega)

/-- Rebalancing preserves structural membership. -/
public theorem mem_balance {x key : α} {left right : BinaryTree α} :
    x ∈ balance left key right ↔ x ∈ left ∨ x = key ∨ x ∈ right := by
  by_cases hTallLeft : 3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1)
  · cases left with
    | nil => simp only [numNodes_empty] at hTallLeft; omega
    | node leftKey leftLeft leftRight =>
      simp only [numNodes_node] at hTallLeft
      by_cases hSingle : leftRight.numNodes ≤ 2 * leftLeft.numNodes
      · rw [balance_left_single hTallLeft hSingle]
        simp only [mem_node, or_assoc]
      · cases leftRight with
        | nil => simp only [numNodes_empty] at hSingle; omega
        | node leftRightKey leftRightLeft leftRightRight =>
          simp only [numNodes_node] at hTallLeft hSingle
          rw [balance_left_double hTallLeft (by omega)]
          simp only [mem_node, or_assoc]
  · by_cases hTallRight : 3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1)
    · cases right with
      | nil => simp only [numNodes_empty] at hTallRight; omega
      | node rightKey rightLeft rightRight =>
        simp only [numNodes_node] at hTallRight
        by_cases hSingle : rightLeft.numNodes ≤ 2 * rightRight.numNodes
        · rw [balance_right_single hTallRight hSingle]
          simp only [mem_node, or_assoc]
        · cases rightLeft with
          | nil => simp only [numNodes_empty] at hSingle; omega
          | node rightLeftKey rightLeftLeft rightLeftRight =>
            simp only [numNodes_node] at hTallRight hSingle
            rw [balance_right_double hTallRight (by omega)]
            simp only [mem_node, or_assoc]
    · rw [balance_eq_node_of_le (by omega) (by omega)]
      simp only [mem_node]

/-- Rebalancing preserves the search-tree ordering invariant. -/
public theorem ordered_balance [LinearOrder α] {key : α} {left right : BinaryTree α}
    (hOrdLeft : BinarySearchTree.Ordered left) (hOrdRight : BinarySearchTree.Ordered right)
    (hAllLeft : BinarySearchTree.All (· < key) left) (hAllRight : BinarySearchTree.All (key < ·) right) :
    BinarySearchTree.Ordered (balance left key right) := by
  by_cases hTallLeft : 3 * (left.numNodes + right.numNodes + 2) < 4 * (left.numNodes + 1)
  · cases left with
    | nil => simp only [numNodes_empty] at hTallLeft; omega
    | node leftKey leftLeft leftRight =>
      obtain ⟨hOrdLeftLeft, hOrdLeftRight, hAllLeftLeft, hAllLeftRight⟩ := hOrdLeft
      obtain ⟨hAllLeftLeftKey, hLeftKeyKey, hAllLeftRightKey⟩ := hAllLeft
      simp only [numNodes_node] at hTallLeft
      by_cases hSingle : leftRight.numNodes ≤ 2 * leftLeft.numNodes
      · rw [balance_left_single hTallLeft hSingle]
        refine ordered_node hOrdLeftLeft
          (ordered_node hOrdLeftRight hOrdRight hAllLeftRightKey hAllRight)
          hAllLeftLeft ⟨hAllLeftRight, hLeftKeyKey, ?_⟩
        exact All_mono (p := (key < ·)) (q := (leftKey < ·))
          (fun _ ha => lt_trans hLeftKeyKey ha) right hAllRight
      · cases leftRight with
        | nil => simp only [numNodes_empty] at hSingle; omega
        | node leftRightKey leftRightLeft leftRightRight =>
          obtain ⟨hOrdLRL, hOrdLRR, hAllLRL, hAllLRR⟩ := hOrdLeftRight
          obtain ⟨hAllLRLKey, hLeftRightKeyKey, hAllLRRKey⟩ := hAllLeftRightKey
          obtain ⟨hAllLRLLeft, hLeftKeyLeftRightKey, hAllLRRLeft⟩ := hAllLeftRight
          simp only [numNodes_node] at hTallLeft hSingle
          rw [balance_left_double hTallLeft (by omega)]
          refine ordered_node
            (ordered_node hOrdLeftLeft hOrdLRL hAllLeftLeft hAllLRLLeft)
            (ordered_node hOrdLRR hOrdRight hAllLRRKey hAllRight)
            ⟨?_, hLeftKeyLeftRightKey, hAllLRL⟩
            ⟨hAllLRR, hLeftRightKeyKey, ?_⟩
          · exact All_mono (p := (· < leftKey)) (q := (· < leftRightKey))
              (fun _ ha => lt_trans ha hLeftKeyLeftRightKey) leftLeft hAllLeftLeft
          · exact All_mono (p := (key < ·)) (q := (leftRightKey < ·))
              (fun _ ha => lt_trans hLeftRightKeyKey ha) right hAllRight
  · by_cases hTallRight : 3 * (left.numNodes + right.numNodes + 2) < 4 * (right.numNodes + 1)
    · cases right with
      | nil => simp only [numNodes_empty] at hTallRight; omega
      | node rightKey rightLeft rightRight =>
        obtain ⟨hOrdRightLeft, hOrdRightRight, hAllRightLeft, hAllRightRight⟩ :=
          hOrdRight
        obtain ⟨hAllRightLeftKey, hKeyRightKey, hAllRightRightKey⟩ := hAllRight
        simp only [numNodes_node] at hTallRight
        by_cases hSingle : rightLeft.numNodes ≤ 2 * rightRight.numNodes
        · rw [balance_right_single hTallRight hSingle]
          refine ordered_node
            (ordered_node hOrdLeft hOrdRightLeft hAllLeft hAllRightLeftKey)
            hOrdRightRight ⟨?_, hKeyRightKey, hAllRightLeft⟩ hAllRightRight
          exact All_mono (p := (· < key)) (q := (· < rightKey))
            (fun _ ha => lt_trans ha hKeyRightKey) left hAllLeft
        · cases rightLeft with
          | nil => simp only [numNodes_empty] at hSingle; omega
          | node rightLeftKey rightLeftLeft rightLeftRight =>
            obtain ⟨hOrdRLL, hOrdRLR, hAllRLL, hAllRLR⟩ := hOrdRightLeft
            obtain ⟨hAllRLLKey, hKeyRightLeftKey, hAllRLRKey⟩ := hAllRightLeftKey
            obtain ⟨hAllRLLRight, hRightLeftKeyRightKey, hAllRLRRight⟩ :=
              hAllRightLeft
            simp only [numNodes_node] at hTallRight hSingle
            rw [balance_right_double hTallRight (by omega)]
            refine ordered_node
              (ordered_node hOrdLeft hOrdRLL hAllLeft hAllRLLKey)
              (ordered_node hOrdRLR hOrdRightRight hAllRLRRight hAllRightRight)
              ⟨?_, hKeyRightLeftKey, hAllRLL⟩
              ⟨hAllRLR, hRightLeftKeyRightKey, ?_⟩
            · exact All_mono (p := (· < key)) (q := (· < rightLeftKey))
                (fun _ ha => lt_trans ha hKeyRightLeftKey) left hAllLeft
            · exact All_mono (p := (rightKey < ·)) (q := (rightLeftKey < ·))
                (fun _ ha => lt_trans hRightLeftKeyRightKey ha) rightRight
                hAllRightRight
    · rw [balance_eq_node_of_le (by omega) (by omega)]
      exact ordered_node hOrdLeft hOrdRight hAllLeft hAllRight

/-- Insertion increases the number of keys by at most one. -/
public theorem numNodes_insert_le [LinearOrder α] {x : α} {tree : BinaryTree α} :
    (insert x tree).numNodes ≤ tree.numNodes + 1 := by
  induction tree with
  | nil => simp [insert]
  | node key left right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · have hEq : insert x (.node key left right) =
          balance (insert x left) key right := by
        simp [insert, hXLeft]
      rw [hEq, numNodes_balance]
      simp only [numNodes_node]
      omega
    · by_cases hXRight : key < x
      · have hEq : insert x (.node key left right) =
            balance left key (insert x right) := by
          simp [insert, hXLeft, hXRight]
        rw [hEq, numNodes_balance]
        simp only [numNodes_node]
        omega
      · have hEq : insert x (.node key left right) = .node key left right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        omega

/-- Insertion never decreases the size. -/
public theorem le_numNodes_insert [LinearOrder α] {x : α} {tree : BinaryTree α} :
    tree.numNodes ≤ (insert x tree).numNodes := by
  induction tree with
  | nil => simp [insert]
  | node key left right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · have hEq : insert x (.node key left right) =
          balance (insert x left) key right := by
        simp [insert, hXLeft]
      rw [hEq, numNodes_balance]
      simp only [numNodes_node]
      omega
    · by_cases hXRight : key < x
      · have hEq : insert x (.node key left right) =
            balance left key (insert x right) := by
          simp [insert, hXLeft, hXRight]
        rw [hEq, numNodes_balance]
        simp only [numNodes_node]
        omega
      · have hEq : insert x (.node key left right) = .node key left right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]

/-- Insertion preserves the weight-balance invariant. -/
public theorem balanced_insert [LinearOrder α] {x : α} {tree : BinaryTree α}
    (hBal : Balanced tree) : Balanced (insert x tree) := by
  induction tree with
  | nil => exact balanced_node trivial trivial (by simp) (by simp)
  | node key left right ihLeft ihRight =>
    obtain ⟨hBalL, hBalR, hBalA, hBalB⟩ := hBal
    by_cases hXLeft : x < key
    · have hEq : insert x (.node key left right) =
          balance (insert x left) key right := by
        simp [insert, hXLeft]
      rw [hEq]
      refine balanced_balance (ihLeft hBalL) hBalR ?_ ?_
      · have hBound : (insert x left).numNodes ≤ left.numNodes + 1 := numNodes_insert_le
        have hBound' : left.numNodes ≤ (insert x left).numNodes := le_numNodes_insert
        omega
      · have hBound : (insert x left).numNodes ≤ left.numNodes + 1 := numNodes_insert_le
        have hBound' : left.numNodes ≤ (insert x left).numNodes := le_numNodes_insert
        omega
    · by_cases hXRight : key < x
      · have hEq : insert x (.node key left right) =
            balance left key (insert x right) := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        refine balanced_balance hBalL (ihRight hBalR) ?_ ?_
        · have hBound : (insert x right).numNodes ≤ right.numNodes + 1 := numNodes_insert_le
          have hBound' : right.numNodes ≤ (insert x right).numNodes := le_numNodes_insert
          omega
        · have hBound : (insert x right).numNodes ≤ right.numNodes + 1 := numNodes_insert_le
          have hBound' : right.numNodes ≤ (insert x right).numNodes := le_numNodes_insert
          omega
      · have hEq : insert x (.node key left right) = .node key left right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ⟨hBalL, hBalR, hBalA, hBalB⟩

/-- Inserting a key adds exactly that key to structural membership. -/
public theorem mem_insert [LinearOrder α] {x y : α} {tree : BinaryTree α} :
    y ∈ insert x tree ↔ y = x ∨ y ∈ tree := by
  induction tree with
  | nil => simp [insert]
  | node key left right ihLeft ihRight =>
    by_cases hXLeft : x < key
    · have hEq : insert x (.node key left right) =
          balance (insert x left) key right := by
        simp [insert, hXLeft]
      rw [hEq]
      simp [mem_balance, ihLeft, or_assoc, or_left_comm]
    · by_cases hXRight : key < x
      · have hEq : insert x (.node key left right) =
            balance left key (insert x right) := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        simp [mem_balance, ihRight, or_left_comm]
      · have hEq : insert x (.node key left right) = .node key left right := by
          simp [insert, hXLeft, hXRight]
        have hxEq : x = key := le_antisymm (le_of_not_gt hXRight) (le_of_not_gt hXLeft)
        subst x
        rw [hEq]
        constructor
        · exact Or.inr
        · rintro (rfl | hy)
          · exact Or.inr (Or.inl rfl)
          · exact hy

private theorem all_insert [LinearOrder α] {p : α → Prop} {x : α} {tree : BinaryTree α}
    (hx : p x) (hTree : BinarySearchTree.All p tree) : BinarySearchTree.All p (insert x tree) := by
  rw [BinarySearchTree.all_iff_forall_mem] at hTree
  rw [BinarySearchTree.all_iff_forall_mem]
  intro y hy
  rw [mem_insert] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hTree y hy

/-- Insertion preserves the strict search-tree invariant. -/
public theorem ordered_insert [LinearOrder α] {x : α} {tree : BinaryTree α}
    (hTree : BinarySearchTree.Ordered tree) : BinarySearchTree.Ordered (insert x tree) := by
  induction tree with
  | nil => simp [insert, BinarySearchTree.Ordered, BinarySearchTree.All]
  | node key left right ihLeft ihRight =>
    obtain ⟨hLeft, hRight, hAllLeft, hAllRight⟩ := hTree
    by_cases hXLeft : x < key
    · have hEq : insert x (.node key left right) =
          balance (insert x left) key right := by
        simp [insert, hXLeft]
      rw [hEq]
      exact ordered_balance (ihLeft hLeft) hRight (all_insert hXLeft hAllLeft)
        hAllRight
    · by_cases hXRight : key < x
      · have hEq : insert x (.node key left right) =
            balance left key (insert x right) := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ordered_balance hLeft (ihRight hRight) hAllLeft
          (all_insert hXRight hAllRight)
      · have hEq : insert x (.node key left right) = .node key left right := by
          simp [insert, hXLeft, hXRight]
        rw [hEq]
        exact ⟨hLeft, hRight, hAllLeft, hAllRight⟩

/-- Trees built by insertion are balanced. -/
public theorem balanced_fromList [LinearOrder α] {xs : List α} :
    Balanced (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact balanced_insert ih

/-- Building a tree by insertion always produces an ordered tree. -/
public theorem ordered_fromList [LinearOrder α] {xs : List α} :
    BinarySearchTree.Ordered (fromList xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ordered_insert ih

/-- A key is in a tree built from a list exactly when it is in the list. -/
public theorem mem_fromList [LinearOrder α] {x : α} {xs : List α} :
    x ∈ fromList xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [fromList]
  | cons y ys ih => simp [fromList, mem_insert, ih]

/-- The weight of a balanced tree grows at least geometrically in its
height with ratio `4 / 3`: a balanced tree of height `k + 1` has weight
at least `(4 / 3) ^ k`, in integer form `4 ^ k ≤ 3 ^ k * weight tree`.
This is where the weight form of the invariant is used: the taller child
has weight at most three quarters of the weight of the node. -/
public theorem pow_height_le {tree : BinaryTree α} (hBal : Balanced tree) :
    ∀ k : Nat, BinaryTree.height tree = k + 1 → 4 ^ k ≤ 3 ^ k * weight tree := by
  induction tree with
  | nil =>
      intro k hk
      simp only [BinaryTree.height] at hk
      omega
  | node key left right ihLeft ihRight =>
      obtain ⟨hBalL, hBalR, hA, hB⟩ := hBal
      intro k hk
      simp only [BinaryTree.height] at hk
      cases k with
      | zero =>
          simp only [pow_zero, one_mul, weight, numNodes_node]
          omega
      | succ k =>
          rcases le_total (BinaryTree.height left) (BinaryTree.height right) with hle | hle
          · have hmax : max (BinaryTree.height left) (BinaryTree.height right) = BinaryTree.height right :=
              Nat.max_eq_right hle
            have hTall : BinaryTree.height right = k + 1 := by omega
            have ih := ihRight hBalR k hTall
            calc 4 ^ (k + 1) = 4 * 4 ^ k := by ring
              _ ≤ 4 * (3 ^ k * weight right) :=
                Nat.mul_le_mul (Nat.le_refl 4) ih
              _ = 3 ^ k * (4 * weight right) := by ring
              _ ≤ 3 ^ k * (3 * weight (BinaryTree.node key left right)) :=
                Nat.mul_le_mul (Nat.le_refl _)
                  (by simp only [weight, numNodes_node]; omega)
              _ = 3 ^ (k + 1) * weight (BinaryTree.node key left right) := by
                ring
          · have hmax : max (BinaryTree.height left) (BinaryTree.height right) = BinaryTree.height left :=
              Nat.max_eq_left hle
            have hTall : BinaryTree.height left = k + 1 := by omega
            have ih := ihLeft hBalL k hTall
            calc 4 ^ (k + 1) = 4 * 4 ^ k := by ring
              _ ≤ 4 * (3 ^ k * weight left) :=
                Nat.mul_le_mul (Nat.le_refl 4) ih
              _ = 3 ^ k * (4 * weight left) := by ring
              _ ≤ 3 ^ k * (3 * weight (BinaryTree.node key left right)) :=
                Nat.mul_le_mul (Nat.le_refl _)
                  (by simp only [weight, numNodes_node]; omega)
              _ = 3 ^ (k + 1) * weight (BinaryTree.node key left right) := by
                ring

/-- The height of a balanced tree is logarithmic in its number of keys:
`BinaryTree.height tree ≤ Nat.log2 ((tree.numNodes + 1) ^ 3) + 1`. This is the
`Nat.log2` form of `pow_height_le`, using `(4 / 3) ^ 3 > 2` to pass from
base `4 / 3` to base `2`. -/
public theorem height_le_log2 {tree : BinaryTree α} (hBal : Balanced tree) :
    BinaryTree.height tree ≤ Nat.log2 ((tree.numNodes + 1) ^ 3) + 1 := by
  cases tree with
  | nil =>
      simp only [BinaryTree.height]
      exact Nat.zero_le _
  | node key left right =>
      have hHeightPos : 1 ≤ BinaryTree.height (.node key left right) := by
        simp only [BinaryTree.height]; omega
      set k := BinaryTree.height (.node key left right) - 1 with hkDef
      have hkEq : BinaryTree.height (.node key left right) = k + 1 := by omega
      have hPow : 4 ^ k ≤
          3 ^ k * ((BinaryTree.node key left right).numNodes + 1) :=
        pow_height_le hBal k hkEq
      have h2 : 2 ^ k ≤ ((BinaryTree.node key left right).numNodes + 1) ^ 3 := by
        have h54 : (54 : Nat) ^ k ≤ 64 ^ k :=
          Nat.pow_le_pow_left (by decide) k
        have h64 : (64 : Nat) ^ k ≤
            (27 : Nat) ^ k * ((BinaryTree.node key left right).numNodes + 1) ^ 3 := by
          calc (64 : Nat) ^ k = (4 ^ k) ^ 3 := by
                rw [show (64 : Nat) = 4 ^ 3 by decide, ← pow_mul, ← pow_mul,
                  Nat.mul_comm k 3]
            _ ≤ (3 ^ k * ((BinaryTree.node key left right).numNodes + 1)) ^ 3 :=
              Nat.pow_le_pow_left hPow 3
            _ = (27 : Nat) ^ k * ((BinaryTree.node key left right).numNodes + 1) ^ 3 := by
              rw [mul_pow, ← pow_mul, Nat.mul_comm k 3, pow_mul,
                show (3 : Nat) ^ 3 = 27 by decide]
        have h27 : (27 : Nat) ^ k * 2 ^ k ≤
            (27 : Nat) ^ k * ((BinaryTree.node key left right).numNodes + 1) ^ 3 := by
          have h54eq : (54 : Nat) ^ k = (27 : Nat) ^ k * 2 ^ k := by
            rw [show (54 : Nat) = 27 * 2 by decide, mul_pow]
          rw [h54eq] at h54
          exact le_trans h54 h64
        have h2k : 2 ^ k ≤
            ((BinaryTree.node key left right).numNodes + 1) ^ 3 :=
          Nat.le_of_mul_le_mul_left h27 (Nat.pow_pos (by decide : (0 : Nat) < 27))
        exact h2k
      have hkLog : k ≤ Nat.log 2 (((BinaryTree.node key left right).numNodes + 1) ^ 3) :=
        Nat.le_log_of_pow_le (by decide) h2
      rw [← Nat.log2_eq_log_two] at hkLog
      omega

end WeightBalancedTree
end Cslib.Algorithms.Lean
