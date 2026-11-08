/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree
public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.RedBlackTree.DeleteBalanced

/-!
# Tests for the red-black tree API

These client examples exercise insertion and both deletion strategies
(rebuild-based `delete` and double-black `DeleteBalanced.deleteBal`)
through the public executable and correctness API: empty trees, duplicate
and missing keys, root and black-leaf deletion, two-child deletion, and
the unconditional validity guarantee of rebuild-based deletion. The
double-black repair branches (red far/near nephews and their mirrors) are
covered by direct kernel computations (`by decide`) on dedicated valid
fixtures that check the exact rotated trees, not only their traversals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RedBlackTreeTests

open RedBlackTree

private theorem inorder_fromList_of_sorted {xs : List Nat}
    (h : List.Pairwise (· < ·) xs) : inorder (fromList xs) = xs :=
  List.Pairwise.eq_of_mem_iff (ordered_inorder valid_fromList.1) h
    (fun a => by rw [mem_inorder, mem_fromList])

/-- A seven-key valid tree used across the deletion tests. -/
public def tree7 : RedBlackTree.Tree Nat := fromList [1, 2, 3, 4, 5, 6, 7]

private theorem tree7_valid : Valid tree7 := valid_fromList

private theorem tree7_inorder : inorder tree7 = [1, 2, 3, 4, 5, 6, 7] :=
  inorder_fromList_of_sorted (by decide)

private theorem tree7_mem {a : Nat} : a ∈ tree7 ↔ a ∈ [1, 2, 3, 4, 5, 6, 7] :=
  mem_fromList

example : Valid tree7 := tree7_valid

example : inorder tree7 = [1, 2, 3, 4, 5, 6, 7] := tree7_inorder

/-- Traversal is inherited from `BinarySearchTree` through `erase`. -/
example : inorder tree7 = BinarySearchTree.inorder (erase tree7) :=
  inorder_erase tree7

example : (inorder tree7).Nodup :=
  BinarySearchTree.inorder_nodup tree7_valid.1

example : (4 : Nat) ∈ tree7 := tree7_mem.mpr (by decide)

example : (9 : Nat) ∉ tree7 := fun h => by
  have h9 := tree7_mem.mp h
  revert h9; decide

example : contains 4 tree7 = true :=
  (contains_eq_true_iff tree7_valid.1).mpr (tree7_mem.mpr (by decide))

example : contains 9 tree7 = false := by
  cases h : contains 9 tree7 with
  | false => rfl
  | true =>
      have h9 := tree7_mem.mp ((contains_eq_true_iff tree7_valid.1).mp h)
      revert h9; decide

/-- Duplicate insertion leaves membership and validity unchanged. -/
example : Valid (insert 4 tree7) := valid_insert tree7_valid

example : ∀ y : Nat, y ∈ insert 4 tree7 ↔ y = 4 ∨ y ∈ tree7 :=
  fun _ => mem_insert

example : inorder (insert 4 tree7) = [1, 2, 3, 4, 5, 6, 7] := by
  refine List.Pairwise.eq_of_mem_iff
    (ordered_inorder (valid_insert tree7_valid).1) (by decide) (fun a => ?_)
  rw [mem_inorder, mem_insert]
  constructor
  · rintro (rfl | h)
    · decide
    · exact tree7_mem.mp h
  · intro h
    exact Or.inr (tree7_mem.mpr h)

/-! ### Rebuild-based deletion (`delete`) -/

example : inorder (delete 4 (.empty : RedBlackTree.Tree Nat)) = [] := by
  rw [inorder_delete (tree := .empty) trivial]
  rfl

/-- Deleting the root/middle (two-child) key of a seven-key tree. -/
example : inorder (delete 4 tree7) = [1, 2, 3, 5, 6, 7] := by
  rw [inorder_delete tree7_valid.1, tree7_inorder]
  rfl

example : inorder (delete 1 tree7) = [2, 3, 4, 5, 6, 7] := by
  rw [inorder_delete tree7_valid.1, tree7_inorder]
  rfl

example : inorder (delete 7 tree7) = [1, 2, 3, 4, 5, 6] := by
  rw [inorder_delete tree7_valid.1, tree7_inorder]
  rfl

/-- Deleting a missing key leaves the contents unchanged. -/
example : inorder (delete 9 tree7) = [1, 2, 3, 4, 5, 6, 7] := by
  rw [inorder_delete tree7_valid.1, tree7_inorder]
  rfl

example : (4 : Nat) ∉ delete 4 tree7 := not_mem_delete_self tree7_valid.1

example : Valid (delete 4 tree7) := valid_delete

/-- An invalid input: unordered and with a red-red redex at the root. -/
public def malformed : RedBlackTree.Tree Nat :=
  .node .red (.node .red .empty 5 .empty) 3 .empty

example : ¬ Ordered malformed := by
  intro h
  have h5 : (5 : Nat) < 3 := (all_iff_forall_mem.mp h.2.2.1) 5 (Or.inr (Or.inl rfl))
  omega

/-- Rebuild-based deletion is valid unconditionally, even on `malformed`. -/
example : Valid (delete 3 malformed) := valid_delete

example : Ordered (delete 3 malformed) := ordered_delete

example : RedOk (delete 3 malformed) := redOk_delete

example : Balanced (delete 3 malformed) := balanced_delete

example : colorOf (delete 3 malformed) = .black := colorOf_delete

/-! ### Double-black deletion (`DeleteBalanced.deleteBal`) -/

open DeleteBalanced

example : inorder (deleteBal 4 (.empty : RedBlackTree.Tree Nat)) = [] := by
  rw [inorder_deleteBal (tree := .empty) trivial]
  rfl

/-- Deleting the middle (two-child) key. -/
example : inorder (deleteBal 4 tree7) = [1, 2, 3, 5, 6, 7] := by
  rw [inorder_deleteBal tree7_valid.1, tree7_inorder]
  rfl

/-- Deleting black leaves of the all-black `tree7` takes the
black-sibling/two-black-nephew bubbling path. The red-nephew rotation
paths need red nephews and are covered by the fixtures below. -/
example : inorder (deleteBal 1 tree7) = [2, 3, 4, 5, 6, 7] := by
  rw [inorder_deleteBal tree7_valid.1, tree7_inorder]
  rfl

example : inorder (deleteBal 7 tree7) = [1, 2, 3, 4, 5, 6] := by
  rw [inorder_deleteBal tree7_valid.1, tree7_inorder]
  rfl

/-- The same bubbling deletions by direct kernel computation, reducing
`deleteBal` itself rather than rewriting with its specification. -/
example : inorder (deleteBal 1 tree7) = [2, 3, 4, 5, 6, 7] := by decide

example : inorder (deleteBal 7 tree7) = [1, 2, 3, 4, 5, 6] := by decide

/-! ### Double-black repair branches: red near/far nephews

Each fixture is a small valid tree in which deleting the black leaf
creates a deficit whose sibling is black with a single red nephew. The
exact result trees distinguish the branches: a red *far* nephew is
repaired by a single rotation (the sibling key becomes the root), a red
*near* nephew by a double rotation (the nephew key becomes the root).
Both mirrored directions (`fixLeft` for a left deficit, `fixRight` for a
right deficit) are covered, and every result is checked by `decide`,
which kernel-reduces `deleteBal` on the fixture. -/

/-- Left deficit, red far (right) nephew `7`: single rotation. -/
public def fixtureFarLeft : RedBlackTree.Tree Nat :=
  .node .black (.node .black .empty 2 .empty) 4
    (.node .black .empty 6 (.node .red .empty 7 .empty))

/-- Left deficit, red near (left) nephew `5`: double rotation. -/
public def fixtureNearLeft : RedBlackTree.Tree Nat :=
  .node .black (.node .black .empty 2 .empty) 4
    (.node .black (.node .red .empty 5 .empty) 6 .empty)

/-- Right deficit, red far (left) nephew `1`: single rotation. -/
public def fixtureFarRight : RedBlackTree.Tree Nat :=
  .node .black (.node .black (.node .red .empty 1 .empty) 2 .empty) 4
    (.node .black .empty 6 .empty)

/-- Right deficit, red near (right) nephew `3`: double rotation. -/
public def fixtureNearRight : RedBlackTree.Tree Nat :=
  .node .black (.node .black .empty 2 (.node .red .empty 3 .empty)) 4
    (.node .black .empty 6 .empty)

private theorem fixtureFarLeft_valid : Valid fixtureFarLeft := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [fixtureFarLeft, Ordered, RedOk, Balanced, blackHeight, colorOf,
      BinarySearchTree.Ordered, BinarySearchTree.All, erase]

private theorem fixtureNearLeft_valid : Valid fixtureNearLeft := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [fixtureNearLeft, Ordered, RedOk, Balanced, blackHeight, colorOf,
      BinarySearchTree.Ordered, BinarySearchTree.All, erase]

private theorem fixtureFarRight_valid : Valid fixtureFarRight := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [fixtureFarRight, Ordered, RedOk, Balanced, blackHeight, colorOf,
      BinarySearchTree.Ordered, BinarySearchTree.All, erase]

private theorem fixtureNearRight_valid : Valid fixtureNearRight := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp [fixtureNearRight, Ordered, RedOk, Balanced, blackHeight, colorOf,
      BinarySearchTree.Ordered, BinarySearchTree.All, erase]

example : Valid fixtureFarLeft := fixtureFarLeft_valid

example : Valid fixtureNearLeft := fixtureNearLeft_valid

example : Valid fixtureFarRight := fixtureFarRight_valid

example : Valid fixtureNearRight := fixtureNearRight_valid

/-- Far nephew, left deficit: one rotation puts the sibling key `6` at
the root. -/
example : deleteBal 2 fixtureFarLeft =
    .node .black (.node .black .empty 4 .empty) 6
      (.node .black .empty 7 .empty) := by decide

/-- Near nephew, left deficit: two rotations put the nephew key `5` at
the root. -/
example : deleteBal 2 fixtureNearLeft =
    .node .black (.node .black .empty 4 .empty) 5
      (.node .black .empty 6 .empty) := by decide

/-- Far nephew, right deficit (mirror): the sibling key `2` at the root. -/
example : deleteBal 6 fixtureFarRight =
    .node .black (.node .black .empty 1 .empty) 2
      (.node .black .empty 4 .empty) := by decide

/-- Near nephew, right deficit (mirror): the nephew key `3` at the root. -/
example : deleteBal 6 fixtureNearRight =
    .node .black (.node .black .empty 2 .empty) 3
      (.node .black .empty 4 .empty) := by decide

example : inorder (deleteBal 2 fixtureFarLeft) = [4, 6, 7] := by decide

example : inorder (deleteBal 2 fixtureNearLeft) = [4, 5, 6] := by decide

example : inorder (deleteBal 6 fixtureFarRight) = [1, 2, 4] := by decide

example : inorder (deleteBal 6 fixtureNearRight) = [2, 3, 4] := by decide

example : Valid (deleteBal 2 fixtureFarLeft) :=
  valid_deleteBal fixtureFarLeft_valid

example : Valid (deleteBal 2 fixtureNearLeft) :=
  valid_deleteBal fixtureNearLeft_valid

example : Valid (deleteBal 6 fixtureFarRight) :=
  valid_deleteBal fixtureFarRight_valid

example : Valid (deleteBal 6 fixtureNearRight) :=
  valid_deleteBal fixtureNearRight_valid

/-- Repeated deletion drains the tree in order. -/
example : inorder (deleteBal 3 (deleteBal 1 tree7)) = [2, 4, 5, 6, 7] := by
  rw [inorder_deleteBal (ordered_deleteBal tree7_valid.1),
    inorder_deleteBal tree7_valid.1, tree7_inorder]
  rfl

/-- Deleting a missing key leaves the contents unchanged. -/
example : inorder (deleteBal 9 tree7) = [1, 2, 3, 4, 5, 6, 7] := by
  rw [inorder_deleteBal tree7_valid.1, tree7_inorder]
  rfl

example : (4 : Nat) ∉ deleteBal 4 tree7 :=
  not_mem_deleteBal_self tree7_valid.1

example : Valid (deleteBal 4 tree7) := valid_deleteBal tree7_valid

example : Valid (deleteBal 1 (deleteBal 7 tree7)) :=
  valid_deleteBal (valid_deleteBal tree7_valid)

example : colorOf (deleteBal 4 tree7) = .black := colorOf_deleteBal

/-- Both deletion strategies agree on contents for valid trees. -/
example : inorder (delete 4 tree7) = inorder (deleteBal 4 tree7) := by
  rw [inorder_delete tree7_valid.1, inorder_deleteBal tree7_valid.1]

/-- The public double-black API can be reasoned about abstractly, through
its published constructor and preservation lemmas alone. -/
example (left right : RedBlackTree.Tree Nat) (key : Nat) :
    inorder (blacken (.nodeBB left key right)) =
      inorder left ++ key :: inorder right := by
  rw [inorder_blacken, inorderBB_nodeBB]

example (tree : BBTree Nat) (hb : BalancedBB tree) (hr : RedOkBB tree) :
    Balanced (blacken tree) ∧ RedOk (blacken tree) ∧
      colorOf (blacken tree) = .black :=
  ⟨balanced_blacken hb, redOk_blacken hr, colorOf_blacken⟩

example : colorBB (.emptyBB : BBTree Nat) = .doubleBlack := colorBB_emptyBB

example : blacken (.emptyBB : BBTree Nat) = .empty := blacken_emptyBB

#check DeleteBalanced.inorder_blacken
#check DeleteBalanced.balanced_blacken
#check DeleteBalanced.redOk_blacken
#check DeleteBalanced.colorOf_blacken
#check DeleteBalanced.inorderBB_nodeBB
#check DeleteBalanced.blacken_nodeBB
#check DeleteBalanced.rootBlack
#check DeleteBalanced.incrBlack
#check DeleteBalanced.colorBB_regular_red
#check DeleteBalanced.incrBlack_node_black

/-- `rootBlack` and `incrBlack` are usable abstractly through their
published constructor equations. -/
example (left right : RedBlackTree.Tree Nat) (key : Nat) :
    blacken (incrBlack (.node .black left key right)) =
      .node .black left key right := by
  rw [incrBlack_node_black, blacken_nodeBB]

example (left right : RedBlackTree.Tree Nat) (key : Nat) :
    colorBB (.regular (.node .red left key right)) = .red :=
  colorBB_regular_red

#print axioms valid_delete
#print axioms valid_deleteBal
#print axioms inorder_deleteBal

end Cslib.Algorithms.Lean.RedBlackTreeTests
