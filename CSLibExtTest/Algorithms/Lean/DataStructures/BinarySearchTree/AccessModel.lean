/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.AccessModel

/-! # Fixtures for the single-pointer binary search tree access model -/

namespace Cslib.Algorithms.Lean.BinarySearchTree.AccessModel

private theorem four_keys (key : Fin 4) : key = 0 ∨ key = 1 ∨ key = 2 ∨ key = 3 := by
  omega

private def original : Tree 4 where
  tree := .node 3 (.node 1 (.node 0 .nil .nil) (.node 2 .nil .nil)) .nil
  positive := by decide
  ordered := by simp only [Ordered, All]; decide
  full key := by rcases four_keys key with rfl | rfl | rfl | rfl <;> simp

private def rotated : Tree 4 where
  tree := .node 1 (.node 0 .nil .nil) (.node 3 (.node 2 .nil .nil) .nil)
  positive := by decide
  ordered := by simp only [Ordered, All]; decide
  full key := by rcases four_keys key with rfl | rfl | rfl | rfl <;> simp

private def root : Cursor 4 := ⟨3, .node 1 (.node 0 .nil .nil) (.node 2 .nil .nil), .nil, []⟩
private def child : Cursor 4 := ⟨1, .node 0 .nil .nil, .node 2 .nil .nil, [.left 3 .nil]⟩
private def promoted : Cursor 4 := ⟨1, .node 0 .nil .nil, .node 3 (.node 2 .nil .nil) .nil, []⟩
private def demoted : Cursor 4 := ⟨3, .node 2 .nil .nil, .nil, [.right 1 (.node 0 .nil .nil)]⟩

private theorem rootHit : Access original 3 [] original := by
  exact ⟨root, root, [3], rfl, rfl, .nil _, by simp, rfl⟩

example : Serves original [3] [[]] original 1 :=
  ⟨original, 0, rootHit, ⟨rfl, rfl⟩, rfl⟩

example : Serves original [1] [[.left]] original 2 := by
  refine ⟨original, 0, ?_, ⟨rfl, rfl⟩, rfl⟩
  exact ⟨root, child, [3, 1], rfl, rfl, .cons .left (.nil _), by simp, rfl⟩

example : Serves original [1] [[.left, .rotate]] rotated 3 := by
  refine ⟨rotated, 0, ?_, ⟨rfl, rfl⟩, rfl⟩
  exact ⟨root, promoted, [3, 1, 1], rfl, rfl,
    .cons .left (.cons .rotateLeftChild (.nil _)), by simp, rfl⟩

-- The other rotation transfers key 2 back and keeps the pointer on key 3.
example : Step .rotate demoted root := .rotateRightChild

-- The first access hits 1 before ending at 3; the next starts at the new root 1, not at 3.
example : Serves original [1, 1] [[.left, .rotate, .right], []] rotated 5 := by
  refine ⟨rotated, 1, ?_, ⟨rotated, 0, ?_, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨root, demoted, [3, 1, 1, 3], rfl, rfl,
      .cons .left (.cons .rotateLeftChild (.cons .right (.nil _))), by simp, rfl⟩
  · exact ⟨promoted, promoted, [1], rfl, rfl, .nil _, by simp, rfl⟩

example : ¬ ∃ t, Step .parent root t := by
  rintro ⟨t, h⟩
  cases h

example : ¬ ∃ t, Step .rotate root t := by
  rintro ⟨t, h⟩
  cases h

example : ¬ ∃ t, Step .right root t := by
  rintro ⟨t, h⟩
  cases h

example : ¬ Access original 1 [] original := by
  rintro ⟨⟨k, l, r, ctx⟩, t, visits, rfl, h, walk, hit, _⟩
  change BinaryTree.node k l r = original.tree at h
  cases h
  cases walk
  simp at hit

example : ¬ ∃ key : Fin 4, key.val + 1 = 5 := by
  rintro ⟨key, h⟩
  have := key.isLt
  omega

example : IsOfflineMinimum original [] 0 := by
  refine ⟨⟨[], original, rfl, rfl⟩, fun _ _ => Nat.zero_le _⟩

example : IsOfflineMinimum original [3] 1 := by
  refine ⟨⟨[[]], original, original, 0, rootHit, ⟨rfl, rfl⟩, rfl⟩, ?_⟩
  rintro c ⟨plan, finish, legal⟩
  cases plan with
  | nil => cases legal
  | cons ops plan =>
      obtain ⟨mid, tail, _, _, rfl⟩ := legal
      omega

private theorem returnToRoot : Access original 3 [.left, .parent] original := by
  exact ⟨root, root, [3, 1, 3], rfl, rfl,
    .cons .left (.cons .parentOfLeft (.nil _)), by simp, rfl⟩

-- A nontrivial online strategy: pick the path to each key independently, without rotations.
private def childMoves (key : Fin 4) : List Primitive :=
  match key.val with
  | 0 => [.left, .left]
  | 1 => [.left]
  | 2 => [.left, .right]
  | _ => []

private theorem childMoves_access (key : Fin 4) : Access original key (childMoves key) original := by
  rcases four_keys key with rfl | rfl | rfl | rfl
  · refine ⟨root, ⟨0, .nil, .nil, [.left 1 (.node 2 .nil .nil), .left 3 .nil]⟩,
      [3, 1, 0], rfl, rfl, .cons .left (.cons .left (.nil _)), by simp, rfl⟩
  · exact ⟨root, child, [3, 1], rfl, rfl, .cons .left (.nil _), by simp, rfl⟩
  · refine ⟨root, ⟨2, .nil, .nil, [.right 1 (.node 0 .nil .nil), .left 3 .nil]⟩,
      [3, 1, 2], rfl, rfl, .cons .left (.cons .right (.nil _)), by simp, rfl⟩
  · exact rootHit

private def fixedTreeStrategy : Strategy original where
  plan := List.map childMoves
  legal requests := by
    induction requests with
    | nil => exact ⟨original, 0, rfl, rfl⟩
    | cons key requests ih =>
        obtain ⟨finish, cost, legal⟩ := ih
        exact ⟨finish, 1 + (childMoves key).length + cost, original, cost,
          childMoves_access key, legal, rfl⟩

example : Online fixedTreeStrategy := by
  intro pref xs ys
  change ((pref ++ xs).map childMoves).take pref.length =
    ((pref ++ ys).map childMoves).take pref.length
  simp only [List.map_append, List.take_left' (List.length_map (as := pref) childMoves)]

-- A legal planner that peeks at the rest of the input, even though the tree at the end of
-- the first request is identical in the two executions that witness the violation.
private noncomputable def peeking : Strategy original where
  plan requests :=
    if requests = [3, 3] then [[.left, .parent], []]
    else if requests = [3] then [[]]
    else Classical.choose (serves_exists original requests)
  legal requests := by
    split_ifs with h h'
    · subst requests
      exact ⟨original, 4, original, 1, returnToRoot,
        ⟨original, 0, rootHit, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
    · subst requests
      exact ⟨original, 1, original, 0, rootHit, ⟨rfl, rfl⟩, rfl⟩
    · obtain ⟨c, hc⟩ := Classical.choose_spec (serves_exists original requests)
      exact ⟨original, c, hc⟩

example : ¬ Online peeking := by
  intro online
  have h := online [3] [] [3]
  change ([[]] : List (List Primitive)) = [[.left, .parent]] at h
  cases h

end Cslib.Algorithms.Lean.BinarySearchTree.AccessModel
