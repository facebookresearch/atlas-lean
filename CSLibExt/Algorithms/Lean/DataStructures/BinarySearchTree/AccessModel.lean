/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Find

/-!
# The binary search tree access model

Following John Iacono, *In pursuit of the dynamic optimality conjecture*, §1
(<https://arxiv.org/abs/1306.0207>), a single pointer visits each request, using edge
moves and rotations. We charge one additional unit per request. These are mathematical
event counts, not the running time of an implementation or of choosing the operations.
Keys in `Fin n` label the source's keys `1, …, n` by `i ↦ i.val + 1`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.BinarySearchTree.AccessModel

/-- A strict binary search tree containing each of the `n > 0` keys, with `Fin n` relabeled
by `i ↦ i.val + 1`. Strict ordering excludes duplicates. -/
structure Tree (n : ℕ) where
  tree : BinaryTree (Fin n)
  positive : 0 < n
  ordered : Ordered tree
  full : ∀ key, key ∈ tree

-- A frame records which child the pointer came from, the parent key, and the sibling subtree.
inductive Frame (n : ℕ) where
  | left (key : Fin n) (right : BinaryTree (Fin n))
  | right (key : Fin n) (left : BinaryTree (Fin n))

-- The focused node is nonempty by construction; the immediate parent is first in the list.
structure Cursor (n : ℕ) where
  key : Fin n
  left : BinaryTree (Fin n)
  right : BinaryTree (Fin n)
  parents : List (Frame n)

-- Reattach a subtree to one parent.
def Frame.plug {n : ℕ} (t : BinaryTree (Fin n)) : Frame n → BinaryTree (Fin n)
  | .left k r => .node k t r
  | .right k l => .node k l t

-- The whole tree is recovered by folding the parent frames from nearest to farthest.
def Cursor.tree {n : ℕ} (s : Cursor n) : BinaryTree (Fin n) :=
  s.parents.foldl Frame.plug (.node s.key s.left s.right)

/-- The four unit-cost operations: move to the left child, right child, or parent, or rotate
with the parent. Whether an operation is legal depends on the current pointer position. -/
inductive Primitive where
  | left | right | parent | rotate

/-- A legal operation of the single pointer. A move follows an existing edge without changing
the tree. A rotation promotes the focused node over its immediate parent, transferring the
middle subtree to the old parent. The pointer stays on the same key, now at the promoted node. -/
inductive Step {n : ℕ} : Primitive → Cursor n → Cursor n → Prop where
  | left {p k a b c ctx} :
      Step .left ⟨p, .node k a b, c, ctx⟩ ⟨k, a, b, .left p c :: ctx⟩
  | right {p k a b c ctx} :
      Step .right ⟨p, a, .node k b c, ctx⟩ ⟨k, b, c, .right p a :: ctx⟩
  | parentOfLeft {p k a b c ctx} :
      Step .parent ⟨k, a, b, .left p c :: ctx⟩ ⟨p, .node k a b, c, ctx⟩
  | parentOfRight {p k a b c ctx} :
      Step .parent ⟨k, b, c, .right p a :: ctx⟩ ⟨p, a, .node k b c, ctx⟩
  | rotateLeftChild {p k a b c ctx} :
      Step .rotate ⟨k, a, b, .left p c :: ctx⟩ ⟨k, a, .node p b c, ctx⟩
  | rotateRightChild {p k a b c ctx} :
      Step .rotate ⟨k, b, c, .right p a :: ctx⟩ ⟨k, .node p a b, c, ctx⟩

/-- A finite walk under the primitive rules, recording the initial key and the key after
 each operation, in order. -/
inductive Walk {n : ℕ} : List Primitive → Cursor n → Cursor n → List (Fin n) → Prop where
  | nil (s : Cursor n) : Walk [] s s [s.key]
  | cons {op ops s u t visits} :
      Step op s u → Walk ops u t visits → Walk (op :: ops) s t (s.key :: visits)

/-- A legal single access starts at the root of the current tree, walks according to its
operation list, and touches the requested key somewhere in its visit list. Its final tree
is the tree at the end of the walk, regardless of the final pointer position. -/
def Access {n : ℕ} (start : Tree n) (key : Fin n) (ops : List Primitive) (finish : Tree n) : Prop :=
  ∃ (s t : Cursor n) (visits : List (Fin n)),
    s.parents = [] ∧ s.tree = start.tree ∧ Walk ops s t visits ∧
      key ∈ visits ∧ t.tree = finish.tree

/-- **The binary search tree access model.** For a fixed `n > 0`, the initial and final
states are strict trees containing every key of `Fin n`. Requests form a finite list of
keys in `Fin n`, and a plan gives exactly one list of primitive operations per request;
a length mismatch is rejected. The pointer starts at the current root on every request,
for free. Each walk must visit its request, and its resulting tree is used for the next
access. The given final tree is the last resulting tree, and the given natural-number
cost is the sum of one plus the number of primitive operations for each request. The
empty plan on the empty sequence costs zero and leaves the tree unchanged. -/
def Serves {n : ℕ} (start : Tree n) :
    List (Fin n) → List (List Primitive) → Tree n → ℕ → Prop
  | [], [], finish, cost => finish = start ∧ cost = 0
  | x :: xs, ops :: plan, finish, cost =>
      ∃ mid tailCost, Access start x ops mid ∧ Serves mid xs plan finish tailCost ∧
        cost = 1 + ops.length + tailCost
  | _, _, _, _ => False

/-- The offline optimum is an attained least cost among all legal plans for the given requests
from the same initial tree. The plan may depend on the entire request sequence. -/
def IsOfflineMinimum {n : ℕ} (start : Tree n) (requests : List (Fin n)) (cost : ℕ) : Prop :=
  IsLeast {c | ∃ plan finish, Serves start requests plan finish c} cost

/-- A strategy for a fixed initial tree chooses a legal plan for every finite request list. -/
structure Strategy {n : ℕ} (start : Tree n) where
  plan : List (Fin n) → List (List Primitive)
  legal : ∀ requests, ∃ finish cost, Serves start requests (plan requests) finish cost

/-- A strategy is online if on any common request prefix its complete operation lists agree,
independently of both suffixes (including their lengths). -/
def Online {n : ℕ} {start : Tree n} (strategy : Strategy start) : Prop :=
  ∀ pref xs ys : List (Fin n),
    (strategy.plan (pref ++ xs)).take pref.length =
      (strategy.plan (pref ++ ys)).take pref.length

private theorem inorder_foldl {n : ℕ} (ctx : List (Frame n))
    {s t : BinaryTree (Fin n)} (h : inorder s = inorder t) :
    inorder (ctx.foldl Frame.plug s) = inorder (ctx.foldl Frame.plug t) := by
  induction ctx generalizing s t with
  | nil => exact h
  | cons f ctx ih => cases f <;> exact ih (by simp [Frame.plug, h])

-- The inorder traversal is unchanged even when the rotation is below the root.
theorem Step.inorder_eq {n : ℕ} {op : Primitive} {s t : Cursor n} (h : Step op s t) :
    inorder s.tree = inorder t.tree := by
  cases h
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [Cursor.tree, List.foldl_cons, Frame.plug]
    apply inorder_foldl
    simp [List.append_assoc]
  · simp only [Cursor.tree, List.foldl_cons, Frame.plug]
    apply inorder_foldl
    simp [List.append_assoc]

private theorem ordered_of_pairwise_inorder {n : ℕ} {tree : BinaryTree (Fin n)}
    (h : List.Pairwise (· < ·) (inorder tree)) : Ordered tree := by
  induction tree with
  | nil => trivial
  | node k l r ihl ihr =>
      rw [inorder_node, List.pairwise_append, List.pairwise_cons] at h
      obtain ⟨hl, ⟨hkr, hr⟩, hlkr⟩ := h
      refine ⟨ihl hl, ihr hr, all_iff_forall_mem.mpr ?_, all_iff_forall_mem.mpr ?_⟩
      · exact fun x hx => hlkr x (mem_inorder.mpr hx) k (List.mem_cons_self ..)
      · exact fun x hx => hkr x (mem_inorder.mpr hx)

-- Starting with a legal tree, every prefix of a legal walk preserves the key-set invariant.
theorem Walk.preservesTree {n : ℕ} {ops : List Primitive} {s t : Cursor n}
    {visits : List (Fin n)} (h : Walk ops s t visits) (start : Tree n) (hs : s.tree = start.tree) :
    ∃ finish : Tree n, t.tree = finish.tree := by
  have hi : inorder s.tree = inorder t.tree := by
    clear start hs
    induction h with
    | nil => rfl
    | cons step _ ih => exact step.inorder_eq.trans ih
  rw [hs] at hi
  refine ⟨⟨t.tree, start.positive, ordered_of_pairwise_inorder ?_, ?_⟩, rfl⟩
  · rw [← hi]
    exact ordered_inorder start.ordered
  · intro key
    exact mem_inorder.mp (hi ▸ mem_inorder.mpr (start.full key))

private theorem walk_to_mem {n : ℕ} (tree : BinaryTree (Fin n)) {key : Fin n}
    (h : key ∈ tree) (ctx : List (Frame n)) :
    ∃ k l r ops finish visits, tree = .node k l r ∧
      Walk ops ⟨k, l, r, ctx⟩ finish visits ∧ key ∈ visits ∧
        finish.tree = (⟨k, l, r, ctx⟩ : Cursor n).tree := by
  induction tree generalizing ctx with
  | nil => exact (mem_nil.mp h).elim
  | node k l r ihl ihr =>
      rcases mem_node.mp h with h | rfl | h
      · obtain ⟨p, a, b, ops, finish, visits, rfl, walk, hit, same⟩ := ihl h (.left k r :: ctx)
        exact ⟨k, _, r, .left :: ops, finish, k :: visits, rfl,
          .cons .left walk, List.mem_cons_of_mem _ hit, same⟩
      · exact ⟨key, l, r, [], _, [key], rfl, .nil _, List.mem_singleton_self _, rfl⟩
      · obtain ⟨p, a, b, ops, finish, visits, rfl, walk, hit, same⟩ := ihr h (.right k l :: ctx)
        exact ⟨k, l, _, .right :: ops, finish, k :: visits, rfl,
          .cons .right walk, List.mem_cons_of_mem _ hit, same⟩

/-- Fix `n > 0` and an initial `Tree n`, a strict binary search tree containing every key
of `Fin n`. Every finite list of requests in `Fin n` has a legal plan and a cost with the
same tree as its final tree: child moves alone suffice to visit each request. -/
theorem serves_exists {n : ℕ} (start : Tree n) (requests : List (Fin n)) :
    ∃ plan cost, Serves start requests plan start cost := by
  induction requests with
  | nil => exact ⟨[], 0, rfl, rfl⟩
  | cons key requests ih =>
      obtain ⟨k, l, r, ops, finish, visits, root, walk, hit, same⟩ :=
        walk_to_mem start.tree (start.full key) []
      obtain ⟨plan, cost, tail⟩ := ih
      refine ⟨ops :: plan, 1 + ops.length + cost, start, cost, ?_, tail, rfl⟩
      exact ⟨⟨k, l, r, []⟩, finish, visits, rfl, root.symm, walk, hit, same.trans root.symm⟩

/-- Fix `n > 0` and an initial `Tree n`, a strict binary search tree containing every key
of `Fin n`. For every finite list of requests in `Fin n`, there is a natural-number cost
attained by a legal plan and least among the costs of legal plans from that initial tree. -/
theorem exists_offlineMinimum {n : ℕ} (start : Tree n) (requests : List (Fin n)) :
    ∃ cost, IsOfflineMinimum start requests cost := by
  classical
  obtain ⟨plan, cost, legal⟩ := serves_exists start requests
  have h : ∃ c, ∃ p t, Serves start requests p t c := ⟨cost, plan, start, legal⟩
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hc => Nat.find_min' h hc⟩

end Cslib.Algorithms.Lean.BinarySearchTree.AccessModel
