/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.MinMax

/-!
# Cartesian trees

The Cartesian tree of a list is the binary tree whose inorder traversal is the
list itself and which is heap-ordered by value: the root is the minimum element,
the left subtree is built from the elements before that minimum, and the right
subtree from the elements after it. This is the treap view of an array: with
priorities in place of values it is the structure behind randomized search trees
and range-minimum queries (La Rocca, *Advanced Algorithms and Data Structures*,
ch. 3; Demaine, MIT 6.851, Lecture 15).

`build` recursively splits its input at the (first) minimum. Recursion is on an
explicit fuel initialized to the input length; each split produces strictly
shorter lists, so the fuel bound `xs.length ≤ n` maintained in the correctness
proofs is exactly termination by list length. When the minimum occurs several
times, splitting at its first occurrence still yields a heap-ordered tree with
the correct inorder traversal.

The machine-checked results are `inorder_build` (the inorder traversal of
`build xs` is `xs`), `heapOrdered_build` (the result satisfies the recursive
`HeapOrdered` predicate), `root_build_min` (the root is a minimum of the input),
and `perm_build` (the elements are a permutation of the input). The split
helper is specified by `splitAtFirst_spec` (reconstruction from the two
parts) together with `splitAtFirst_not_mem_fst` (the split value does not
occur in the left part, i.e. the split is at its first occurrence). No cost model is
formalized; this splitting construction takes quadratic time in the worst case,
while the classic stack-based construction is linear.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace CartesianTree

variable {α : Type u}

/-- Min-heap order: every key is no greater than the keys in its subtrees,
recursively. -/
public def HeapOrdered [LE α] : BinaryTree α → Prop
  | .nil => True
  | .node key left right =>
      HeapOrdered left ∧ HeapOrdered right ∧
        BinarySearchTree.All (key ≤ ·) left ∧
        BinarySearchTree.All (key ≤ ·) right

/-- The root key of a tree, if it has one. -/
public def root : BinaryTree α → Option α
  | .nil => none
  | .node key _ _ => some key

@[simp] public theorem root_empty : root (.nil : BinaryTree α) = none :=
  rfl

@[simp] public theorem root_node {left right : BinaryTree α} {key : α} :
    root (.node key left right) = some key :=
  rfl

/-- `All` is equivalent to universal quantification over the inorder traversal. -/
public theorem all_iff_forall_inorder {p : α → Prop} {tree : BinaryTree α} :
    BinarySearchTree.All p tree ↔
      ∀ x ∈ BinarySearchTree.inorder tree, p x := by
  rw [BinarySearchTree.all_iff_forall_mem]
  constructor
  · intro h x hx
    exact h x (BinarySearchTree.mem_inorder.mp hx)
  · intro h x hx
    exact h x (BinarySearchTree.mem_inorder.mpr hx)

/-- The root of a nonempty tree is a member of the tree. -/
public theorem mem_of_root_eq_some {tree : BinaryTree α} {key : α}
    (hRoot : root tree = some key) : key ∈ tree := by
  cases tree with
  | nil => simp at hRoot
  | node key' left right =>
    simp only [root_node, Option.some.injEq] at hRoot
    subst hRoot
    exact Or.inr (Or.inl rfl)

/-- In a heap-ordered tree, the root is no greater than every member. -/
public theorem root_le_of_heapOrdered [Preorder α] {tree : BinaryTree α}
    {key : α}
    (hHeap : HeapOrdered tree) (hRoot : root tree = some key) :
    ∀ x ∈ tree, key ≤ x := by
  cases tree with
  | nil => simp at hRoot
  | node key' left right =>
    simp only [root_node, Option.some.injEq] at hRoot
    obtain rfl : key' = key := hRoot
    obtain ⟨-, -, hAllLeft, hAllRight⟩ := hHeap
    intro x hx
    rcases hx with hx | rfl | hx
    · exact (BinarySearchTree.all_iff_forall_mem.mp hAllLeft) x hx
    · exact le_refl _
    · exact (BinarySearchTree.all_iff_forall_mem.mp hAllRight) x hx

section SplitAtFirst

variable [DecidableEq α]

/-- Split a list at the first occurrence of `m`, dropping that occurrence.
Only equality on `α` is needed, so this helper and its specification are
generalized over `[DecidableEq α]` rather than the `[LinearOrder α]`
required to build Cartesian trees. -/
public def splitAtFirst (m : α) : List α → List α × List α
  | [] => ([], [])
  | a :: as =>
      if a = m then ([], as)
      else
        let rest := splitAtFirst m as
        (a :: rest.1, rest.2)

public theorem splitAtFirst_spec (m : α) :
    ∀ (xs : List α), m ∈ xs →
      (splitAtFirst m xs).1 ++ m :: (splitAtFirst m xs).2 = xs ∧
        (splitAtFirst m xs).1.length < xs.length ∧
        (splitAtFirst m xs).2.length < xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons a as ih =>
    intro hm
    by_cases ham : a = m
    · subst ham
      have hSplit : splitAtFirst a (a :: as) = ([], as) := by
        simp [splitAtFirst]
      rw [hSplit]
      refine ⟨rfl, by simp, by simp⟩
    · have hmAs : m ∈ as := by
        rcases List.mem_cons.mp hm with h | h
        · exact (ham h.symm).elim
        · exact h
      obtain ⟨hEq, hLenLeft, hLenRight⟩ := ih hmAs
      have hSplit : splitAtFirst m (a :: as) =
          ((a :: (splitAtFirst m as).1), (splitAtFirst m as).2) := by
        simp [splitAtFirst, ham]
      rw [hSplit]
      refine ⟨?_, by simp; omega, by simp; omega⟩
      show (a :: (splitAtFirst m as).1) ++ m :: (splitAtFirst m as).2 = a :: as
      rw [List.cons_append, hEq]

/-- Splitting at the *first* occurrence: the split value does not occur in
the left part. Together with the reconstruction equation in
`splitAtFirst_spec`, this characterizes the split point (including the
duplicate tie-breaking behavior used by `build`) without unfolding the
definition: reconstruction alone would hold for a split at any
occurrence. -/
public theorem splitAtFirst_not_mem_fst (m : α) :
    ∀ (xs : List α), m ∈ xs → m ∉ (splitAtFirst m xs).1 := by
  intro xs
  induction xs with
  | nil => simp
  | cons a as ih =>
    intro hm
    by_cases ham : a = m
    · subst ham
      have hSplit : splitAtFirst a (a :: as) = ([], as) := by
        simp [splitAtFirst]
      rw [hSplit]
      simp
    · have hmAs : m ∈ as := by
        rcases List.mem_cons.mp hm with h | h
        · exact (ham h.symm).elim
        · exact h
      have hSplit : splitAtFirst m (a :: as) =
          ((a :: (splitAtFirst m as).1), (splitAtFirst m as).2) := by
        simp [splitAtFirst, ham]
      rw [hSplit]
      intro hmem
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ham rfl
      · exact ih hmAs hmem

end SplitAtFirst

section Build

variable [LinearOrder α]

/-- The minimum of `a :: as`, computed by folding `min` from the head. -/
public def listMin (a : α) : List α → α
  | [] => a
  | b :: bs => listMin (min a b) bs

private theorem listMin_eq_or_mem (a : α) (as : List α) :
    listMin a as = a ∨ listMin a as ∈ as := by
  induction as generalizing a with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    show listMin (min a b) bs = a ∨ listMin (min a b) bs ∈ b :: bs
    rcases ih (a := min a b) with h | h
    · rw [h]
      rcases min_choice a b with hMin | hMin
      · exact Or.inl hMin
      · exact Or.inr (by simp [hMin])
    · exact Or.inr (List.mem_cons_of_mem b h)

public theorem listMin_mem (a : α) (as : List α) : listMin a as ∈ a :: as := by
  rcases listMin_eq_or_mem a as with h | h
  · simp [h]
  · exact List.mem_cons_of_mem a h

public theorem listMin_le (a : α) (as : List α) :
    listMin a as ≤ a ∧ ∀ y ∈ as, listMin a as ≤ y := by
  induction as generalizing a with
  | nil => exact ⟨le_refl a, by simp⟩
  | cons b bs ih =>
    obtain ⟨hMin, hAll⟩ := ih (a := min a b)
    refine ⟨le_trans hMin (min_le_left a b), ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans hMin (min_le_right _ _)
    · exact hAll y hy

public theorem listMin_le_of_mem {a : α} {as : List α} {y : α} (hy : y ∈ a :: as) :
    listMin a as ≤ y := by
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (listMin_le _ _).1
  · exact (listMin_le _ _).2 _ hy

/-- Build a Cartesian tree with an explicit fuel bound: the recursion splits at
the minimum, so a fuel of at least the input length never runs out. -/
public def buildFuel : Nat → List α → BinaryTree α
  | 0, _ => .nil
  | _ + 1, [] => .nil
  | n + 1, (a :: as) =>
      let m := listMin a as
      let parts := splitAtFirst m (a :: as)
      .node m (buildFuel n parts.1) (buildFuel n parts.2)

public theorem buildFuel_cons (n : Nat) (a : α) (as : List α) :
    buildFuel (n + 1) (a :: as) =
      .node (listMin a as)
        (buildFuel n (splitAtFirst (listMin a as) (a :: as)).1)
        (buildFuel n (splitAtFirst (listMin a as) (a :: as)).2) :=
  rfl

/-- The Cartesian tree of a list: min-heap by value, inorder equal to the list. -/
public def build (xs : List α) : BinaryTree α :=
  buildFuel xs.length xs

public theorem inorder_buildFuel :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n →
      BinarySearchTree.inorder (buildFuel n xs) = xs := by
  intro n
  induction n with
  | zero =>
    intro xs hLen
    have hNil : xs = [] := by
      cases xs with
      | nil => rfl
      | cons a as => simp at hLen
    rw [hNil]
    rfl
  | succ n ih =>
    intro xs hLen
    cases xs with
    | nil => rfl
    | cons a as =>
      set m := listMin a as with hm
      obtain ⟨hEq, hLenLeft, hLenRight⟩ :=
        splitAtFirst_spec m (a :: as) (listMin_mem a as)
      simp only [List.length_cons] at hLen hLenLeft hLenRight
      have hLeft : (splitAtFirst m (a :: as)).1.length ≤ n := by omega
      have hRight : (splitAtFirst m (a :: as)).2.length ≤ n := by omega
      rw [buildFuel_cons, BinarySearchTree.inorder_node, ih _ hLeft, ih _ hRight, hEq]

/-- The inorder traversal of the Cartesian tree of `xs` is `xs` itself. -/
public theorem inorder_build (xs : List α) :
    BinarySearchTree.inorder (build xs) = xs :=
  inorder_buildFuel xs.length xs (le_refl xs.length)

/-- The elements of the Cartesian tree are a permutation of the input. -/
public theorem perm_build (xs : List α) :
    (BinarySearchTree.inorder (build xs)).Perm xs := by
  rw [inorder_build]

/-- Membership in the Cartesian tree agrees with membership in the input. -/
public theorem mem_build {x : α} {xs : List α} : x ∈ build xs ↔ x ∈ xs := by
  rw [← BinarySearchTree.mem_inorder, inorder_build]

public theorem heapOrdered_buildFuel :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → HeapOrdered (buildFuel n xs) := by
  intro n
  induction n with
  | zero =>
    intro xs hLen
    have hNil : xs = [] := by
      cases xs with
      | nil => rfl
      | cons a as => simp at hLen
    rw [hNil]
    trivial
  | succ n ih =>
    intro xs hLen
    cases xs with
    | nil => trivial
    | cons a as =>
      set m := listMin a as with hm
      obtain ⟨hEq, hLenLeft, hLenRight⟩ :=
        splitAtFirst_spec m (a :: as) (listMin_mem a as)
      simp only [List.length_cons] at hLen hLenLeft hLenRight
      have hLeft : (splitAtFirst m (a :: as)).1.length ≤ n := by omega
      have hRight : (splitAtFirst m (a :: as)).2.length ≤ n := by omega
      have hMinLeft : ∀ y ∈ (splitAtFirst m (a :: as)).1, m ≤ y := by
        intro y hy
        apply listMin_le_of_mem (a := a) (as := as)
        rw [← hEq]
        exact List.mem_append_left _ hy
      have hMinRight : ∀ y ∈ (splitAtFirst m (a :: as)).2, m ≤ y := by
        intro y hy
        apply listMin_le_of_mem (a := a) (as := as)
        rw [← hEq]
        exact List.mem_append_right _ (List.mem_cons_of_mem m hy)
      rw [buildFuel_cons]
      refine ⟨ih _ hLeft, ih _ hRight, ?_, ?_⟩
      · rw [all_iff_forall_inorder, inorder_buildFuel n _ hLeft]
        exact hMinLeft
      · rw [all_iff_forall_inorder, inorder_buildFuel n _ hRight]
        exact hMinRight

/-- The Cartesian tree of a list is heap-ordered. -/
public theorem heapOrdered_build (xs : List α) : HeapOrdered (build xs) :=
  heapOrdered_buildFuel xs.length xs (le_refl xs.length)

/-- The Cartesian tree of a nonempty list has a root. -/
public theorem root_build_cons_isSome (a : α) (as : List α) :
    ∃ m, root (build (a :: as)) = some m := by
  have hBuild : build (a :: as) = buildFuel (as.length + 1) (a :: as) := by
    simp [build]
  rw [hBuild, buildFuel_cons]
  exact ⟨listMin a as, rfl⟩

/-- The root of the Cartesian tree is a minimum of the input list. -/
public theorem root_build_min {xs : List α} {m : α}
    (hRoot : root (build xs) = some m) :
    m ∈ xs ∧ ∀ y ∈ xs, m ≤ y := by
  have hMemTree : m ∈ build xs := mem_of_root_eq_some hRoot
  have hLeTree : ∀ x ∈ build xs, m ≤ x :=
    root_le_of_heapOrdered (heapOrdered_build xs) hRoot
  exact ⟨mem_build.mp hMemTree, fun y hy => hLeTree y (mem_build.mpr hy)⟩

end Build

end CartesianTree
end Cslib.Algorithms.Lean
