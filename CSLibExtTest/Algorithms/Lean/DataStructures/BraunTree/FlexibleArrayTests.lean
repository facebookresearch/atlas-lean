/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.FlexibleArray

/-!
# Flexible-array regression tests

Concrete `del_hi` / `add_lo` / `merge` / `del_lo` / `del_lo2` cases,
the `Array` flex operations, the `T*` costs, and restatements of the
correctness specs and the §11.4 logarithmic bounds.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeFlexibleArrayTests

open BraunTree

/-- A complete tree with three elements. -/
private def t3 : Tree Nat := .Node (.Node .Leaf 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A Braun tree with four elements. -/
private def t4 : Tree Nat :=
  .Node (.Node (.Node .Leaf 4 .Leaf) 2 .Leaf) 1 (.Node .Leaf 3 .Leaf)

/-- A singleton tree. -/
private def t9 : Tree Nat := .Node .Leaf 9 .Leaf

example : del_hi 3 t3 = .Node (.Node .Leaf 2 .Leaf) 1 .Leaf := by decide
example : del_hi 4 t4 = t3 := by decide
example : del_hi 1 t3 = .Leaf := by decide
example : del_hi 0 t3 = t3 := by decide

example : add_lo 0 t3 =
    .Node (.Node (.Node .Leaf 3 .Leaf) 1 .Leaf) 0 (.Node .Leaf 2 .Leaf) :=
  by decide
example : add_lo 0 (.Leaf : Tree Nat) = .Node .Leaf 0 .Leaf := by decide
example : list (add_lo 0 t3) = [0, 1, 2, 3] := by simp [list, splice, add_lo, t3]

example : merge t3 t9 =
    .Node t9 1 (.Node (.Node .Leaf 3 .Leaf) 2 .Leaf) := by decide
example : merge (.Leaf : Tree Nat) t3 = t3 := by decide
example : merge t3 (.Leaf : Tree Nat) =
    .Node .Leaf 1 (.Node (.Node .Leaf 3 .Leaf) 2 .Leaf) := by decide
example : list (merge t3 t9) = [1, 9, 2, 3] := by simp [list, splice, merge, t3, t9]

example : del_lo t3 = .Node (.Node .Leaf 3 .Leaf) 2 .Leaf := by decide
example : del_lo (.Leaf : Tree Nat) = .Leaf := by decide
example : list (del_lo t3) = [2, 3] := by simp [list, splice, del_lo, merge, t3]

example : del_lo2 t3 = .Node (.Node .Leaf 3 .Leaf) 2 .Leaf := by simp [del_lo2, t3]
example : del_lo2 (.Leaf : Tree Nat) = .Leaf := by simp [del_lo2]

example : ((Array.ofList [1, 2, 3]).add_lo 0).toList = [0, 1, 2, 3] :=
  (flex_add_lo [1, 2, 3] 0).1
example : ((Array.ofList [1, 2, 3]).del_lo).toList = [2, 3] :=
  (flex_del_lo [1, 2, 3]).1
example : ((Array.ofList [1, 2, 3]).add_hi 4).toList = [1, 2, 3, 4] :=
  (flex_add_hi [1, 2, 3] 4).1
example : ((Array.ofList [1, 2, 3]).del_hi).toList = [1, 2] :=
  (flex_del_hi [1, 2, 3]).1

example : Tdel_hi 3 t3 = 2 := by decide
example : Tdel_hi 1 t3 = 1 := by decide
example : Tadd_lo t3 = 3 := by decide
example : Tmerge t3 t9 = 3 := by decide
example : Tdel_lo t3 = 3 := by decide

/-- Merging the children of a Braun node: Braunness, list, size. -/
example {α : Type u} {l r : Tree α} {x : α} (h : braun (.Node l x r)) :
    braun (merge l r) ∧ list (merge l r) = splice (list l) (list r)
      ∧ size (merge l r) = size l + size r :=
  merge_spec h

/-- `del_lo`: Braunness, list, size. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    braun (del_lo t) ∧ list (del_lo t) = (list t).tail
      ∧ size (del_lo t) = size t - 1 :=
  del_lo_spec h

/-- `add_lo`: Braunness, list, size. -/
example {α : Type u} {t : Tree α} (h : braun t) (x : α) :
    braun (add_lo x t) ∧ list (add_lo x t) = x :: list t
      ∧ size (add_lo x t) = size t + 1 :=
  add_lo_spec h x

/-- `del_hi`: Braunness, list (drop-last), size. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    braun (del_hi (size t) t) ∧ list (del_hi (size t) t) = (list t).dropLast
      ∧ size (del_hi (size t) t) = size t - 1 :=
  del_hi_spec h

/-- Flex `add_lo` on the array built from a list. -/
example {α : Type u} (xs : List α) (x : α) :
    ((Array.ofList xs).add_lo x).toList = x :: xs ∧
      braun (((Array.ofList xs).add_lo x).tree) ∧
      size (((Array.ofList xs).add_lo x).tree) =
        ((Array.ofList xs).add_lo x).n :=
  flex_add_lo xs x

/-- Flex `del_lo` on the array built from a list. -/
example {α : Type u} (xs : List α) :
    ((Array.ofList xs).del_lo).toList = xs.tail ∧
      braun (((Array.ofList xs).del_lo).tree) ∧
      size (((Array.ofList xs).del_lo).tree) = ((Array.ofList xs).del_lo).n :=
  flex_del_lo xs

/-- Flex `add_hi` on the array built from a list. -/
example {α : Type u} (xs : List α) (x : α) :
    ((Array.ofList xs).add_hi x).toList = xs ++ [x] ∧
      braun (((Array.ofList xs).add_hi x).tree) ∧
      size (((Array.ofList xs).add_hi x).tree) =
        ((Array.ofList xs).add_hi x).n :=
  flex_add_hi xs x

/-- Flex `del_hi` on the array built from a list. -/
example {α : Type u} (xs : List α) :
    ((Array.ofList xs).del_hi).toList = xs.dropLast ∧
      braun (((Array.ofList xs).del_hi).tree) ∧
      size (((Array.ofList xs).del_hi).tree) = ((Array.ofList xs).del_hi).n :=
  flex_del_hi xs

/-- Flex `add_lo` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) (x : α) :
    ((a.add_lo x).toList = x :: a.toList) ∧ (a.add_lo x).invar :=
  flex_add_lo_invar h x

/-- Flex `del_lo` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) :
    (a.del_lo.toList = a.toList.tail) ∧ (a.del_lo).invar :=
  flex_del_lo_invar h

/-- Flex `add_hi` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) (x : α) :
    ((a.add_hi x).toList = a.toList ++ [x]) ∧ (a.add_hi x).invar :=
  flex_add_hi_invar h x

/-- Flex `del_hi` on an arbitrary invariant array. -/
example {α : Type u} {a : BraunTree.Array α} (h : a.invar) :
    (a.del_hi.toList = a.toList.dropLast) ∧ (a.del_hi).invar :=
  flex_del_hi_invar h

/-- Exercise 11.6: `del_lo2` is `del_lo`. -/
example {α : Type u} (t : Tree α) : del_lo2 t = del_lo t :=
  del_lo2_eq t

/-- (§11.4): `del_hi` descends along one branch. -/
example (n : ℕ) (t : Tree Nat) : Tdel_hi n t ≤ height t + 1 :=
  Tdel_hi_le n t

/-- (§11.4): `add_lo` descends along one branch. -/
example {α : Type u} (t : Tree α) : Tadd_lo t ≤ height t + 1 :=
  Tadd_lo_le t

/-- (§11.4): `merge` descends along one branch of its first argument. -/
example {α : Type u} (t₁ t₂ : Tree α) : Tmerge t₁ t₂ ≤ height t₁ + 1 :=
  Tmerge_le t₁ t₂

/-- (§11.4): `del_lo` is one `merge` along one branch. -/
example {α : Type u} (t : Tree α) : Tdel_lo t ≤ height t + 1 :=
  Tdel_lo_le t

/-- (§11.4): `del_hi` is logarithmic on Braun trees. -/
example {α : Type u} {n : ℕ} {t : Tree α} (h : braun t) :
    Tdel_hi n t ≤ Nat.log2 (size t) + 2 :=
  Tdel_hi_le_braun h

/-- (§11.4): `add_lo` is logarithmic on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    Tadd_lo t ≤ Nat.log2 (size t) + 2 :=
  Tadd_lo_le_braun h

/-- (§11.4): `merge` is logarithmic (in its first argument) on Braun trees. -/
example {α : Type u} {t₁ t₂ : Tree α} (h : braun t₁) :
    Tmerge t₁ t₂ ≤ Nat.log2 (size t₁) + 2 :=
  Tmerge_le_braun h

/-- (§11.4): `del_lo` is logarithmic on Braun trees. -/
example {α : Type u} {t : Tree α} (h : braun t) :
    Tdel_lo t ≤ Nat.log2 (size t) + 2 :=
  Tdel_lo_le_braun h

end Cslib.Algorithms.Lean.BraunTreeFlexibleArrayTests
