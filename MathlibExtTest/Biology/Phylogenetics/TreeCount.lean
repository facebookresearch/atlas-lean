/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.TreeCount

/-!
# Tests for the count of rooted binary phylogenetic trees

A concrete tree on three taxa (non-vacuity of `RootedBinaryTree`), a swap identifying two
drawings, a non-example (a drawing with a repeated taxon is not a drawing on `X`), the boundary
cases `n = 0` (no tree), `n = 1` and `n = 2` (one tree), and the counts `3`, `15`, `105` for
`n = 3, 4, 5`.
-/

@[expose] public section

open scoped Nat

namespace MathlibExtTest.Biology.Phylogenetics.TreeCount

open MathlibExt.Biology.Phylogenetics.TreeCount PlaneTree

/-- The drawing `((0, 1), 2)` on the taxa `{0, 1, 2}`. -/
def t₀ : PlaneTree.On ({0, 1, 2} : Finset ℕ) :=
  ⟨node (node (leaf 0) (leaf 1)) (leaf 2), by decide⟩

/-- The drawing `(2, (1, 0))`, obtained from `t₀` by two swaps. -/
def t₁ : PlaneTree.On ({0, 1, 2} : Finset ℕ) :=
  ⟨node (leaf 2) (node (leaf 1) (leaf 0)), by decide⟩

-- Non-vacuity: a rooted binary phylogenetic tree on three taxa.
example : RootedBinaryTree ({0, 1, 2} : Finset ℕ) := ⟦t₀⟧

-- Swapping children does not change the phylogenetic tree.
example : (⟦t₀⟧ : RootedBinaryTree ({0, 1, 2} : Finset ℕ)) = ⟦t₁⟧ :=
  Quotient.sound <| .trans _ _ _ (.rel _ _ (.root _ _))
    (.rel _ _ (.right _ (.root _ _)))

-- A drawing that repeats a taxon is not a drawing on `{0, 1, 2}`.
example : (node (node (leaf 0) (leaf 0)) (leaf 2) : PlaneTree ℕ).leaves ≠
    ({0, 1, 2} : Finset ℕ).val := by decide

-- No taxa: no tree.
example : Nat.card (RootedBinaryTree (∅ : Finset ℕ)) = 0 := Nat.card_of_isEmpty

-- One and two taxa: one tree.
example : Nat.card (RootedBinaryTree ({7} : Finset ℕ)) = 1 := by
  rw [nat_card_rootedBinaryTree _ (Finset.singleton_nonempty 7)]; decide

example : Nat.card (RootedBinaryTree ({0, 1} : Finset ℕ)) = 1 := by
  rw [nat_card_rootedBinaryTree _ (by decide)]; decide

-- Three, four and five taxa: `3‼ = 3`, `5‼ = 15`, `7‼ = 105` trees.
example : Nat.card (RootedBinaryTree ({0, 1, 2} : Finset ℕ)) = 3 := by
  rw [nat_card_rootedBinaryTree _ (by decide)]; decide

example : Nat.card (RootedBinaryTree (Finset.range 4)) = 15 := by
  rw [nat_card_rootedBinaryTree _ (by decide)]; decide

example : Nat.card (RootedBinaryTree (Finset.univ : Finset (Fin 5))) = 105 := by
  rw [nat_card_rootedBinaryTree _ Finset.univ_nonempty]; decide

-- In particular the type of trees is finite.
example : Finite (RootedBinaryTree (Finset.range 4)) :=
  Nat.finite_of_card_ne_zero (by rw [nat_card_rootedBinaryTree _ (by decide)]; decide)

end MathlibExtTest.Biology.Phylogenetics.TreeCount
