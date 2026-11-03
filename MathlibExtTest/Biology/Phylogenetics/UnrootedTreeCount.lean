/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.UnrootedTreeCount

/-!
# Tests for the count of unrooted binary phylogenetic trees

The star tree on three taxa (non-vacuity of `UnrootedBinaryTree`), a binary hierarchy and a
non-example (a polytomy), the boundary cases of the hierarchy count, the boundary `n = 2` of the
unrooted count, and the counts `1, 3, 15, 105` for `n = 3, 4, 5, 6`.
-/

@[expose] public section

open scoped Nat

namespace MathlibExtTest.Biology.Phylogenetics.UnrootedTreeCount

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount

/-! ### Non-vacuity: the star tree on three taxa -/

/-- The star with center `3` and leaves `0, 1, 2`. -/
def starGraph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 3

theorem starGraph_adj (i j : Fin 4) :
    starGraph.Adj i j ↔ i ≠ j ∧ (i = 3 ∨ j = 3) := by
  rw [starGraph, SimpleGraph.fromRel_adj]

instance : DecidableRel starGraph.Adj := fun i j =>
  decidable_of_iff _ (starGraph_adj i j).symm

theorem starGraph_degree :
    ∀ v : Fin 4, starGraph.degree v = if v = 3 then 3 else 1 := by
  decide

theorem starGraph_card : starGraph.edgeFinset.card = 3 := by decide

theorem starGraph_connected : starGraph.Connected := by
  have h : ∀ v, starGraph.Reachable v 3 := by
    intro v
    by_cases hv : v = 3
    · subst hv; rfl
    · exact SimpleGraph.Adj.reachable ((starGraph_adj _ _).2 ⟨hv, Or.inr rfl⟩)
  exact ⟨fun u v => (h u).trans (h v).symm⟩

theorem starGraph_isTree : starGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨starGraph_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, starGraph_card]
  simp

theorem starGraph_degree_castSucc :
    ∀ i : Fin 3, starGraph.degree i.castSucc = 1 := by
  decide

/-- The labeling of the leaves of the star. -/
def starLabel : Fin 3 → {v : Fin 4 // starGraph.degree v = 1} :=
  fun i => ⟨i.castSucc, starGraph_degree_castSucc i⟩

theorem starLabel_bijective : Function.Bijective starLabel := by decide

/-- Non-vacuity: the star with three leaves is an unrooted binary phylogenetic tree on three
taxa. -/
noncomputable def star : UnrootedBinaryTree (Fin 3) where
  V := Fin 4
  G := starGraph
  isTree := starGraph_isTree
  label := Equiv.ofBijective _ starLabel_bijective
  degree_eq_three v hv := by
    rw [starGraph_degree] at hv ⊢
    split_ifs at hv ⊢ <;> simp_all

-- Its clusters seen from the leaf `0` form a binary hierarchy on `{1, 2}`.
example : IsBinaryHierarchy (Finset.univ.erase 0) (clusterSet star 0) :=
  isBinaryHierarchy_clusterSet star 0

-- Every unrooted binary phylogenetic tree on three taxa is isomorphic to the star.
example (T : UnrootedBinaryTree (Fin 3)) :
    Quot.mk _ T = Quot.mk UnrootedBinaryTree.Iso star := by
  have h := nat_card_unrootedBinaryTree 3 le_rfl
  have : Subsingleton (Quot (UnrootedBinaryTree.Iso (X := Fin 3))) :=
    (Nat.card_eq_one_iff_unique.mp (by rw [h]; decide)).1
  exact Subsingleton.elim _ _

/-! ### Binary hierarchies -/

-- The clusters `{0, 1, 2}, {0, 1}, {0}, {1}, {2}` of the rooted tree `((0, 1), 2)`.
example : IsBinaryHierarchy ({0, 1, 2} : Finset ℕ) {{0, 1, 2}, {0, 1}, {0}, {1}, {2}} := by
  unfold IsBinaryHierarchy; decide

-- Non-example: the star `{0, 1, 2}, {0}, {1}, {2}` (a polytomy) is not binary.
example : ¬ IsBinaryHierarchy ({0, 1, 2} : Finset ℕ) {{0, 1, 2}, {0}, {1}, {2}} := by
  unfold IsBinaryHierarchy; decide

-- Non-example: overlapping sets are not nested or disjoint.
example : ¬ IsBinaryHierarchy ({0, 1, 2} : Finset ℕ)
    {{0, 1, 2}, {0, 1}, {1, 2}, {0}, {1}, {2}} := by
  unfold IsBinaryHierarchy; decide

-- One element: one hierarchy; three elements: three.
example : Nat.card {H : Finset (Finset ℕ) // IsBinaryHierarchy {7} H} = 1 := by
  rw [nat_card_binaryHierarchy _ (Finset.singleton_nonempty 7)]; decide

example : Nat.card {H : Finset (Finset ℕ) // IsBinaryHierarchy {0, 1, 2} H} = 3 := by
  rw [nat_card_binaryHierarchy _ (by decide)]; decide

/-! ### The counts -/

-- Two taxa: one tree (a single edge); the formula gives `(2 · 2 - 5)‼ = 0‼ = 1`.
example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 2))) = 1 := by
  rw [nat_card_unrootedBinaryTree_of_two_le 2 le_rfl]; decide

-- Three to six taxa: `1‼ = 1`, `3‼ = 3`, `5‼ = 15`, `7‼ = 105` trees.
example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 3))) = 1 := by
  rw [nat_card_unrootedBinaryTree 3 le_rfl]; decide

example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 4))) = 3 := by
  rw [nat_card_unrootedBinaryTree 4 (by decide)]; decide

example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 5))) = 15 := by
  rw [nat_card_unrootedBinaryTree 5 (by decide)]; decide

example : Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin 6))) = 105 := by
  rw [nat_card_unrootedBinaryTree 6 (by decide)]; decide

#print axioms nat_card_unrootedBinaryTree
#print axioms nat_card_binaryHierarchy

/-- In the complete graph on `Fin 3` the vertex `1` has a parent one step closer to `0`. -/
example : ∃ p, (⊤ : SimpleGraph (Fin 3)).Adj 1 p ∧
    (⊤ : SimpleGraph (Fin 3)).dist 0 p + 1 = (⊤ : SimpleGraph (Fin 3)).dist 0 1 :=
  SimpleGraph.exists_parent SimpleGraph.connected_top (by decide)

end MathlibExtTest.Biology.Phylogenetics.UnrootedTreeCount
