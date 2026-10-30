/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting unrooted binary phylogenetic trees

An *unrooted binary phylogenetic tree* on a set of taxa `X` is a finite tree whose leaves (the
vertices of degree one) are labeled bijectively by `X` and whose other vertices all have degree
three. Two such trees are the same when a graph isomorphism between them preserves the leaf
labels. For `n ≥ 3` taxa there are `(2 n - 5)‼` of them (`1, 3, 15, 105` for `n = 3, 4, 5, 6`);
the rooted count `(2 n - 3)‼` is proved in `MathlibExt.Biology.Phylogenetics.TreeCount`
(rooting at the pendant edge of one taxon is the classical bijection between the two).

## References

* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, Proposition 2.1.4.
* J. Felsenstein, *Inferring Phylogenies*, Sinauer, 2004, chapter 3.
-/

@[expose] public section

open scoped Nat

namespace MathlibExt.Biology.Phylogenetics.UnrootedTreeCountWanted

/-- An **unrooted binary phylogenetic tree** on the taxa `X`: a finite tree `G` on a vertex
type `V` whose degree-one vertices are labeled bijectively by `X` (`label`) and whose other
vertices all have degree three. -/
structure UnrootedBinaryTree (X : Type) : Type 1 where
  /-- The vertex type. -/
  V : Type
  /-- The vertex type is finite. -/
  [fintype : Fintype V]
  /-- The tree. -/
  G : SimpleGraph V
  /-- Adjacency is decidable (so that degrees are defined). -/
  [decRel : DecidableRel G.Adj]
  /-- `G` is a tree. -/
  isTree : G.IsTree
  /-- The bijective labeling of the leaves by the taxa. -/
  label : X ≃ {v : V // G.degree v = 1}
  /-- Every vertex that is not a leaf has degree three. -/
  degree_eq_three : ∀ v, G.degree v ≠ 1 → G.degree v = 3

attribute [instance] UnrootedBinaryTree.fintype UnrootedBinaryTree.decRel

/-- Two unrooted binary phylogenetic trees are **isomorphic** when some graph isomorphism maps
the leaf with each label to the leaf with the same label. -/
def UnrootedBinaryTree.Iso {X : Type} (T T' : UnrootedBinaryTree X) : Prop :=
  ∃ e : T.G ≃g T'.G, ∀ x, e (T.label x) = T'.label x

/-- **The number of unrooted binary phylogenetic trees.** On `n ≥ 3` labeled taxa there are
`(2 n - 5)‼ = 1 · 3 ⋯ (2 n - 5)` unrooted binary phylogenetic trees up to label-preserving
isomorphism.

Source: Semple & Steel (2003), Proposition 2.1.4. -/
theorem_wanted nat_card_unrootedBinaryTree (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (Quot (UnrootedBinaryTree.Iso (X := Fin n))) = (2 * n - 5)‼

/-! ### Non-vacuity: the star tree on three taxa -/

/-- The star with center `3` and leaves `0, 1, 2`. -/
private def starGraph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 3

private theorem starGraph_adj (i j : Fin 4) :
    starGraph.Adj i j ↔ i ≠ j ∧ (i = 3 ∨ j = 3) := by
  rw [starGraph, SimpleGraph.fromRel_adj]

private instance : DecidableRel starGraph.Adj := fun i j =>
  decidable_of_iff _ (starGraph_adj i j).symm

private theorem starGraph_degree :
    ∀ v : Fin 4, starGraph.degree v = if v = 3 then 3 else 1 := by
  decide

private theorem starGraph_card : starGraph.edgeFinset.card = 3 := by decide

private theorem starGraph_connected : starGraph.Connected := by
  have h : ∀ v, starGraph.Reachable v 3 := by
    intro v
    by_cases hv : v = 3
    · subst hv; rfl
    · exact SimpleGraph.Adj.reachable ((starGraph_adj _ _).2 ⟨hv, Or.inr rfl⟩)
  exact ⟨fun u v => (h u).trans (h v).symm⟩

private theorem starGraph_isTree : starGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨starGraph_connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, starGraph_card]
  simp

private theorem starGraph_degree_castSucc :
    ∀ i : Fin 3, starGraph.degree i.castSucc = 1 := by
  decide

/-- The labeling of the leaves of the star. -/
private def starLabel : Fin 3 → {v : Fin 4 // starGraph.degree v = 1} :=
  fun i => ⟨i.castSucc, starGraph_degree_castSucc i⟩

private theorem starLabel_bijective : Function.Bijective starLabel := by decide

-- Non-vacuity: the star with three leaves is an unrooted binary phylogenetic tree on three taxa.
noncomputable example : UnrootedBinaryTree (Fin 3) where
  V := Fin 4
  G := starGraph
  isTree := starGraph_isTree
  label := Equiv.ofBijective _ starLabel_bijective
  degree_eq_three v hv := by
    rw [starGraph_degree] at hv ⊢
    split_ifs at hv ⊢ <;> simp_all

end MathlibExt.Biology.Phylogenetics.UnrootedTreeCountWanted
