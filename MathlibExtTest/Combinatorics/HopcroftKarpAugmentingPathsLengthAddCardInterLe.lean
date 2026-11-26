/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HopcroftKarpAugmentingPathsLengthAddCardInterLe

/-!
# Tests for augmenting after a shortest augmentation

The length inequality implies monotonicity and excludes shared edges at equal lengths.
A concrete pair of successive augmentations shares one edge.

J. E. Hopcroft and R. M. Karp, *An n^{5/2} algorithm for maximum matchings in bipartite graphs*,
SIAM Journal on Computing 2(4) (1973), 225–231, §2, Theorem 2.
-/

set_option autoImplicit false

namespace MathlibExtTest.Combinatorics.HopcroftKarpAugmentingPathsLengthAddCardInterLe

open MetaMathlibExt
open scoped symmDiff

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {u v : V} (p : G.Walk u v) (hp : IsAugmentingWalk M p)
    (hshort : ∀ (a b : V) (r : G.Walk a b), IsAugmentingWalk M r → p.length ≤ r.length)
    {a b : V} (q : G.Walk a b) (hq : IsAugmentingWalk (M ∆ p.edges.toFinset) q) :
    p.length ≤ q.length :=
  (Nat.le_add_right _ _).trans (hp.length_add_card_inter_le G M hMG hM p hshort q hq)

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {u v : V} (p : G.Walk u v) (hp : IsAugmentingWalk M p)
    (hshort : ∀ (a b : V) (r : G.Walk a b), IsAugmentingWalk M r → p.length ≤ r.length)
    {a b : V} (q : G.Walk a b) (hq : IsAugmentingWalk (M ∆ p.edges.toFinset) q)
    (hlen : p.length = q.length) : p.edges.toFinset ∩ q.edges.toFinset = ∅ := by
  have h := hp.length_add_card_inter_le G M hMG hM p hshort q hq
  apply Finset.card_eq_zero.mp
  omega

private def firstEdge : (⊤ : SimpleGraph (Fin 4)).Walk 0 1 :=
  .cons (by decide) .nil

private def overlappingWalk : (⊤ : SimpleGraph (Fin 4)).Walk 2 3 :=
  .cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 2 0)
    (.cons (by decide : (⊤ : SimpleGraph (Fin 4)).Adj 0 1) (.cons (by decide) .nil))

example : (firstEdge.edges.toFinset ∩ overlappingWalk.edges.toFinset).card = 1 := by
  decide

example : firstEdge.length +
    (firstEdge.edges.toFinset ∩ overlappingWalk.edges.toFinset).card ≤ overlappingWalk.length := by
  have hp : IsAugmentingWalk (∅ : Finset (Sym2 (Fin 4))) firstEdge :=
    ⟨by decide, by decide, by simp, by simp, by simp [firstEdge], by simp [firstEdge]⟩
  have hq : IsAugmentingWalk (∅ ∆ firstEdge.edges.toFinset) overlappingWalk := by
    simp only [IsAugmentingWalk, firstEdge, overlappingWalk]
    decide
  exact hp.length_add_card_inter_le ⊤ ∅ (by simp) (by simp) firstEdge
    (fun _ _ r hr => by simpa [firstEdge] using Nat.add_one_le_of_lt hr.2.2.2.2.2) overlappingWalk hq

end MathlibExtTest.Combinatorics.HopcroftKarpAugmentingPathsLengthAddCardInterLe
