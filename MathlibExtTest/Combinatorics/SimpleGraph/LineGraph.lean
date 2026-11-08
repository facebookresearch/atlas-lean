/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

open SimpleGraph

namespace MathlibExtTest.Combinatorics.SimpleGraph.LineGraph

open MetaMathlibExt

-- Combinatorics 428: Is line graph

-- Sanity check: The line graph of the bipartite graph $K_{1,3}$ is the complete graph $K_3$

/-- Decidability of the `K_{1,3}` adjacency relation. -/

instance : DecidableRel (completeBipartiteGraph (Fin 1) (Fin 3)).Adj :=
  fun a b => decidable_of_iff (a.isLeft ∧ b.isRight ∨ a.isRight ∧ b.isLeft) Iff.rfl

/-- Every (unordered) pair with an endpoint in each side contains `inl 0` on the
    left, unless it is a same-side pair, which is never an edge of `K_{1,3}`. -/

private theorem k13_center_mem_aux (t : Sym2 (Fin 1 ⊕ Fin 3))
    (h : t ∈ (completeBipartiteGraph (Fin 1) (Fin 3)).edgeSet) :
    (Sum.inl 0 : Fin 1 ⊕ Fin 3) ∈ t := by
  revert h
  refine Sym2.ind (fun a b => ?_) t
  intro hmem
  rw [mem_edgeSet] at hmem
  match a, b with
  | .inl _, .inl _ => simp at hmem
  | .inl x, .inr y =>
    rw [Sym2.mem_iff]
    exact Or.inl (congrArg Sum.inl (Subsingleton.elim x 0)).symm
  | .inr y, .inl x =>
    rw [Sym2.mem_iff]
    exact Or.inr (congrArg Sum.inl (Subsingleton.elim x 0)).symm
  | .inr _, .inr _ => simp at hmem

-- The line graph of the bipartite graph $K_{1,3}$ is isomorphic to the complete graph $K_3$

example : Nonempty ((completeBipartiteGraph (Fin 1) (Fin 3)).lineGraph ≃g
    completeGraph (Fin 3)) := by
  -- The line graph is complete: any two distinct edges share the center `inl 0`.
  have hcompl : ∀ e₁ e₂ : (completeBipartiteGraph (Fin 1) (Fin 3)).edgeSet,
      e₁ ≠ e₂ →
        (completeBipartiteGraph (Fin 1) (Fin 3)).lineGraph.Adj e₁ e₂ := by
    intro e₁ e₂ hne
    rw [lineGraph_adj_iff_exists]
    exact ⟨hne, Sum.inl 0, k13_center_mem_aux e₁.val e₁.property,
      k13_center_mem_aux e₂.val e₂.property⟩
  -- ... and it has three vertices.
  have hcard : Fintype.card (completeBipartiteGraph (Fin 1) (Fin 3)).edgeSet =
      Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    decide
  -- Any bijection between complete graphs is an isomorphism.
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro e₁ e₂
  constructor
  · intro h
    exact hcompl e₁ e₂ (fun he => h (congrArg _ he))
  · intro h
    have hne : e₁ ≠ e₂ := (lineGraph_adj_iff_exists.mp h).1
    change e e₁ ≠ e e₂
    exact fun he => hne (e.injective he)

end MathlibExtTest.Combinatorics.SimpleGraph.LineGraph

end
