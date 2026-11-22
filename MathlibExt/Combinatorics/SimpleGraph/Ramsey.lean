/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
# Classical graph Ramsey numbers
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Nat

/-!
The arbitrary-graph Ramsey API is adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean`.
-/

@[expose] public section

namespace SimpleGraph

/-- `classicalRamsey s t N` says that every graph on `N` vertices contains an
ordinary copy of `K_s`, or its complement contains an ordinary copy of `K_t`.
Thus the graph and its complement encode the two colors of a complete graph. -/
def classicalRamsey (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    IsContained (completeGraph (Fin s)) G ∨
      IsContained (completeGraph (Fin t)) Gᶜ

/-- The classical two-color graph Ramsey number `R(s, t)`, defined as the least
cardinality at which `classicalRamsey s t` holds.

The defining set is nonempty by the finite Ramsey theorem. This definition is
total independently of that fact because `sInf` on `ℕ` is total. -/
noncomputable def graphRamsey (s t : ℕ) : ℕ :=
  sInf {N : ℕ | classicalRamsey s t N}

/-- The defining characterization of `graphRamsey`. -/
theorem graphRamsey_eq_sInf (s t : ℕ) :
    graphRamsey s t = sInf {N : ℕ | classicalRamsey s t N} :=
  rfl

/-- The two-color Ramsey number for an arbitrary pair of finite graphs. This
uses a separate name so the established natural-parameter `graphRamsey` API
remains compatible with existing callers. -/
@[nolint unusedArguments]
noncomputable def graphPairRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ}

/-- The defining characterization of `graphPairRamsey`. -/
theorem graphPairRamsey_eq_sInf {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    graphPairRamsey G H =
      sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ} :=
  rfl

/-- Monotonicity of the pair-Ramsey property in the number of vertices: if
every graph on `N` vertices contains `G` or its complement contains `H`,
then so does every graph on `M ≥ N` vertices (restrict to the first `N`
vertices and push the witness copy forward along `Fin.castLE`). -/
theorem pairRamsey_mono {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    {N M : ℕ} (hNM : N ≤ M)
    (hR : ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ) :
    ∀ C : SimpleGraph (Fin M), G.IsContained C ∨ H.IsContained Cᶜ := by
  intro C
  have hC := hR (C.comap (Fin.castLE hNM))
  rcases hC with h1 | h2
  · obtain ⟨f⟩ := h1
    refine Or.inl ⟨⟨⟨fun i => Fin.castLE hNM (f.toHom i), fun {x y} hadj => ?_⟩,
      ?_⟩⟩
    · exact f.toHom.map_adj hadj
    · exact (Fin.castLE_injective hNM).comp f.injective
  · obtain ⟨f⟩ := h2
    refine Or.inr ⟨⟨⟨fun i => Fin.castLE hNM (f.toHom i), fun {x y} hadj => ?_⟩,
      ?_⟩⟩
    · have h2 := f.toHom.map_adj hadj
      rw [compl_adj] at h2 ⊢
      refine ⟨?_, h2.2⟩
      intro heq
      exact h2.1 (Fin.castLE_injective hNM heq)
    · exact (Fin.castLE_injective hNM).comp f.injective

/-- Symmetry of the pair-Ramsey number: complementing the coloring swaps the
two roles. -/
theorem graphPairRamsey_symm {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    graphPairRamsey G H = graphPairRamsey H G := by
  rw [graphPairRamsey_eq_sInf, graphPairRamsey_eq_sInf]
  congr 1
  ext n
  constructor
  · intro h C
    rcases h Cᶜ with h1 | h1
    · exact Or.inr h1
    · rw [compl_compl] at h1
      exact Or.inl h1
  · intro h C
    rcases h Cᶜ with h1 | h1
    · exact Or.inr h1
    · rw [compl_compl] at h1
      exact Or.inl h1

/-- The diagonal graph Ramsey number `R(G, G)` for an arbitrary finite graph. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphPairRamsey G G

/-- A graph `G` is Ramsey size linear if `R(G,H)` is bounded linearly by the
number of edges of every finite graph `H` without isolated vertices. -/
def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (graphPairRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

end SimpleGraph
