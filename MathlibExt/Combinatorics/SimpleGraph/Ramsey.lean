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

/-- **The Ramsey property for cliques.** For natural numbers $s$, $t$ and $N$, the classical
Ramsey property for $(s, t)$ holds at $N$ when every simple graph $G$ on $N$ vertices contains the
complete graph $K_s$ as a subgraph, or its complement $\overline{G}$ contains $K_t$ as a subgraph.

Thus the graph and its complement encode the two colors of a complete graph. -/
def classicalRamsey (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    IsContained (completeGraph (Fin s)) G ∨
      IsContained (completeGraph (Fin t)) Gᶜ

/-- **Classical Ramsey numbers.** For natural numbers $s$ and $t$, the Ramsey number $R(s, t)$ is
the least $N$ such that every simple graph on $N$ vertices contains the complete graph $K_s$ as a
subgraph or has a complement containing $K_t$ as a subgraph, and $0$ if there is no such $N$.

Such an $N$ always exists by the finite Ramsey theorem. -/
noncomputable def graphRamsey (s t : ℕ) : ℕ :=
  sInf {N : ℕ | classicalRamsey s t N}

/-- **Classical Ramsey numbers as an infimum.** For all natural numbers $s$ and $t$, the Ramsey
number $R(s, t)$ equals the infimum in $\mathbb{N}$ (where the empty set has infimum $0$) of the
set of $N$ such that every simple graph on $N$ vertices contains the complete graph $K_s$ as a
subgraph or has a complement containing $K_t$ as a subgraph. -/
theorem graphRamsey_eq_sInf (s t : ℕ) :
    graphRamsey s t = sInf {N : ℕ | classicalRamsey s t N} :=
  rfl

/-- **Ramsey number of a pair of graphs.** For finite simple graphs $G$ and $H$, the Ramsey number
$R(G, H)$ is the least $n$ such that every simple graph $C$ on $n$ vertices contains a copy of $G$
as a subgraph or has a complement containing a copy of $H$ as a subgraph, and $0$ if there is no
such $n$. -/
@[nolint unusedArguments]
noncomputable def graphPairRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ}

/-- **The pair Ramsey number as an infimum.** For finite simple graphs $G$ and $H$, the Ramsey
number $R(G, H)$ equals the infimum in $\mathbb{N}$ (where the empty set has infimum $0$) of the
set of $n$ such that every simple graph $C$ on $n$ vertices contains a copy of $G$ as a subgraph
or has a complement containing a copy of $H$ as a subgraph. -/
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

/-- **Diagonal Ramsey number of a graph.** For a finite simple graph $G$, the diagonal Ramsey
number of $G$ is $R(G, G)$: the least $n$ such that for every simple graph $C$ on $n$ vertices,
$C$ or its complement contains a copy of $G$ as a subgraph, and $0$ if there is no such $n$. -/
noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphPairRamsey G G

/-- **Ramsey size linear graphs.** Let $G$ be a finite simple graph. For a finite simple graph
$H$, write $R(G, H)$ for the least $m$ such that every simple graph on $m$ vertices contains a
copy of $G$ or has a complement containing a copy of $H$ ($0$ if there is no such $m$), and write
$e(H)$ for the number of edges of $H$. Then $G$ is Ramsey size linear if there is a real constant
$c > 0$ such that for every $n$ and every simple graph $H$ on $n$ vertices with no isolated
vertices, $R(G, H) \le c \cdot e(H)$. -/
def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (graphPairRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

end SimpleGraph
