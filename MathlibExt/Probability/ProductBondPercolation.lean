/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure

universe u

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.ProductBondPercolation

/-- The integer line graph: nearest-neighbor graph on `ℤ`. -/
def intLine : SimpleGraph ℤ where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h <;> omega⟩

/-- The product graph `G × ℤ` is the box product of `G` with the
integer line: `G`-edges within a level together with vertical
line edges (see `SimpleGraph.boxProd_adj`). -/
def prodGraph {V : Type u} (G : SimpleGraph V) : SimpleGraph (V × ℤ) :=
  G □ intLine

/-- The open subgraph of `prodGraph G` determined by an edge-opening
pattern `ω`: keep exactly the product edges with `ω e = true`. -/
def configGraph {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool) :
    SimpleGraph (V × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ω e = true} ⊓ prodGraph G

theorem configGraph_adj {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (a b : V × ℤ) :
    (configGraph G ω).Adj a b ↔ (prodGraph G).Adj a b ∧ ω s(a, b) = true := by
  simp only [configGraph, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hω, -⟩, hG⟩
    exact ⟨hG, hω⟩
  · rintro ⟨hG, hω⟩
    exact ⟨⟨hω, (prodGraph G).ne_of_adj hG⟩, hG⟩

theorem configGraph_le_prodGraph {V : Type u} (G : SimpleGraph V)
    (ω : Sym2 (V × ℤ) → Bool) :
    configGraph G ω ≤ prodGraph G := inf_le_right

/-- The open cluster of `x` in the configuration `ω`: vertices reachable
from `x` by open edges. -/
def cluster {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (x : V × ℤ) : Set (V × ℤ) :=
  {y | (configGraph G ω).Reachable x y}

theorem self_mem_cluster {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)
    (x : V × ℤ) : x ∈ cluster G ω x := by
  change (configGraph G ω).Reachable x x
  exact SimpleGraph.Reachable.refl x

/-- Product Bernoulli(`p`) bond law on edge-opening patterns of `G × ℤ`:
the infinite product measure over all unordered pairs, each independently open
with probability `p` (`Measure.infinitePi`). -/
noncomputable def bernoulliLaw {V : Type u} (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure (Sym2 (V × ℤ) → Bool) :=
  Measure.infinitePi fun _ => ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩

/-- Almost-sure truth under the Bernoulli(`p`) bond law. -/
def AlmostSurely {V : Type u} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (Sym2 (V × ℤ) → Bool) → Prop) : Prop :=
  ∀ᵐ ω ∂(bernoulliLaw p hp0 hp1), P ω

section GeneralGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The open subgraph of a general graph `G` determined by an
edge-opening pattern `ω` on `Sym2 V`. -/
def openSubgraph (ω : Sym2 V → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ω e = true} ⊓ G

theorem openSubgraph_le (ω : Sym2 V → Bool) : openSubgraph G ω ≤ G :=
  inf_le_right

/-- The open cluster of `x` for bond percolation on `G`. -/
def gcluster (ω : Sym2 V → Bool) (x : V) : Set V :=
  {y | (openSubgraph G ω).Reachable x y}

theorem self_mem_gcluster (ω : Sym2 V → Bool) (x : V) : x ∈ gcluster G ω x := by
  change (openSubgraph G ω).Reachable x x
  exact SimpleGraph.Reachable.refl x

/-- Product Bernoulli(`p`) bond law on `G` itself. -/
noncomputable def gbernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (Sym2 V → Bool) :=
  Measure.infinitePi fun _ => ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩

end GeneralGraph

/-- The critical probability `p_c(G)` for bond percolation on a graph
`G` with countable vertex type: the infimum of densities at which an
infinite open cluster exists with positive probability, with `1`
inserted so that graphs which never percolate (empty density set) get
`p_c(G) = 1`, the standard `[0, 1]`-valued threshold convention
(`sInf ∅ = 0` in `ℝ`). Countability is part of the domain so that the
global "some infinite cluster exists" event is measurable for the
`Measure.infinitePi` product law. -/
noncomputable def criticalProb {V : Type u} [Countable V] (G : SimpleGraph V) : ℝ :=
  sInf (insert 1 {p : ℝ | ∃ hp0 : 0 ≤ p, ∃ hp1 : p ≤ 1,
    0 < gbernoulliLaw p hp0 hp1 {ω | ∃ x : V, (gcluster G ω x).Infinite}})

end MathlibExt.Probability.ProductBondPercolation
