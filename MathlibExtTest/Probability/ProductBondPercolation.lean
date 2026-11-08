/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProductBondPercolation

universe u

open MathlibExt.Probability.ProductBondPercolation

namespace MathlibExtTest.Probability.ProductBondPercolation

variable {V : Type u} (G : SimpleGraph V) (ω : Sym2 (V × ℤ) → Bool)

/-- The integer line has the expected nearest-neighbor adjacency. -/
example : intLine.Adj 0 1 := Or.inl rfl

/-- The product graph is definitionally the box product. -/
example : prodGraph G = G □ intLine := rfl

/-- Open edges are product edges (adjacency containment). -/
example : configGraph G ω ≤ prodGraph G := configGraph_le_prodGraph G ω

/-- Adjacency in the open subgraph is symmetric. -/
example (a b : V × ℤ) (h : (configGraph G ω).Adj a b) :
    (configGraph G ω).Adj b a := h.symm

/-- A vertex lies in its own open cluster. -/
example (x : V × ℤ) : x ∈ cluster G ω x := self_mem_cluster G ω x

/-- Adjacency characterisation: open product edges. -/
example (a b : V × ℤ) :
    (configGraph G ω).Adj a b ↔ (prodGraph G).Adj a b ∧ ω s(a, b) = true :=
  configGraph_adj G ω a b

variable (η : Sym2 V → Bool)

/-- The open subgraph of `G` is contained in `G`. -/
example : openSubgraph G η ≤ G := openSubgraph_le G η

/-- A vertex lies in its own open `G`-cluster. -/
example (x : V) : x ∈ gcluster G η x := self_mem_gcluster G η x

end MathlibExtTest.Probability.ProductBondPercolation
