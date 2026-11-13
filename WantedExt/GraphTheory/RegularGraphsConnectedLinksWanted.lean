/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Source record `OWR-16931-008`
# Regular graphs with regular connected neighbourhoods (Friedgut)

E. Friedgut, Regular graphs with regular connected neighborhoods, Oberwolfach Rep. 16 (2019),
Report 19/2019 "Combinatorics, Probability and Computing", DOI 10.4171/OWR/2019/19.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GraphTheory.RegularGraphsConnectedLinksWanted

/-- The link of a finite vertex set `S`: its common neighbourhood `{w | ∀ s ∈ S, s ~ w}`. -/
def link {V : Type*} (G : SimpleGraph V) (S : Finset V) : Set V :=
  {w | ∀ s ∈ S, G.Adj s w}

/-- The graph induced by `G` on `W` is `(d₁, …, d_r)`-regular: every `v ∈ W` has exactly `d₁`
neighbours in `W`, and `N(v) ∩ W` induces a `(d₂, …, d_r)`-regular graph. -/
def IsTupleRegularOn {V : Type*} (G : SimpleGraph V) : Set V → List ℕ → Prop
  | _, [] => True
  | W, d :: ds => ∀ v ∈ W, (G.neighborSet v ∩ W).ncard = d ∧
      IsTupleRegularOn G (G.neighborSet v ∩ W) ds

/-- `G` has connected links of all orders up to `5`: `G` itself (the link of the empty
clique) and the graphs induced on the links of every vertex, edge, triangle, `K₄` and `K₅`
are connected. -/
def HasConnectedLinks {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card ≤ 5 → G.IsClique (S : Set V) → (G.induce (link G S)).Connected

/-- Friedgut's question: for some `(a, b, c, d, e)` there are `(a, b, c, d, e)`-regular
graphs with connected links of all orders and arbitrarily many vertices. -/
def conjecture : Prop :=
  ∃ a b c d e : ℕ, ∀ N : ℕ, ∃ n ≥ N, ∃ G : SimpleGraph (Fin n),
    IsTupleRegularOn G Set.univ [a, b, c, d, e] ∧ HasConnectedLinks G

/--
Resolved true: Resolved affirmatively by Friedgut and Iluz (Hyper-regular graphs and high
dimensional expanders, Israel J. Math. 256 (2023) 233-267, arXiv:2010.03829, Theorem 1.1 with
Definitions 1.7 and 1.13): for every n there are infinite families of (d0, ..., d_{n-1})-regular
graphs whose clique complexes are λ-expanders with λ < 1. With n = 7 the graph and the links of
all cliques of size at most 5 are connected, which answers Friedgut's question (Oberwolfach
Report 19/2019, p. 1132). Source: E. Friedgut, Y. Iluz, Hyper-regular graphs and high
dimensional expanders, Israel J. Math. 256 (2023) 233-267, arXiv:2010.03829,
https://doi.org/10.1007/s11856-023-2511-y. Moved from
`OpenConjectures/GraphTheory/RegularGraphsConnectedLinks`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.RegularGraphsConnectedLinksWanted
