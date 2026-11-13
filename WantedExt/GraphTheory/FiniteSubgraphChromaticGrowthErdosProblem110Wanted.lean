/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small finite subgraphs of large chromatic number (Erdős Problem 110)

Erdős Problem 110 (Erdős, Hajnal and Szemerédi): is there some `F(n)` such that every graph with
chromatic number `ℵ₁` has, for all large `n`, a subgraph with chromatic number `n` on at most `F(n)`
vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.FiniteSubgraphChromaticGrowthErdosProblem110Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #110, https://www.erdosproblems.com/110 (status
DISPROVED). UnsolvedMath record UM-30006726 (`EP-110`), dataset ulamai/UnsolvedMath v1.8.0.

Chromatic number `ℵ₁` is `MathlibExt`'s `SimpleGraph.chromaticCardinal G = ℵ₁` (the least
cardinality of a color type of a proper coloring); the finite subgraphs use Mathlib's
`chromaticNumber`. Subgraphs are taken induced (see the target); vertex types are in `Type`.
-/

/-- Erdős Problem 110 (Erdős, Hajnal and Szemerédi): there is `F : ℕ → ℕ` such that every graph with
chromatic number `ℵ₁` has, for all large `n`, a subgraph with chromatic number `n` on at most `F(n)`
vertices (taken induced; any subgraph with chromatic number `n` on a vertex set `W` gives an induced
one on a subset of `W`). -/
def smallFiniteSubgraphsOfEveryChromaticNumber : Prop :=
  ∃ F : ℕ → ℕ, ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = Cardinal.aleph 1 →
    ∀ᶠ n : ℕ in Filter.atTop, ∃ W : Finset V, W.card ≤ F n ∧
      (G.induce (W : Set V)).chromaticNumber = n

/--
Resolved false: Lambie-Hanson proved in ZFC that for every `f : ℕ → ℕ` there is a graph with
chromatic number `ℵ₁` all of whose subgraphs with chromatic number `k ≥ 3` have at least `f(k)`
vertices; with `f = F + 1` this defeats any `F` (Komjáth and Shelah had shown the negative answer
consistent). erdosproblems.com/110 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #110, https://www.erdosproblems.com/110 (status DISPROVED); resolution: C.
Lambie-Hanson, On the growth rate of chromatic numbers of finite subgraphs, Adv. Math. (2020),
107176, Main Theorem: for every f : ℕ → ℕ there is a graph G with |G| = 2^ℵ₀ and χ(G) = ℵ₁ such that
every subgraph of chromatic number k ≥ 3 has at least f(k) vertices (erdosproblems.com/110),
https://www.erdosproblems.com/110.
-/
public theorem_wanted smallFiniteSubgraphsOfEveryChromaticNumber_refuted :
    ¬ smallFiniteSubgraphsOfEveryChromaticNumber

end MathlibExt.GraphTheory.FiniteSubgraphChromaticGrowthErdosProblem110Wanted
