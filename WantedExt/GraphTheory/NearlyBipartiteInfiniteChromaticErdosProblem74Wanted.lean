/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nearly bipartite graphs of infinite chromatic number (Erdős Problem 74)

Erdős Problem 74 (Erdős, Hajnal and Szemerédi): let `f(n) → ∞` (possibly very slowly). Is there a
graph of infinite chromatic number such that every finite subgraph on `n` vertices can be made
bipartite by deleting at most `f(n)` edges?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.NearlyBipartiteInfiniteChromaticErdosProblem74Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #74, https://www.erdosproblems.com/74 (status DISPROVED
(LEAN)). UnsolvedMath record UM-00001912 (`EP-74`), dataset ulamai/UnsolvedMath v1.8.0.

`f : ℕ → ℕ` (edge counts are integers; real `f` could be negative at small `n`, which would make the
question trivially false). It suffices to consider induced subgraphs on finite vertex sets `S`; "can
be made bipartite by deleting at most `m` edges" is: some `2`-colouring leaves at most `m`
monochromatic edges (ordered pairs counted, hence `2 f(|S|)`). Infinite chromatic number is
`chromaticNumber = ⊤`. The disproof is machine-generated (GPT-6 Astra); the problem page marks the
problem disproved. Compared with the formal-conjectures statement `ErdosProblems/74.lean`
(equivalent; no code imported).
-/

open Classical in
/-- The number of edges of `G` with both ends in `S` that are monochromatic under the
`2`-colouring `c`; `S` can be made bipartite by deleting `m` edges iff some `c` makes this at most
`m`. Ordered pairs are counted, so each edge contributes `2`. -/
noncomputable def monochromaticPairs {V : Type} (G : SimpleGraph V) (S : Finset V) (c : V → Bool) :
    ℕ :=
  (S.offDiag.filter fun p => G.Adj p.1 p.2 ∧ c p.1 = c p.2).card

/-- Erdős Problem 74 (Erdős, Hajnal and Szemerédi): for every `f : ℕ → ℕ` with `f(n) → ∞` there is
a graph of infinite chromatic number in which every finite set of `n` vertices induces a subgraph
that can be made bipartite by deleting at most `f(n)` edges. -/
def nearlyBipartiteInfiniteChromatic : Prop :=
  ∀ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop →
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ S : Finset V, ∃ c : V → Bool, monochromaticPairs G S c ≤ 2 * f S.card

/--
Resolved false: erdosproblems.com/74 records a disproof (by GPT-6 Astra, formalized in Lean) for
`f(n) ≍ log n / log log n`: a graph in which every finite subgraph on `n` vertices can be made
bipartite by deleting at most `f(n)` edges has chromatic number at most `3`; the page lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #74,
https://www.erdosproblems.com/74 (status DISPROVED (LEAN)); resolution: erdosproblems.com/74 and its
proof exposition (disproof by GPT-6 Astra, formalized in Lean), erdosproblems.com/74: 'A negative
answer for f(n) ≍ log n / log log n was provided by GPT-6 Astra; see the proof expositions. (In fact
such a graph must have chromatic number ≤ 3.)'; status DISPROVED (LEAN),
https://www.erdosproblems.com/74.
-/
public theorem_wanted nearlyBipartiteInfiniteChromatic_refuted : ¬ nearlyBipartiteInfiniteChromatic

end MathlibExt.GraphTheory.NearlyBipartiteInfiniteChromaticErdosProblem74Wanted
