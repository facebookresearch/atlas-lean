/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Induced subgraphs of Ramsey graphs with every edge count (Erdős Problem 88)

Erdős Problem 88 (Erdős and McKay): for any `ε > 0` there is `δ > 0` such that if `G` is a graph on
`n` vertices with no independent set or clique of size `≥ ε log n` then `G` contains an induced
subgraph with `m` edges for all `m ≤ δ n²`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyGraphInducedEdgesErdosProblem88Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #88, https://www.erdosproblems.com/88 (status PROVED).
UnsolvedMath record UM-30006717 (`EP-88`), dataset ulamai/UnsolvedMath v1.8.0.

No clique or independent set of size `≥ ε log n` is: every clique and every independent set has
fewer than `ε log n` vertices (natural logarithm). Erdős's original condition `e(G) ≫ n²` follows
from this one (Erdős and Szemerédi), as the page notes, and is omitted. Compared with the
formal-conjectures statement `ErdosProblems/88.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 88 (Erdős and McKay): for every `ε > 0` there is `δ > 0` such that every graph on
`n` vertices with no clique or independent set of size `≥ ε log n` has, for every `m ≤ δ n²`, an
induced subgraph with exactly `m` edges. -/
def ramseyGraphInducedEdgeCounts : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ s : Finset (Fin n), G.IsClique (s : Set (Fin n)) → (s.card : ℝ) < ε * Real.log n) →
    (∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) < ε * Real.log n) →
      ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
        ∃ S : Finset (Fin n), (G.induce (S : Set (Fin n))).edgeSet.ncard = m

/--
Resolved true: Kwan, Sah, Sauermann and Sawhney proved the Erdős-McKay conjecture: a graph on `n`
vertices with no clique or independent set of size `C log n` has induced subgraphs with every number
of edges up to `(1 - η) e(G)` for large `n`, and `e(G) ≫ n²`; erdosproblems.com/88 lists the problem
as proved. Source: T. F. Bloom, Erdős Problems, Problem #88, https://www.erdosproblems.com/88
(status PROVED); resolution: M. Kwan, A. Sah, L. Sauermann and M. Sawhney, Anticoncentration in
Ramsey graphs and a proof of the Erdős-McKay conjecture, arXiv:2208.02874 (2022), Theorem 1.1: for
fixed C, η > 0 and n large, every C-Ramsey graph G on n vertices (no clique or independent set of
size C log₂ n) has, for every integer 0 ≤ x ≤ (1 - η) e(G), a vertex subset inducing exactly x
edges; footnote 2 deduces the Erdős-McKay conjecture for all n (δ_C small for small n, and e(G) ≥
ε_C n² by Erdős and Szemerédi), https://arxiv.org/abs/2208.02874.
-/
public theorem_wanted ramseyGraphInducedEdgeCounts_holds : ramseyGraphInducedEdgeCounts

end MathlibExt.GraphTheory.RamseyGraphInducedEdgesErdosProblem88Wanted
