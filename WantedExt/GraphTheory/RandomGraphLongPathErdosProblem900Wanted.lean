/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Long paths in sparse random graphs (Erdős Problem 900)

Erdős Problem 900: there is a function `f : (1/2, ∞) → ℝ` such that `f(c) → 0` as `c → 1/2` and
`f(c) → 1` as `c → ∞`, and every random graph with `n` vertices and `c n` edges has (with high
probability) a path of length at least `f(c) n`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphLongPathErdosProblem900Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #900, https://www.erdosproblems.com/900 (status
PROVED). UnsolvedMath record UM-30007077 (`EP-900`), dataset ulamai/UnsolvedMath v1.8.0.

The random graph is the uniform model `G(n, ⌊c n⌋)` on `Fin n`; with high probability is probability
tending to `1`. `f(c) > 0` for every `c > 1/2` is required: without it `f ≤ 0` near `1/2` would make
the statement empty there. A path of length `L` has `L` edges. formal-conjectures has no statement
of this problem.
-/

open Classical in
/-- The proportion of the graphs on `Fin n` with exactly `m` edges (the uniform model `G(n, m)`)
that contain a path of length at least `x`. -/
noncomputable def longPathProportion (n m : ℕ) (x : ℝ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m ∧
      ∃ (u v : Fin n) (p : G.Walk u v), p.IsPath ∧ x ≤ p.length).card : ℝ) /
    (Finset.univ.filter fun G : SimpleGraph (Fin n) => G.edgeFinset.card = m).card

/-- Erdős Problem 900: there is `f` with `f(c) > 0` for `c > 1/2`, `f(c) → 0` as `c → 1/2⁺` and
`f(c) → 1` as `c → ∞`, such that for every `c > 1/2` the random graph with `n` vertices and
`⌊c n⌋` edges has a path of length at least `f(c) n` with probability tending to `1`. -/
def randomGraphLinearPath : Prop :=
  ∃ f : ℝ → ℝ, (∀ c, 1 / 2 < c → 0 < f c) ∧
    Filter.Tendsto f (nhdsWithin (1 / 2) (Set.Ioi (1 / 2))) (nhds 0) ∧
    Filter.Tendsto f Filter.atTop (nhds 1) ∧
    ∀ c : ℝ, 1 / 2 < c →
      Filter.Tendsto (fun n : ℕ => longPathProportion n ⌊c * n⌋₊ (f c * n)) Filter.atTop (nhds 1)

/--
Resolved true: Ajtai, Komlós and Szemerédi proved that a random graph with `(1 + ε) n / 2` edges has
a path of length `c n` with probability tending to `1`, settling Erdős's conjecture (Szemerédi had
believed the longest path is `o(n)`), and, as Frieze records, they and Fernandez de la Vega showed
that the attainable proportion tends to `1` as the edge density grows; erdosproblems.com/900 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #900,
https://www.erdosproblems.com/900 (status PROVED); resolution: M. Ajtai, J. Komlós and E. Szemerédi,
The longest path in a random graph, Combinatorica 1 (1981), 1-12; A. M. Frieze, On large matchings
and cycles in sparse random graphs, Discrete Math. 59 (1986), 243-256, AKS abstract: a random graph
with (1 + ε) n/2 edges contains a path of length cn, settling a conjecture of Erdős; Frieze, Section
1: 'Ajtai, Komlós and Szemerédi and Fernandez de la Vega showed that β(c) → 1 as c → ∞', β(c) being
the supremum of the β such that G(n, c/n) almost surely has a cycle on at least βn vertices, and
Frieze's Theorem 1.2 gives β(c) = 1 - (1 + ε(c)) c e^{-c}, https://doi.org/10.1007/BF02579172.
-/
public theorem_wanted randomGraphLinearPath_holds : randomGraphLinearPath

end MathlibExt.GraphTheory.RandomGraphLongPathErdosProblem900Wanted
