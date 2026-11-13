/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Induced subgraphs of Ramsey graphs with many distinct degrees (Erdős Problem 637)

Erdős Problem 637 (Erdős, Faudree and Sós): if `G` is a graph on `n` vertices which contains no
complete graph or independent set on `≫ log n` vertices then `G` contains an induced subgraph on `≫
n` vertices which contains `≫ n^{1/2}` distinct degrees.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyGraphDistinctDegreesErdosProblem637Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #637, https://www.erdosproblems.com/637 (status
PROVED). UnsolvedMath record UM-30006962 (`EP-637`), dataset ulamai/UnsolvedMath v1.8.0.

The hypothesis 'no complete graph or independent set on `≫ log n` vertices' is `ω(G) < C log n` and
`α(G) < C log n` for a constant `C > 0` (natural logarithm); the conclusion's constant may depend on
`C`, and the statement is for all large `n`, as in the resolving paper. Degrees are taken in the
induced subgraph `G[U]`.
-/

open Classical in
/-- The number of distinct degrees in the subgraph of `G` induced by `U`. -/
noncomputable def inducedDistinctDegrees {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) : ℕ :=
  (U.image fun v => (U.filter fun w => G.Adj v w).card).card

/-- Erdős Problem 637 (Erdős, Faudree and Sós): for every `C > 0` there is `c > 0` such that for
large `n` every graph on `n` vertices with no clique and no independent set of `C log n` vertices
has an induced subgraph on at least `c n` vertices with at least `c √n` distinct degrees. -/
def ramseyGraphInducedManyDegrees : Prop :=
  ∀ C > (0 : ℝ), ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (G.cliqueNum : ℝ) < C * Real.log n → (G.indepNum : ℝ) < C * Real.log n →
      ∃ U : Finset (Fin n), c * n ≤ U.card ∧ c * Real.sqrt n ≤ inducedDistinctDegrees G U

/--
Resolved true: Bukh and Sudakov proved that every graph on `n` vertices with no clique or
independent set of size `C log n` has an induced subgraph on `α n` vertices in which `β √n` vertices
have distinct degrees, with `α, β > 0` depending only on `C`; erdosproblems.com/637 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #637,
https://www.erdosproblems.com/637 (status PROVED); resolution: B. Bukh and B. Sudakov, Induced
subgraphs of Ramsey graphs with many distinct degrees, J. Combin. Theory Ser. B 97 (2007), 612-619,
abstract: every graph on n vertices with hom(G) < C log n contains an induced subgraph of order αn
in which βn^{1/2} vertices have different degrees, α and β depending only on C;
erdosproblems.com/637: proved by Bukh and Sudakov,
https://people.math.ethz.ch/~sudakovb/distinct-degrees.pdf.
-/
public theorem_wanted ramseyGraphInducedManyDegrees_holds : ramseyGraphInducedManyDegrees

end MathlibExt.GraphTheory.RamseyGraphDistinctDegreesErdosProblem637Wanted
