/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular induced subgraphs of Ramsey graphs (Erdős Problem 1031)

Erdős Problem 1031 (Erdős, Fajtlowicz and Staton): if `G` is a graph on `n` vertices with no trivial
(empty or complete) induced subgraph on `≥ 10 log n` vertices, must `G` contain an induced
non-trivial regular subgraph on `≫ log n` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyGraphRegularInducedErdosProblem1031Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1031, https://www.erdosproblems.com/1031 (status
PROVED). UnsolvedMath record UM-30007136 (`EP-1031`), dataset ulamai/UnsolvedMath v1.8.0.

`log` is the natural logarithm (another base only rescales the constants). The statement is for all
large `n`: for small `n` every graph satisfies the hypothesis while graphs on at most `3` vertices
have no non-trivial regular induced subgraph. Regular means every vertex of the induced subgraph has
the same number of neighbours in it.
-/

/-- Erdős Problem 1031: there is `c > 0` such that, for all large `n`, every graph on `n` vertices
with no clique and no independent set of size at least `10 log n` has an induced subgraph on at
least `c log n` vertices that is regular and neither complete nor empty. -/
def ramseyGraphLargeRegularInduced : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (∀ s : Finset (Fin n), (G.IsClique (s : Set (Fin n)) ∨ G.IsIndepSet (s : Set (Fin n))) →
      (s.card : ℝ) < 10 * Real.log n) →
    ∃ s : Finset (Fin n), c * Real.log n ≤ s.card ∧
      (∃ d : ℕ, ∀ v ∈ s, (G.neighborSet v ∩ (s : Set (Fin n))).ncard = d) ∧
      ¬ G.IsClique (s : Set (Fin n)) ∧ ¬ G.IsIndepSet (s : Set (Fin n))

/--
Resolved true: Prömel and Rödl proved that such a graph contains every graph on `O(log n)` vertices
as an induced subgraph, in particular an induced cycle of length `≫ log n`, which is `2`-regular and
neither empty nor complete; erdosproblems.com/1031 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #1031, https://www.erdosproblems.com/1031 (status PROVED); resolution: H. J.
Prömel and V. Rödl, Non-Ramsey graphs are c log n-universal, J. Combin. Theory Ser. A (1999),
379-384, if G has no trivial subgraph on ≥ c log n vertices then G contains every graph on O_c(log
n) vertices as an induced subgraph (erdosproblems.com/1031), https://www.erdosproblems.com/1031.
-/
public theorem_wanted ramseyGraphLargeRegularInduced_holds : ramseyGraphLargeRegularInduced

end MathlibExt.GraphTheory.RamseyGraphRegularInducedErdosProblem1031Wanted
