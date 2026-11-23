/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of distinct sizes of maximal cliques (Erdős Problem 927)

Erdős Problem 927: let `g(n)` be the maximum number of different sizes of cliques that can occur in
a graph on `n` vertices. Estimate `g(n)`; in particular, is it true that `g(n) = n - log₂ n -
log_*(n) + O(1)`, where `log_*(n)` is the number of iterated logarithms such that `log ⋯ log n < 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import MathlibExt.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.MaximalCliqueSizeCountErdosProblem927Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #927, https://www.erdosproblems.com/927 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007094 (`EP-927`), dataset ulamai/UnsolvedMath v1.8.0.

Cliques are maximal complete subgraphs, as for Moon and Moser: every graph with clique number `ω`
has complete subgraphs of all sizes up to `ω`, so for complete subgraphs `g(n) = n` and the question
would be trivial. `g(n)` is the maximum over graphs on `Fin n` of the size of MathlibExt's
`SimpleGraph.maximalCliqueSizes`; `log*` iterates the natural logarithm and `log₂` is `Real.logb 2`;
the claim is `|g(n) - (n - log₂ n - log* n)| ≤ C` for all large `n`. The open-ended request to
estimate `g(n)` is not formalized. Compared with the formal-conjectures statement
`ErdosProblems/927.lean` (which uses `Nat.log 2` and `Nat.iteratedLog 2`; equivalent up to the
`O(1)`; no code imported).
-/

open Filter

/-- `g(n)`: the largest number of distinct sizes of maximal cliques of a graph on `n` vertices
(`SimpleGraph.maximalCliqueSizes`, MathlibExt). -/
noncomputable def maxCliqueSizeCount (n : ℕ) : ℕ :=
  Finset.univ.sup fun G : SimpleGraph (Fin n) => G.maximalCliqueSizes.ncard

/-- `log* x`: the number of times the natural logarithm must be iterated, starting from `x`, to
get a value below `1`. -/
noncomputable def iteratedLog (x : ℝ) : ℕ :=
  sInf {k : ℕ | Real.log^[k] x < 1}

/-- Erdős Problem 927: `g(n) = n - log₂ n - log* n + O(1)`. -/
def cliqueSizeCountAsymptotic : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    |(maxCliqueSizeCount n : ℝ) - (n - Real.logb 2 n - iteratedLog n)| ≤ C

/--
Resolved false: Spencer proved `g(n) > n - log₂ n - O(1)`, so `g(n) - (n - log₂ n - log* n)` is at
least `log* n - O(1)`, which is unbounded; erdosproblems.com/927 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #927, https://www.erdosproblems.com/927 (status
DISPROVED (LEAN)); resolution: J. H. Spencer, On cliques in graphs, Israel J. Math. (1971), 419-421,
erdosproblems.com/927: Spencer proved g(n) > n - log₂ n - O(1), disproving Erdős's conjecture (Moon
and Moser had g(n) ≤ n - ⌊log₂ n⌋), https://www.erdosproblems.com/927.
-/
public theorem_wanted cliqueSizeCountAsymptotic_refuted : ¬ cliqueSizeCountAsymptotic

end MathlibExt.GraphTheory.MaximalCliqueSizeCountErdosProblem927Wanted
