/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Ramsey-Turán problem for `K₄` (Erdős Problem 615)

Erdős Problem 615 (Erdős, Hajnal, Simonovits, Sós and Szemerédi): does there exist some constant `c
> 0` such that if `G` is a graph with `n` vertices and at least `(1/8 - c) n²` edges then `G` must
contain either a `K₄` or an independent set on at least `n / log n` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyTuranKFourErdosProblem615Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #615, https://www.erdosproblems.com/615 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006952 (`EP-615`), dataset ulamai/UnsolvedMath v1.8.0.

The claim is required only for all sufficiently large `n` (weaker than for every `n`, so its
refutation is stronger); `log` is the natural logarithm and `indepNum` is Mathlib's independence
number. Compared with the formal-conjectures statement `ErdosProblems/615.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 615 (Erdős, Hajnal, Simonovits, Sós and Szemerédi): there is `c > 0` such that
for all large `n` every graph on `n` vertices with at least `(1/8 - c) n²` edges contains a `K₄` or
an independent set of at least `n / log n` vertices. -/
def ramseyTuranKFourLogIndependence : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (1 / 8 - c) * (n : ℝ) ^ 2 ≤ G.edgeSet.ncard →
      ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum

/--
Resolved false: Fox, Loh and Zhao proved `rt(n; 4, n e^{-f(n)}) ≥ (1/8 - o(1)) n²` whenever `f(n) =
o(√(log n / log log n))`; with `f(n) = log log n` this gives, for every `c > 0` and all large `n`,
`K₄`-free graphs with at least `(1/8 - c) n²` edges and no independent set of `n / log n` vertices;
erdosproblems.com/615 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#615, https://www.erdosproblems.com/615 (status DISPROVED (LEAN)); resolution: J. Fox, P.-S. Loh and
Y. Zhao, The critical window for the classical Ramsey-Turán problem, Combinatorica (2015), 435-476,
erdosproblems.com/615: the answer is no; rt(n; 4, n e^{-f(n)}) ≥ (1/8 - o(1)) n² whenever f(n) =
o(√(log n / log log n)), https://www.erdosproblems.com/615.
-/
public theorem_wanted ramseyTuranKFourLogIndependence_refuted : ¬ ramseyTuranKFourLogIndependence

end MathlibExt.GraphTheory.RamseyTuranKFourErdosProblem615Wanted
