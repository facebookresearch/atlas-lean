/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.RamseyErdosLowerBound
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The chromatic number of dense random graphs

Bollobás (1988) determined the chromatic number of `G(n, p)` for constant `p` asymptotically:
`χ(G(n, p)) ~ n / (2 log_b n)` with high probability, where `b = 1/(1 - p)`; for `p = 1/2` this is
`n / (2 log₂ n)`. The lower bound follows from the independence number `α(G(n, p)) ~ 2 log_b n`;
the upper bound needs that every set of `n/(log_b n)²` vertices contains an independent set of
size close to `2 log_b n`, which Bollobás proved with a martingale concentration inequality for
the maximum number of edge-disjoint independent sets of that size.

References: B. Bollobás, "The chromatic number of random graphs", *Combinatorica* 8 (1988)
49–55; A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press 2016,
Theorem 7.7 and the remarks after its proof.

`G(n, p)` is `pairGraph ω` for `ω` drawn from `randomSubsetLaw` with constant probability `p`.
-/

@[expose] public section

open MeasureTheory Filter Topology unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumberWanted

/-- **Chromatic number of dense random graphs (Bollobás).** For a constant `0 < p < 1` and
`b = 1/(1 - p)`, with high probability `χ(G(n, p)) = (1 + o(1)) n / (2 log_b n)`: for every
`ε > 0`, the probability that `χ(G(n, p))` lies within a factor `1 ± ε` of `n / (2 log_b n)` tends
to `1` (B. Bollobás, *Combinatorica* 8 (1988); Frieze and Karoński, *Introduction to Random
Graphs*, 2016, Theorem 7.7). At `p = 1/2`, `b = 2` and the value is `n / (2 log₂ n)`. -/
theorem_wanted tendsto_measureReal_chromaticNumber_near (p : I) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p)).real
      {ω | |((pairGraph ω).chromaticNumber.toNat : ℝ) /
          (n / (2 * Real.logb (1 / (1 - (p : ℝ))) n)) - 1| ≤ ε}) atTop (𝓝 1)

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphChromaticNumberWanted
