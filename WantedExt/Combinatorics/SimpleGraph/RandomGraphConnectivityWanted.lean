/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.RandomGraphNoIsolated
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The connectivity threshold of `G(n, p)`

At `p = (log n + c)/n` the number of isolated vertices of `G(n, p)` is asymptotically Poisson with
mean `e^{-c}`, and with high probability `G(n, p)` has no component of order between `2` and
`n/2`, so `G(n, p)` is connected exactly when it has no isolated vertex and
`P(G(n, p) is connected) → e^{-e^{-c}}` (P. Erdős and A. Rényi, "On random graphs I", *Publ.
Math. Debrecen* 6 (1959); A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge
University Press 2016, Theorem 3.1 (ii) for the Poisson limit, and Theorem 4.1 with its proof,
which states the `G(n, p)` form used here).
The limiting probability of having no isolated vertex is proved in
`MathlibExt.Combinatorics.SimpleGraph.RandomGraphNoIsolated`.

`G(n, p)` is `pairGraph ω` for `ω` drawn from `randomSubsetLaw` with constant probability `p`.
The hypothesis `pₙ = (log n + c)/n` for all large `n` is satisfiable for every real `c`
(`RandomGraphIsolatedVertices.exists_prob_eventually_eq`), and implies `n pₙ - log n → c`
(`RandomGraphIsolatedVertices.tendsto_mul_sub_log_of_eventually_eq`).
-/

@[expose] public section

open MeasureTheory Filter Topology unitInterval
  MathlibExt.Probability.Combinatorics.RandomSubset
  MathlibExt.Combinatorics.RamseyErdosLowerBound

namespace MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted

/-- **Connectivity threshold of `G(n, p)` (Erdős–Rényi).** If `pₙ = (log n + c)/n` for all large
`n`, then `P(G(n, pₙ) is connected) → e^{-e^{-c}}` (P. Erdős and A. Rényi, 1959; Frieze and
Karoński, *Introduction to Random Graphs*, 2016, Theorem 4.1, whose proof establishes this
`G(n, p)` form before transferring it to `G(n, m)` with `m = n(log n + c)/2`). -/
theorem_wanted tendsto_measureReal_connected (c : ℝ) (p : ℕ → I)
    (hp : ∀ᶠ n : ℕ in atTop, (p n : ℝ) = (Real.log n + c) / n) :
    Tendsto (fun n : ℕ => (randomSubsetLaw (fun _ : Pair n => p n)).real
      {ω | (pairGraph ω).Connected}) atTop (𝓝 (Real.exp (-Real.exp (-c))))

end MathlibExt.Combinatorics.SimpleGraph.RandomGraphConnectivityWanted
