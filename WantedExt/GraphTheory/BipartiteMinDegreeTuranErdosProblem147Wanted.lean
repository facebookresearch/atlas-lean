/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turán exponents of bipartite graphs of given minimum degree (Erdős Problem 147)

Erdős Problem 147: if `H` is bipartite with minimum degree `r`, is there `ε = ε(H) > 0` such that
`ex(n; H) ≫ n^{2 - 1/(r-1) + ε}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.BipartiteMinDegreeTuranErdosProblem147Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #147, https://www.erdosproblems.com/147 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006741 (`EP-147`), dataset ulamai/UnsolvedMath v1.8.0.

`H` is a finite nonempty bipartite graph with `r ≥ 2` (for `r = 1` the exponent is undefined);
`ex(n; H)` is Mathlib's `SimpleGraph.extremalNumber`, and `≫` is `=O` in the reverse direction.
Compared with the formal-conjectures statement `ErdosProblems/147.lean` (equivalent to `erdos_147`;
no code imported).
-/

open Filter Asymptotics

/-- Erdős Problem 147: for every finite bipartite graph `H` with minimum degree `r ≥ 2` there is
`ε > 0` with `ex(n; H) ≫ n^{2 - 1/(r - 1) + ε}`. -/
def bipartiteMinDegreeTuranExponent : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (H : SimpleGraph V) [DecidableRel H.Adj],
    H.IsBipartite → 2 ≤ H.minDegree → ∃ ε : ℝ, 0 < ε ∧
      (fun n : ℕ => (n : ℝ) ^ (2 - 1 / ((H.minDegree : ℝ) - 1) + ε)) =O[atTop]
        fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ)

/--
Resolved false: Janzer constructed, for every `ε > 0`, a `3`-regular bipartite `H` with `ex(n; H) ≪
n^{4/3 + ε}`, below `n^{3/2}`, and for even `r ≥ 4` an `r`-regular bipartite `H` with `ex(n; H) ≪
n^{2 - 2/r + ε}`, below `n^{2 - 1/(r-1)}`; erdosproblems.com/147 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #147, https://www.erdosproblems.com/147 (status
DISPROVED (LEAN)); resolution: O. Janzer, Disproof of a conjecture of Erdős and Simonovits on the
Turán number of graphs with minimum degree 3, Int. Math. Res. Not. IMRN (2023), 8478-8494; O.
Janzer, Rainbow Turán number of even cycles, repeated patterns and blow-ups of cycles, Israel J.
Math. (2023), 813-840, erdosproblems.com/147: for every ε > 0 a 3-regular bipartite H with ex(n; H)
≪ n^{4/3 + ε}; for even r ≥ 4, r-regular bipartite H with ex(n; H) ≪ n^{2 - 2/r + ε}.
-/
public theorem_wanted bipartiteMinDegreeTuranExponent_refuted : ¬ bipartiteMinDegreeTuranExponent

end MathlibExt.GraphTheory.BipartiteMinDegreeTuranErdosProblem147Wanted
