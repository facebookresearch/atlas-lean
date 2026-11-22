/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Anti-Ramsey numbers of cycles (Erdős Problem 1105)

Erdős Problem 1105 (Erdős, Simonovits and Sós): is `AR(n, C_k) = ((k - 2) / 2 + 1 / (k - 1)) n +
O(1)`? And for paths, if `n ≥ k ≥ 5`, is `AR(n, P_k)` equal to `max((k-2 choose 2) + 1, (ℓ-1 choose
2) + (ℓ - 1)(n - ℓ + 1) + ε)`, `ℓ = ⌊(k - 1) / 2⌋`, `ε = 1` for odd `k` and `2` otherwise?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.AntiRamseyCyclesErdosProblem1105Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1105, https://www.erdosproblems.com/1105 (status
PROVED). UnsolvedMath record UM-00002492 (`EP-1105`), dataset ulamai/UnsolvedMath v1.8.0.

`AR(n, C_k)` is `MathlibExt`'s `SimpleGraph.antiRamseyNum (cycleGraph k) n`: the largest `m` such
that some labeling of the edges of `K_n` onto `Fin m` has no rainbow copy of `C_k` (Mathlib's
`SimpleGraph.cycleGraph k`). Only the cycle question is formalized: the path
formula for all `n ≥ k ≥ 5` rests on Yuan's preprint (arXiv:2102.00807), and the published result of
Simonovits and Sós covers only `n ≥ c k²`.
-/

/-- Erdős Problem 1105, first question (Erdős, Simonovits and Sós): for each fixed `k ≥ 3`,
`AR(n, C_k) = ((k - 2) / 2 + 1 / (k - 1)) n + O(1)`. -/
def antiRamseyCycleLinear : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, ∀ n : ℕ,
    |(SimpleGraph.antiRamseyNum (SimpleGraph.cycleGraph k) n : ℝ) -
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n| ≤ C

/--
Resolved true: Montellano-Ballesteros and Neumann-Lara determined `AR(n, C_k)` exactly, and their
formula gives `AR(n, C_k) = ((k - 2) / 2 + 1 / (k - 1)) n + O(1)` for each fixed `k ≥ 3`;
erdosproblems.com/1105 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#1105, https://www.erdosproblems.com/1105 (status PROVED); resolution: J. J. Montellano-Ballesteros
and V. Neumann-Lara, An anti-Ramsey theorem on cycles, Graphs Combin. (2005), 343-354, exact formula
for AR(n, C_k), giving ((k - 2)/2 + 1/(k - 1)) n + O(1) (erdosproblems.com/1105),
https://www.erdosproblems.com/1105.
-/
public theorem_wanted antiRamseyCycleLinear_holds : antiRamseyCycleLinear

end MathlibExt.GraphTheory.AntiRamseyCyclesErdosProblem1105Wanted
