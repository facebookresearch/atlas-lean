/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hamiltonicity of random graphs with many edges (Erdős Problem 746)

Erdős Problem 746: is a random graph on `n` vertices with at least `(1/2 + ε) n log n` edges
Hamiltonian almost surely?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MathlibExt.GraphTheory.RandomGraphHamiltonianErdosProblem746Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #746, https://www.erdosproblems.com/746 (status
PROVED). UnsolvedMath record UM-30007008 (`EP-746`), dataset ulamai/UnsolvedMath v1.8.0.

The random graph with `M` edges is the uniform model `G(n, M)`. The statement quantifies over every
edge count `M(n)` that eventually lies between `(1/2 + ε) n log n` and `n(n - 1)/2` (the upper bound
keeps the model nonempty; only eventual values matter for the limit), with the natural logarithm.
-/

open Classical in
/-- The proportion of Hamiltonian graphs among the graphs on `Fin n` with exactly `M` edges (the
uniform model `G(n, M)`). -/
noncomputable def hamiltonianProportion (n M : ℕ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) =>
      G.edgeFinset.card = M ∧ G.IsHamiltonian).card : ℝ) /
    (Finset.univ.filter fun G : SimpleGraph (Fin n) => G.edgeFinset.card = M).card

/-- Erdős Problem 746 (Erdős–Rényi): for every `ε > 0`, the random graph on `n` vertices with
`M(n) ≥ (1/2 + ε) n log n` edges is Hamiltonian almost surely, for every edge count `M(n)` that
eventually lies between `(1/2 + ε) n log n` and `n (n - 1) / 2`. -/
def randomGraphManyEdgesHamiltonian : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ M : ℕ → ℕ,
    (∀ᶠ n : ℕ in Filter.atTop, (1 / 2 + ε) * n * Real.log n ≤ M n ∧ M n ≤ n.choose 2) →
      Filter.Tendsto (fun n => hamiltonianProportion n (M n)) Filter.atTop (nhds 1)

/--
Resolved true: Korshunov proved that `½ n log n + ½ n log log n + w(n) n` edges suffice for every
`w(n) → ∞`, and Komlós and Szemerédi found the limiting probability at `½ n log n + ½ n log log n +
c n`; `(1/2 + ε) n log n` edges exceed these thresholds. erdosproblems.com/746 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #746, https://www.erdosproblems.com/746 (status
PROVED); resolution: J. Komlós and E. Szemerédi, Limit distribution for the existence of Hamiltonian
cycles in a random graph, Discrete Math. 43 (1983), 55-63; A. D. Korshunov (1977); L. Pósa (1976),
with ½ n log n + ½ n log log n + c n edges P(Hamiltonian) → e^{-e^{-2c}} (erdosproblems.com/746),
https://doi.org/10.1016/0012-365X(83)90021-3.
-/
public theorem_wanted randomGraphManyEdgesHamiltonian_holds : randomGraphManyEdgesHamiltonian

end MathlibExt.GraphTheory.RandomGraphHamiltonianErdosProblem746Wanted
