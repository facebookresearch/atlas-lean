/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 800
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem800Wanted

/-! Source record `FC-ErdosProblem800`, ported from FormalConjectures
`ErdosProblems/800.lean` and checked against erdosproblems.com/800.
The statement reuses MathlibExt's arbitrary-graph Ramsey API; FC's unused edge-colouring
helper is not ported. The upstream `answer(True)` is dropped. Status:
resolved true (Alon [Al94]). -/

/-- **Erdős Problem 800 on linear Ramsey numbers.** The proposition asserts that there is a real
number $C > 0$ such that for every natural number $n$ and every simple graph $G$ on $n$ vertices
in which no two adjacent vertices both have degree at least $3$, the diagonal Ramsey number
$R(G, G)$ is at most $Cn$. -/
def conjecture : Prop :=
  ∃ C > (0 : ℝ), ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (∀ u v, G.Adj u v → ¬(3 ≤ G.degree u ∧ 3 ≤ G.degree v)) →
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ C * n

/--
**Alon's theorem on linear Ramsey numbers.** There is a real number $C > 0$ such that for every
natural number $n$ and every simple graph $G$ on $n$ vertices in which no two adjacent vertices
both have degree at least $3$, the diagonal Ramsey number $R(G, G)$ is at most $Cn$.

This answers Erdős Problem 800 affirmatively.

Source: Noga Alon, Subdivided graphs have linear
Ramsey numbers, Journal of Graph Theory 18 (1994), 343–347,
https://doi.org/10.1002/jgt.3190180406. Moved from
`OpenConjectures/Combinatorics/ErdosProblem800`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem800Wanted
