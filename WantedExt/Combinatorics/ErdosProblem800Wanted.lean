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
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem800Wanted

/-! Source record `FC-ErdosProblem800`, ported from FormalConjectures
`ErdosProblems/800.lean` and checked against erdosproblems.com/800.
The statement reuses MathlibExt's arbitrary-graph Ramsey API; FC's unused edge-colouring
helper is not ported. The upstream `answer(True)` is dropped. Status:
resolved true (Alon [Al94]). -/

/-- Ramsey numbers of graphs with no adjacent high-degree vertices are
linear. -/
def conjecture : Prop :=
  ∃ C > (0 : ℝ), ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (∀ u v, G.Adj u v → ¬(3 ≤ G.degree u ∧ 3 ≤ G.degree v)) →
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ C * n

/--
Resolved true: Resolved true (Alon [Al94]). Source: Noga Alon, Subdivided graphs have linear
Ramsey numbers, Journal of Graph Theory 18 (1994), 343–347,
https://doi.org/10.1002/jgt.3190180406. Moved from
`OpenConjectures/Combinatorics/ErdosProblem800`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem800Wanted
