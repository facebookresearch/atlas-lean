/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 426
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.SubgraphIsomorphism
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Filter SimpleGraph

namespace MathlibExt.GraphTheory.ErdosProblem426Wanted

/-! Source record `FC-ErdosProblem426`, ported from FormalConjectures
`ErdosProblems/426.lean` (`theorem erdos_426`) and checked against
erdosproblems.com/426. `IsUniqueSubgraph` and `uniqueSubgraphCount` are
MathlibExt's (ported from FC's `FormalConjecturesForMathlib`); the FC
`isUniqueSubgraph_bot_bot` sanity check is omitted. Status: resolved
false (Bradač and Christoph [BrCh24]: `f(n) = o(2^C(n,2)/n!)`). The
historical positive proposition is preserved as `conjecture`; its
disproof is the unregistered companion `disprovedForm`. -/

/-- Some constant `c > 0` works for arbitrarily large `n`. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ (n : ℕ) in atTop, ∃ H : SimpleGraph (Fin n),
      c * ((2 : ℝ) ^ n.choose 2 / n.factorial) ≤ (uniqueSubgraphCount H : ℝ)

/-- No constant `c > 0` works (companion recording the disproof). -/
def disprovedForm : Prop := ¬ conjecture

/--
Resolved false: Disproved by Bradač and Christoph [BrCh24], per erdosproblems.com/426. Source:
Bradač and Christoph [BrCh24] (f(n) = o(2^C(n,2)/n!)), per erdosproblems.com/426,
https://www.erdosproblems.com/426. Moved from `OpenConjectures/GraphTheory/ErdosProblem426`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.ErdosProblem426Wanted
