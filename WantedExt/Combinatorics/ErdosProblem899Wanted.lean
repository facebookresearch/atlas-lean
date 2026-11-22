/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 899
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

open Filter
open scoped Pointwise Topology

namespace MathlibExt.Combinatorics.ErdosProblem899Wanted

/-! Source record `FC-ErdosProblem899`, ported from FormalConjectures
`ErdosProblems/899.lean` and checked against erdosproblems.com/899.
The upstream `answer(True)` is dropped. Status: resolved true (Ruzsa
[Ru78]); the registry links a proof-bearing external Lean development. -/

/-- Sparse sets have large difference-to-initial-segment ratios. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ), A.Infinite →
    Tendsto (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 0) →
    Filter.atTop.limsup (fun N => (((A - A : Set ℕ) ∩ Set.Icc 1 N).ncard : EReal) /
      ((A ∩ Set.Icc 1 N).ncard : EReal)) = ⊤

/--
Resolved true: Resolved true by Ruzsa; a proof is available in an external Lean development.
Source: I. Z. Ruzsa, On the cardinality of A+A and A-A (1978), 933–938,
https://mathscinet.ams.org/mathscinet-getitem?mr=519317. Moved from
`OpenConjectures/Combinatorics/ErdosProblem899`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem899Wanted
