/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 57
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Circumference
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Real

@[expose] public section

open SimpleGraph

namespace MathlibExt.GraphTheory.ErdosProblem57Wanted

/-! Source record `FC-ErdosProblem57`, ported from FormalConjectures
`ErdosProblems/57.lean` (`theorem erdos_57`) and checked against
erdosproblems.com/57. `oddCycleLengths` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`); `chromaticNumber` and `Summable` are
Mathlib's. The statement is given as stated. Status: resolved true
(Erdős–Hajnal conjecture, proved by Liu and Montgomery [LiMo20]). -/

/-- Infinite chromatic number forces divergent odd-cycle reciprocal sums. -/
def conjecture : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
    ¬ Summable (fun (a : G.oddCycleLengths) ↦ 1 / (a : ℝ))

/--
Resolved true: Resolved true (Liu and Montgomery [LiMo20]), per erdosproblems.com/57. Source:
Hong Liu and Richard Montgomery, A solution to Erdős and Hajnal's odd cycle problem,
arXiv:2010.15802 (J. Amer. Math. Soc., doi:10.1090/jams/1018), https://arxiv.org/abs/2010.15802.
Moved from `OpenConjectures/GraphTheory/ErdosProblem57`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem57Wanted
