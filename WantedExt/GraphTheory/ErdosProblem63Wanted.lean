/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 63
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Circumference
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.ENat.Basic

@[expose] public section

open SimpleGraph

namespace MathlibExt.GraphTheory.ErdosProblem63Wanted

/-! Source record `FC-ErdosProblem63`, ported from FormalConjectures
`ErdosProblems/63.lean` (`theorem erdos_63`) and checked against
erdosproblems.com/63. `cycleLengths` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`); `chromaticNumber` is Mathlib's. The
`answer(True)` wrapper is elaborated to a direct proposition. Status:
resolved true (Mihók–Erdős conjecture, solved via Liu–Montgomery [LiMo20]). -/

/-- **Statement of Erdős Problem 63.** The proposition that every simple graph $G$ with infinite
chromatic number has cycles of length $2^n$ for infinitely many $n$: for every natural number
$N$ there is some $n \ge N$ such that $G$ contains a cycle of length $2^n$. -/
def conjecture : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
    ∀ N : ℕ, ∃ n ≥ N, 2 ^ n ∈ G.cycleLengths

/--
**Erdős Problem 63 (Liu–Montgomery).** Every simple graph $G$ with infinite chromatic number has
cycles of length $2^n$ for infinitely many $n$: for every natural number $N$ there is some
$n \ge N$ such that $G$ contains a cycle of length $2^n$.

Source: Liu–Montgomery [LiMo20], per erdosproblems.com/63, https://www.erdosproblems.com/63.
Moved from `OpenConjectures/GraphTheory/ErdosProblem63`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem63Wanted
