/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Asymptotics of the extremal number of the `4`-cycle (Erdős Problem 765)

Erdős Problem 765: give an asymptotic formula for `ex(n; C₄)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.FourCycleExtremalAsymptoticErdosProblem765Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #765, https://www.erdosproblems.com/765 (status SOLVED
(LEAN)). UnsolvedMath record UM-30007023 (`EP-765`), dataset ulamai/UnsolvedMath v1.8.0.

`ex(n; C₄)` is Mathlib's `SimpleGraph.extremalNumber n (cycleGraph 4)`, the largest number of edges
of a graph on `n` vertices with no copy of `C₄`. The asymptotic formula is the one
erdosproblems.com/765 states, `ex(n; C₄) ∼ n^{3/2} / 2`. `WantedExt` already states small values and
the projective-plane values (`FourCycleExtremalValuesWanted`), not the asymptotic. Compared with the
formal-conjectures statement `ErdosProblems/765.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 765: `ex(n; C₄) ∼ n^{3/2} / 2`, where `ex(n; C₄)` is the largest number of edges
of a graph on `n` vertices containing no `4`-cycle. -/
def fourCycleExtremalAsymptotic : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ))
    (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2) / 2)

/--
Resolved true: Reiman proved `lim sup ex(n; C₄) / n^{3/2} ≤ 1/2`, and the construction of Erdős and
Rényi and of Brown gives `ex(q² + q + 1; C₄) ≥ q (q + 1)² / 2` for prime powers `q`;
erdosproblems.com/765 states that together these give `ex(n; C₄) ∼ n^{3/2} / 2` and lists the
problem as solved. Source: T. F. Bloom, Erdős Problems, Problem #765,
https://www.erdosproblems.com/765 (status SOLVED (LEAN)); resolution: I. Reiman, Über ein Problem
von K. Zarankiewicz, Acta Math. Acad. Sci. Hungar. (1958), 269-273; W. G. Brown, On graphs that do
not contain a Thomsen graph, Canad. Math. Bull. (1966), 281-285; P. Erdős, A. Rényi and V. T. Sós,
On a problem of graph theory, Studia Sci. Math. Hungar. (1966), 215-235, erdosproblems.com/765:
Reiman's upper bound lim ex(n; C₄)/n^{3/2} ≤ 1/2 with the Erdős-Rényi and Brown construction ex(q² +
q + 1; C₄) ≥ q(q + 1)²/2 for prime powers q implies ex(n; C₄) ∼ n^{3/2}/2,
https://www.erdosproblems.com/765.
-/
public theorem_wanted fourCycleExtremalAsymptotic_holds : fourCycleExtremalAsymptotic

end MathlibExt.GraphTheory.FourCycleExtremalAsymptoticErdosProblem765Wanted
