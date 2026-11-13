/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 753
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.ListColoring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Real SimpleGraph

namespace MathlibExt.GraphTheory.ErdosProblem753Wanted

/-! Source record `FC-ErdosProblem753`, ported from FormalConjectures
`ErdosProblems/753.lean` (`theorem erdos_753` and its `alon` variant) and
checked against erdosproblems.com/753. `SimpleGraph.IsListColorable` is
MathlibExt's; the list chromatic number is its `sInf`. Status: resolved false
(Alon [Al92]): Alon's `(n log n)^{1/2}` upper bound disproves the
`n^{1/2+c}` lower bound. -/

/-- The list chromatic number: least list-colorable `k`. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | G.IsListColorable k}

/-- An `n^{1/2+c}` lower bound holds (disproved). -/
def lowerBoundClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ ((1 : ℝ) / 2 + c) <
      (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ)

/-- Its disproof (companion). -/
def disprovedLowerBound : Prop := ¬ lowerBoundClaim

/-- Alon's `(n log n)^{1/2}` upper bound (established). -/
def alonUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ G : SimpleGraph (Fin n),
    (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ) ≤
      C * ((n : ℝ) * log (n : ℝ)) ^ ((1 : ℝ) / 2)

/--
Resolved false: Answered negatively per erdosproblems.com/753 (DISPROVED (LEAN)): Alon [Al92]
proved that for every n some n-vertex graph G has χ_L(G) + χ_L(G^c) ≪ (n log n)^(1/2), so no c >
0 gives the n^(1/2+c) lower bound. The registered lowerBoundClaim is refuted; the companion
target alonUpperBound records Alon's bound, which holds. This target is refuted: Alon's graphs
([Al92], recorded on erdosproblems.com/753) have χ_L(G) + χ_L(G^c) << (n log n)^{1/2}, which is
below n^{1/2+c} for every c > 0 once n is large, so no c > 0 works. Source: Alon [Al92], per
erdosproblems.com/753, https://www.erdosproblems.com/753. Moved from
`OpenConjectures/GraphTheory/ErdosProblem753`.
-/
public theorem_wanted lowerBoundClaim_refuted : ¬ lowerBoundClaim

/--
Resolved false: Answered negatively per erdosproblems.com/753 (DISPROVED (LEAN)): Alon [Al92]
proved that for every n some n-vertex graph G has χ_L(G) + χ_L(G^c) ≪ (n log n)^(1/2), so no c >
0 gives the n^(1/2+c) lower bound. The registered lowerBoundClaim is refuted; the companion
target alonUpperBound records Alon's bound, which holds. This target holds: Alon's theorem as
recorded on erdosproblems.com/753 ([Al92]): for every n there is an n-vertex graph with χ_L(G) +
χ_L(G^c) at most an absolute constant times (n log n)^{1/2}. Source: Alon [Al92], per
erdosproblems.com/753, https://www.erdosproblems.com/753. Moved from
`OpenConjectures/GraphTheory/ErdosProblem753`.
-/
public theorem_wanted alonUpperBound_holds : alonUpperBound

end MathlibExt.GraphTheory.ErdosProblem753Wanted
