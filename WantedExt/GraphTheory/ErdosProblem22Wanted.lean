/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/22.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
# Erdős Problem 22
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem22Wanted

/-! Source record `FC-ErdosProblem22`, ported from FormalConjectures
`ErdosProblems/22.lean` (`theorem erdos_22`, its Szemerédi/Bollobás–Erdős/
Fox–Loh–Zhao variants, and the proved empty-graph test) and checked
against erdosproblems.com/22. `CliqueFree`, `indepNum`, `edgeFinset`,
and `Real.log` are Mathlib's. The `answer(True)` wrapper is elaborated
to the direct claim. Status: resolved true (all parts proved; Fox–Loh–
Zhao [FLZ15]). -/

open Classical in
/-- The Ramsey–Turán density of `K₄` is `1/8`, with the matching upper
bound, the Bollobás–Erdős lower bound, and the Fox–Loh–Zhao quantitative
form. -/
def conjecture : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card) ∧
  (∀ (ε : ℝ), 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ (n : ℕ) in atTop,
      ∀ G : SimpleGraph (Fin n), G.CliqueFree 4 →
        (G.indepNum : ℝ) ≤ δ * n →
        (G.edgeFinset.card : ℝ) ≤ (1 / 8 + ε) * n ^ 2) ∧
  (∀ (ε δ : ℝ), 0 < ε → 0 < δ → ∀ᶠ (n : ℕ) in atTop,
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (G.indepNum : ℝ) ≤ δ * n ∧ (1 / 8 - ε) * n ^ 2 ≤ G.edgeFinset.card) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in atTop,
    ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (G.indepNum : ℝ) ≤
        C * (Real.log (Real.log n)) ^ (3 / 2 : ℝ) / (Real.log n) ^ (1 / 2 : ℝ) * n ∧
      (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card)

open Classical in
/-- The empty graph satisfies the Szemerédi upper bound. -/
theorem test_bot (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 := by
  refine ⟨SimpleGraph.cliqueFree_bot (by norm_num), ?_⟩
  rw [SimpleGraph.edgeFinset_bot]
  simp only [Finset.card_empty, Nat.cast_zero]
  positivity

/--
Resolved true: Resolved true (Fox-Loh-Zhao): the Ramsey-Turan density of K4 is 1/8, with all
variants and the proved empty-graph test. Source: Jacob Fox, Po-Shen Loh, and Yufei Zhao, The
critical window for the classical Ramsey-Turán problem, Combinatorica 35 (2015), 435–476. Moved
from `OpenConjectures/GraphTheory/ErdosProblem22`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem22Wanted
