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
public import Mathlib.Data.Real.Basic
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
/-- **Ramsey–Turán problem for $K_4$ (Erdős Problem 22).** For a graph $G$ write $\alpha(G)$ for
its independence number and $e(G)$ for its number of edges, and call $G$ $K_4$-free if it has no
four pairwise adjacent vertices. The statement is the conjunction of the following four
assertions.

(i) For every real $\varepsilon > 0$ and all sufficiently large $n$, there is a $K_4$-free graph
$G$ on $n$ vertices with $\alpha(G) \le \varepsilon n$ and $e(G) \ge n^2/8$.

(ii) (Szemerédi's upper bound.) For every real $\varepsilon > 0$ there is a real $\delta > 0$ such
that, for all sufficiently large $n$, every $K_4$-free graph $G$ on $n$ vertices with
$\alpha(G) \le \delta n$ satisfies $e(G) \le (1/8 + \varepsilon) n^2$.

(iii) (Bollobás–Erdős lower bound.) For all real $\varepsilon > 0$ and $\delta > 0$ and all
sufficiently large $n$, there is a $K_4$-free graph $G$ on $n$ vertices with
$\alpha(G) \le \delta n$ and $e(G) \ge (1/8 - \varepsilon) n^2$.

(iv) (Fox–Loh–Zhao quantitative form.) There is a real $C > 0$ such that, for all sufficiently
large $n$, there is a $K_4$-free graph $G$ on $n$ vertices with $e(G) \ge n^2/8$ and
$\alpha(G) \le C n (\log \log n)^{3/2} / (\log n)^{1/2}$. -/
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
/-- **The empty graph meets the Ramsey–Turán edge bound for $K_4$.** For every natural number $n$
and every real $\varepsilon > 0$, the empty graph on $n$ vertices has no four pairwise adjacent
vertices, and its number of edges (namely $0$) is at most $(1/8 + \varepsilon) n^2$. -/
theorem test_bot (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 := by
  refine ⟨SimpleGraph.cliqueFree_bot (by norm_num), ?_⟩
  rw [SimpleGraph.edgeFinset_bot]
  simp only [Finset.card_empty, Nat.cast_zero]
  positivity

/-- **Resolution of Erdős Problem 22 (Fox–Loh–Zhao).** For a graph $G$ write $\alpha(G)$ for its
independence number and $e(G)$ for its number of edges, and call $G$ $K_4$-free if it has no four
pairwise adjacent vertices. All four of the following assertions hold.

(i) For every real $\varepsilon > 0$ and all sufficiently large $n$, there is a $K_4$-free graph
$G$ on $n$ vertices with $\alpha(G) \le \varepsilon n$ and $e(G) \ge n^2/8$.

(ii) (Szemerédi's upper bound.) For every real $\varepsilon > 0$ there is a real $\delta > 0$ such
that, for all sufficiently large $n$, every $K_4$-free graph $G$ on $n$ vertices with
$\alpha(G) \le \delta n$ satisfies $e(G) \le (1/8 + \varepsilon) n^2$.

(iii) (Bollobás–Erdős lower bound.) For all real $\varepsilon > 0$ and $\delta > 0$ and all
sufficiently large $n$, there is a $K_4$-free graph $G$ on $n$ vertices with
$\alpha(G) \le \delta n$ and $e(G) \ge (1/8 - \varepsilon) n^2$.

(iv) (Fox–Loh–Zhao quantitative form.) There is a real $C > 0$ such that, for all sufficiently
large $n$, there is a $K_4$-free graph $G$ on $n$ vertices with $e(G) \ge n^2/8$ and
$\alpha(G) \le C n (\log \log n)^{3/2} / (\log n)^{1/2}$.

Source: Jacob Fox, Po-Shen Loh, and Yufei Zhao, The
critical window for the classical Ramsey-Turán problem, Combinatorica 35 (2015), 435–476. Moved
from `OpenConjectures/GraphTheory/ErdosProblem22`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem22Wanted
