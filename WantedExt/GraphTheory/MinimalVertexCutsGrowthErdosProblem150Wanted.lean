/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Growth rate of the number of minimal vertex cuts (Erdős Problem 150)

Erdős Problem 150: a minimal cut of a graph is a minimal set of vertices whose removal disconnects
the graph. Let `c(n)` be the maximum number of minimal cuts of a graph on `n` vertices. Does
`c(n)^{1/n} → α` for some `α < 2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.MinimalVertexCutsGrowthErdosProblem150Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #150, https://www.erdosproblems.com/150 (status PROVED
(LEAN)). UnsolvedMath record UM-30006742 (`EP-150`), dataset ulamai/UnsolvedMath v1.8.0.

A minimal cut is an inclusion-minimal set `T` with `G - T` not connected (an empty graph or a single
vertex counts as connected, so a disconnected graph has the single minimal cut `∅`). `c(n)` is a
maximum over the finitely many graphs on `Fin n`. The further question whether `c(3m + 2) = 3^m` is
not stated. Compared with the formal-conjectures statement `ErdosProblems/150.lean` (equivalent to
`erdos_150`; no code imported).
-/

open Filter

/-- `T` is a minimal cut of `G`: removing `T` disconnects `G`, and removing any proper subset of
`T` does not. -/
def IsMinimalCut {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ¬ (G.induce Tᶜ).Preconnected ∧ ∀ S ⊂ T, (G.induce Sᶜ).Preconnected

/-- `c(n)`: the maximum number of minimal cuts of a graph on `n` vertices. -/
noncomputable def maxMinimalCuts (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), {T : Set (Fin n) | IsMinimalCut G T}.ncard = k}

/-- Erdős Problem 150: `c(n)^{1/n} → α` for some `α < 2`. -/
def minimalCutsExponentialRateBelowTwo : Prop :=
  ∃ α : ℝ, α < 2 ∧ Tendsto (fun n : ℕ => (maxMinimalCuts n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds α)

/--
Resolved true: the limit `α = lim c(n)^{1/n}` exists by a simple argument given by Bradač, and `α <
2`: Fomin, Kratsch, Todinca and Villanger proved `α ≤ 1.7087` and Fomin and Villanger `α ≤ (1 +
√5)/2` (bounds on minimal separators, which include the minimal cuts); erdosproblems.com/150 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #150,
https://www.erdosproblems.com/150 (status PROVED (LEAN)); resolution: F. V. Fomin and Y. Villanger,
Treewidth computation and extremal combinatorics, Combinatorica 32 (2012), 289-308; F. V. Fomin, D.
Kratsch, I. Todinca and Y. Villanger, Exact algorithms for treewidth and minimum fill-in, SIAM J.
Comput. 38 (2008), 1058-1079; D. Bradač, On a question of Erdős and Nešetřil about minimal cuts in a
graph, arXiv:2409.02974 (2024), erdosproblems.com/150: the limit exists (Bradač), α ≤ 1.7087
(Fomin-Kratsch-Todinca-Villanger), α ≤ (1 + √5)/2 (Fomin-Villanger), α ≥ 1.4457 (Gaspers-Mackenzie),
https://arxiv.org/abs/2409.02974.
-/
public theorem_wanted minimalCutsExponentialRateBelowTwo_holds : minimalCutsExponentialRateBelowTwo

end MathlibExt.GraphTheory.MinimalVertexCutsGrowthErdosProblem150Wanted
