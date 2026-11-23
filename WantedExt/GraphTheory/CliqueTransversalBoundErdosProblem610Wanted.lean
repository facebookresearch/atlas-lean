/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The clique transversal number (Erdős Problem 610)

Erdős Problem 610 (Erdős, Gallai and Tuza): for a graph `G` let `τ(G)` denote the minimal number of
vertices that include at least one from each maximal clique of `G` (aside from isolated vertices).
Is it true that if `G` has `n` vertices then `τ(G) ≤ n - ω(n) √n` for some `ω(n) → ∞`, or even `τ(G)
≤ n - c √(n log n)` for some absolute constant `c > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.CliqueTransversalBoundErdosProblem610Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #610, https://www.erdosproblems.com/610 (status PROVED
(LEAN)). UnsolvedMath record UM-00002210 (`EP-610`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal cliques are `Maximal G.IsClique`; those with a single vertex (the isolated vertices) are
excluded by `Set.Nontrivial`. Graphs are on `Fin n` and `log` is the natural logarithm. The two
questions are separate targets (the second implies the first); the open-ended 'estimate `τ(G)`' is
not formalized.
-/

/-- `T` is a clique transversal of `G`: it meets every maximal clique of `G` with at least two
vertices (the maximal cliques of size one, the isolated vertices, are not counted). -/
def IsCliqueTransversal {V : Type*} (G : SimpleGraph V) (T : Set V) : Prop :=
  ∀ s : Set V, Maximal G.IsClique s → s.Nontrivial → (s ∩ T).Nonempty

/-- The clique transversal number `τ(G)`: the least size of a clique transversal (the whole vertex
set is one). -/
noncomputable def cliqueTransversalNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T : Finset (Fin n), T.card = k ∧ IsCliqueTransversal G T}

/-- Erdős Problem 610, first question: there is `ω(n) → ∞` with `τ(G) ≤ n - ω(n) √n` for every
graph `G` on `n` vertices. -/
def cliqueTransversalWeakBound : Prop :=
  ∃ ω : ℕ → ℝ, Filter.Tendsto ω Filter.atTop Filter.atTop ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (cliqueTransversalNumber G : ℝ) ≤ n - ω n * Real.sqrt n

/-- Erdős Problem 610, second question: there is an absolute constant `c > 0` with
`τ(G) ≤ n - c √(n log n)` for every graph `G` on `n` vertices. -/
def cliqueTransversalStrongBound : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (cliqueTransversalNumber G : ℝ) ≤ n - c * Real.sqrt (n * Real.log n)

/--
Resolved true: the bound `τ(G) ≤ n - c √(n log n)` of the second question, which follows from the
clique colouring theorem of Joret, Micek, Reed and Smid, gives this with `ω(n) = c √(log n)`;
erdosproblems.com/610 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#610, https://www.erdosproblems.com/610 (status PROVED (LEAN)); resolution: G. Joret, P. Micek, B.
Reed and M. Smid, Tight bounds on the clique chromatic number, Electron. J. Combin. (2021), Paper
No. 3.51, erdosproblems.com/610: every n-vertex graph has a vertex colouring with k ≪ (n / log
n)^{1/2} colours in which every maximal clique other than an isolated vertex has two colours; the
union of all colour classes but the largest gives τ(G) ≤ n - c √(n log n),
https://www.erdosproblems.com/610.
-/
public theorem_wanted cliqueTransversalWeakBound_holds : cliqueTransversalWeakBound

/--
Resolved true: Joret, Micek, Reed and Smid proved that every graph on `n` vertices has a vertex
colouring with `k ≪ (n / log n)^{1/2}` colours in which no maximal clique with at least two vertices
is monochromatic; all colour classes but the largest form a clique transversal, so `τ(G) ≤ n - n/k ≤
n - c √(n log n)` (for small `n`, `τ(G) ≤ n - 1` and a smaller `c` suffice). erdosproblems.com/610
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #610,
https://www.erdosproblems.com/610 (status PROVED (LEAN)); resolution: G. Joret, P. Micek, B. Reed
and M. Smid, Tight bounds on the clique chromatic number, Electron. J. Combin. (2021), Paper No.
3.51, erdosproblems.com/610: every n-vertex graph has a vertex colouring with k ≪ (n / log n)^{1/2}
colours in which every maximal clique other than an isolated vertex has two colours; the union of
all colour classes but the largest gives τ(G) ≤ n - c √(n log n), https://www.erdosproblems.com/610.
-/
public theorem_wanted cliqueTransversalStrongBound_holds : cliqueTransversalStrongBound

end MathlibExt.GraphTheory.CliqueTransversalBoundErdosProblem610Wanted
