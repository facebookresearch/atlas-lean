/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turán numbers of the graphs H_k (Erdős Problem 926)

Erdős Problem 926: let `k ≥ 4`. Is it true that `ex(n; H_k) ≪_k n^{3/2}`, where `H_k` is the graph
on vertices `x, y_1, …, y_k, z_1, …, z_{C(k, 2)}`, where `x` is adjacent to all `y_i` and each pair
of `y_i, y_j` is adjacent to a unique `z_i`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.SubdividedBookTuranErdosProblem926Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #926, https://www.erdosproblems.com/926 (status
PROVED). UnsolvedMath record UM-30007093 (`EP-926`), dataset ulamai/UnsolvedMath v1.8.0.

`H_k` has vertex type `Unit ⊕ Fin k ⊕ {(i, j) : i < j}`; `z_{ij}` is adjacent to `y_i` and `y_j`
only. `ex(n; H)` is Mathlib's `SimpleGraph.extremalNumber n H`, and `≪_k n^{3/2}` is a constant `C`
depending on `k` with `ex(n; H_k) ≤ C n^{3/2}` for all `n`. Compared with the formal-conjectures
statement `ErdosProblems/926.lean` (`erdos_926`, equivalent; no code imported).
-/

/-- The graph `H_k` on the vertices `x`, `y_1, …, y_k` and `z_{ij}` (`i < j`): `x` is adjacent to
every `y_i`, and `z_{ij}` is adjacent to exactly `y_i` and `y_j`. -/
def hGraph (k : ℕ) : SimpleGraph (Unit ⊕ Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | Sum.inl _, Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
    | _, _ => False

/-- Erdős Problem 926: for every `k ≥ 4`, `ex(n; H_k) ≪_k n^{3/2}`: some `C` (depending on `k`)
bounds the number of edges of every `H_k`-free graph on `n` vertices by `C n^{3/2}`. -/
def extremalNumberThreeHalves : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ, ∀ n : ℕ,
    (SimpleGraph.extremalNumber n (hGraph k) : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)

/--
Resolved true: Füredi proved `ex(n; H_k) ≪ (k n)^{3/2}`, which bounds `ex(n; H_k)` by `C_k n^{3/2}`;
Alon, Krivelevich and Sudakov improved this to `ex(n; H_k) ≪ k n^{3/2}`; erdosproblems.com/926 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #926,
https://www.erdosproblems.com/926 (status PROVED); resolution: Z. Füredi, On a Turán type problem of
Erdős, Combinatorica (1991), 75-79; N. Alon, M. Krivelevich and B. Sudakov, Turán numbers of
bipartite graphs and related Ramsey-type questions, Combin. Probab. Comput. (2003), 477-494,
erdosproblems.com/926: Füredi proved ex(n; H_k) ≪ (kn)^{3/2}, improved to ≪ k n^{3/2} by Alon,
Krivelevich and Sudakov, https://www.erdosproblems.com/926.
-/
public theorem_wanted extremalNumberThreeHalves_holds : extremalNumberThreeHalves

end MathlibExt.GraphTheory.SubdividedBookTuranErdosProblem926Wanted
