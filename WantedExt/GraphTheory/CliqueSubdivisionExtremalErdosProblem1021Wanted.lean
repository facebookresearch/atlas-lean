/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turán numbers of `1`-subdivisions of cliques (Erdős Problem 1021)

Erdős Problem 1021 (Erdős and Simonovits): is it true that for every `k ≥ 3` there is `c_k > 0` with
`ex(n, G_k) ≪ n^{3/2 - c_k}`, where `G_k` is the bipartite graph between `{y₁, …, y_k}` and `{z₁, …,
z_{(k choose 2)}}`, each `z_j` joined to a unique pair of `y_i`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

@[expose] public section

namespace MathlibExt.GraphTheory.CliqueSubdivisionExtremalErdosProblem1021Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1021, https://www.erdosproblems.com/1021 (status
PROVED). UnsolvedMath record UM-00002442 (`EP-1021`), dataset ulamai/UnsolvedMath v1.8.0.

`G_k` is the `1`-subdivision of `K_k`, with the two-element subsets of `Fin k` as the vertices
`z_j`; `ex(n, G_k)` is Mathlib's `SimpleGraph.extremalNumber`. Compared with the formal-conjectures
statement `ErdosProblems/1021.lean` (equivalent; no code imported).
-/

/-- The `1`-subdivision `G_k` of `K_k`: the bipartite graph between `{y₁, …, y_k}` (`Fin k`) and the
two-element subsets of `Fin k`, each subset joined to its two elements. -/
def cliqueSubdivision (k : ℕ) : SimpleGraph (Fin k ⊕ {p : Finset (Fin k) // p.card = 2}) :=
  SimpleGraph.fromRel fun x y => ∃ i p, x = Sum.inl i ∧ y = Sum.inr p ∧ i ∈ p.1

/-- Erdős Problem 1021: for every `k ≥ 3` there is `c_k > 0` with `ex(n, G_k) = O(n^{3/2 - c_k})`.
-/
def cliqueSubdivisionExtremalPowerSaving : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (SimpleGraph.extremalNumber n (cliqueSubdivision k) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2 - c))

/--
Resolved true: Conlon and Lee proved `ex(n, G_k) ≪ n^{3/2 - 6^{-k}}`, and Janzer improved the
exponent to `3/2 - 1/(4k - 6)`; erdosproblems.com/1021 lists the problem as proved, with a formal
proof in plby/lean-proofs (`Erdos1021.lean`). Source: T. F. Bloom, Erdős Problems, Problem #1021,
https://www.erdosproblems.com/1021 (status PROVED); resolution: D. Conlon and J. Lee, On the
extremal number of subdivisions, Int. Math. Res. Not. IMRN (2021), 9122-9145; O. Janzer, Improved
bounds for the extremal number of subdivisions, Electron. J. Combin. (2019), Paper No. 3.3,
Conlon-Lee: c_k = 6^{-k}; Janzer: c_k = 1/(4k - 6) (erdosproblems.com/1021),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1021.lean#L2359.
-/
public theorem_wanted cliqueSubdivisionExtremalPowerSaving_holds :
    cliqueSubdivisionExtremalPowerSaving

end MathlibExt.GraphTheory.CliqueSubdivisionExtremalErdosProblem1021Wanted
