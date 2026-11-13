/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest sets with distinct reciprocal subset sums (Erdős Problem 321)

Erdős Problem 321: what is the size of the largest `A ⊆ {1, …, N}` such that all sums `∑_{n ∈ S}
1/n` are distinct for `S ⊆ A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctReciprocalSubsetSumsErdosProblem321Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #321, https://www.erdosproblems.com/321 (status
SOLVED). UnsolvedMath record UM-00002047 (`EP-321`), dataset ulamai/UnsolvedMath v1.8.0.

`R(N)` is the largest such size (a maximum over subsets of `{1, …, N}`, so the `sSup` is
attained). erdosproblems.com/321 records `R(N) ≍ (N / log N) ∏_{j=3}^{k} log_j N` 'where `k` is
such that `log_k N = O(1)`' (the page prints `log_k N` inside the product; the companion page
erdosproblems.com/320 prints `log_j N`, used here). The index is made concrete: the bounds are
asserted for every `k ≥ 3` such that all iterates `log_j N`, `j ≤ k`, are at least `1` and `log_k
N ≤ e`. Requiring every iterate to be at least `1` matters: `Real.log` takes `|x|`, so a later
iterate can return to `[1, e]` after a factor below `1` or a negative factor, which would make the
product meaningless. For large `N` such a `k` exists and is unique up to one step, and changing
the window `[1, e]` changes the product by a bounded factor. The exact value of `R(N)` is not
known; only the order of magnitude is stated. Compared with the formal-conjectures statement
`ErdosProblems/321.lean` (formal-conjectures keeps the value open with `answer(sorry)` and states
only the Bleicher-Erdős bounds; no code imported).
-/

open Filter Real

/-- `R(N)`: the largest size of a set `A ⊆ {1, …, N}` such that the sums `∑_{n ∈ S} 1 / n`,
`S ⊆ A`, are pairwise distinct. -/
noncomputable def maxDistinctReciprocalSums (N : ℕ) : ℕ :=
  sSup {m | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    Set.InjOn (fun S : Finset ℕ => ∑ n ∈ S, (1 : ℚ) / n) (A.powerset : Set (Finset ℕ)) ∧
    A.card = m}

/-- `(N / log N) ∏_{j = 3}^{k} log_j N`, where `log_j` is the `j`-fold iterated natural
logarithm. -/
noncomputable def iteratedLogScale (k N : ℕ) : ℝ :=
  (N : ℝ) / log N * ∏ j ∈ Finset.Icc 3 k, log^[j] (N : ℝ)

/-- Erdős Problem 321, with the order of magnitude recorded on erdosproblems.com:
`R(N) ≍ (N / log N) ∏_{j = 3}^{k} log_j N`, where `k = k(N)` is chosen with `log_k N = O(1)`.
Here `k` is any index `≥ 3` such that the iterates `log_j N`, `j ≤ k`, are all at least `1` and
`log_k N ≤ e` (for large `N` such a `k` exists and is unique up to one step). -/
def distinctReciprocalSumsOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 3 ≤ k →
    (∀ j ≤ k, 1 ≤ log^[j] (N : ℝ)) → log^[k] (N : ℝ) ≤ exp 1 →
    c * iteratedLogScale k N ≤ maxDistinctReciprocalSums N ∧
      (maxDistinctReciprocalSums N : ℝ) ≤ C * iteratedLogScale k N

/--
Resolved (order of magnitude; upper bound AI-generated and unrefereed): erdosproblems.com/321
records `R(N) ≍ (N / log N) ∏_{j=3}^{k} log_j N` with `log_k N = O(1)`, the upper bound proved by
GPT 5.6 Sol and the lower bound implicit in Bettin-Grenié-Molteni-Sanna, and lists the problem as
solved. Source: T. F. Bloom, Erdős Problems, Problem #321, https://www.erdosproblems.com/321
(status SOLVED); resolution: upper bound: GPT 5.6 Sol (prompted by Young, Zhu and Luo), proof
linked from erdosproblems.com/320 (AI-generated, unrefereed); lower bound: implicit in S. Bettin,
L. Grenié, G. Molteni and C. Sanna, A lower bound for the number of Egyptian fractions, Math.
Comp. (2026), doi:10.1090/mcom/4190 (arXiv:2509.10030), as stated on erdosproblems.com/321,
erdosproblems.com/321: 'It is now known that R(N) ≍ log S(N) ≍ (N / log N) ∏_{j=3}^k log_k N where
k is such that log_k N = O(1). The lower bound is implicit in work of Bettin, Grenié, Molteni, and
Sanna. The upper bound was proved by GPT 5.6 Sol'; status solved,
https://www.erdosproblems.com/321.
-/
public theorem_wanted distinctReciprocalSumsOrder_holds : distinctReciprocalSumsOrder

end MathlibExt.NumberTheory.DistinctReciprocalSubsetSumsErdosProblem321Wanted
