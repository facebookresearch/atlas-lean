/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingSuccessfulSearchCost
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Analysis of hashing with linear probing: wanted results

Knuth's exact mean costs of linear probing and their load-factor asymptotics, for the model of
`CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAnalysis` (a cyclic table of `N` cells,
independent uniform hash addresses). Source: D. E. Knuth, *Notes on "open" addressing*,
22 July 1963, typeset by H. Prodinger in 1997.

The exact insertion and successful-search formulas are proved in
`CSLibExt.Algorithms.Lean.DataStructures.LinearProbingInsertionCost` and
`CSLibExt.Algorithms.Lean.DataStructures.LinearProbingSuccessfulSearchCost`.

* `tendsto_insertionCost`, `tendsto_successfulSearchCost`: with `n` items in `N` cells and
  `n / N → α < 1`, the costs tend to `(1 + 1 / (1 - α) ^ 2) / 2` and `(1 + 1 / (1 - α)) / 2`.
  Section 8 of the note derives these as the approximations `E_r(N, k) ≈ (1 - α) ^ -(r + 1)`
  with `α = (k - 1) / N`, and states that they become exact as `N → ∞` for fixed `α`. The
  limit of the sums, `tendsto_knuthE` in
  `CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAsymptotics`, is proved; with the exact
  formulas it yields these two limits.
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

namespace Cslib.Algorithms.Lean.LinearProbing

/-- **Expected cost of an unsuccessful linear-probing search at a fixed load factor.** If a cyclic
table of `N` cells holds `n N` items with `n N < N` for all large `N` and `n N / N → α` with
`0 ≤ α < 1`, then the expected number of probes to insert one more item (equivalently, of an
unsuccessful search), with independent uniform hash addresses, tends to
`(1 + 1 / (1 - α) ^ 2) / 2` (Knuth, *Notes on "open" addressing*, 1963, Section 8: the
approximation `M(N, k) ≈ (1 + 1 / (1 - α) ^ 2) / 2` with `α = (k - 1) / N`, exact as
`N → ∞`). -/
theorem_wanted tendsto_insertionCost (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (n : ℕ → ℕ)
    (hn : ∀ᶠ N in atTop, n N < N)
    (hlim : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (insertionCost N (n N) : ℝ)) atTop
      (𝓝 ((1 + 1 / (1 - α) ^ 2) / 2))

/-- **Expected cost of a successful linear-probing search at a fixed load factor.** If a cyclic
table of `N` cells holds `n N` items with `1 ≤ n N ≤ N` for all large `N` and `n N / N → α` with
`0 ≤ α < 1`, then the average number of probes of a successful search, with independent uniform
hash addresses, tends to `(1 + 1 / (1 - α)) / 2` (Knuth, *Notes on "open" addressing*, 1963,
Section 8: the approximation `T(N, k) ≈ (1 + 1 / (1 - α)) / 2`, exact as `N → ∞`). -/
theorem_wanted tendsto_successfulSearchCost (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (n : ℕ → ℕ)
    (hn : ∀ᶠ N in atTop, 1 ≤ n N ∧ n N ≤ N)
    (hlim : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (successfulSearchCost N (n N) : ℝ)) atTop
      (𝓝 ((1 + 1 / (1 - α)) / 2))

end Cslib.Algorithms.Lean.LinearProbing
