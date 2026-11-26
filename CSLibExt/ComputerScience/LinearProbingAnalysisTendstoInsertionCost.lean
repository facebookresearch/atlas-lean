/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingInsertionCost
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAsymptotics

/-!
# Expected cost of an unsuccessful linear-probing search at a fixed load factor

`tendsto_insertionCost`: with `n` items in `N` cells and `n / N → α < 1`, the mean insertion
cost tends to `(1 + 1 / (1 - α) ^ 2) / 2`. It follows from the exact formula `insertionCost_eq`
and the limit `tendsto_knuthE`. Source: D. E. Knuth, *Notes on "open" addressing*,
22 July 1963, typeset by H. Prodinger in 1997, Section 8.
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
theorem tendsto_insertionCost (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (n : ℕ → ℕ)
    (hn : ∀ᶠ N in atTop, n N < N)
    (hlim : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (insertionCost N (n N) : ℝ)) atTop
      (𝓝 ((1 + 1 / (1 - α) ^ 2) / 2)) := by
  -- `E₁(N, n N + 1) → 1 / (1 - α) ^ 2` by `tendsto_knuthE`.
  have hE : Tendsto (fun N : ℕ => (knuthE 1 N (n N + 1) : ℝ)) atTop
      (𝓝 (1 / (1 - α) ^ 2)) := by
    simpa using tendsto_knuthE 1 hα₀ hα₁ n hlim
  -- Hence `(1 + E₁) / 2` tends to the claimed limit.
  have hlim2 : Tendsto (fun N : ℕ => (1 + (knuthE 1 N (n N + 1) : ℝ)) / 2) atTop
      (𝓝 ((1 + 1 / (1 - α) ^ 2) / 2)) :=
    (tendsto_const_nhds.add hE).div_const 2
  -- `insertionCost N (n N)` equals `(1 + E₁) / 2` for all large `N`.
  have heq : ∀ᶠ N in atTop, (1 + (knuthE 1 N (n N + 1) : ℝ)) / 2 =
      (insertionCost N (n N) : ℝ) := by
    filter_upwards [hn] with N hN
    have hkN : n N + 1 ≤ N := by omega
    have h := insertionCost_eq N (n N + 1) (by omega) hkN
    rw [Nat.add_sub_cancel] at h
    exact_mod_cast h.symm
  exact hlim2.congr' heq

end Cslib.Algorithms.Lean.LinearProbing
