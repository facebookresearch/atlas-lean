/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAnalysis
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAsymptotics
import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingSuccessfulSearchCost

/-!
# Expected cost of a successful linear-probing search at a fixed load factor

`tendsto_successfulSearchCost`: with `1 ≤ n N ≤ N` eventually and `n N / N → α < 1`, the mean
successful-search cost tends to `(1 + 1 / (1 - α)) / 2`. The proof uses the exact formula
`successfulSearchCost_eq` and the limit `tendsto_knuthE`. Source: D. E. Knuth,
*Notes on "open" addressing*, 22 July 1963, typeset by H. Prodinger in 1997.
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

namespace Cslib.Algorithms.Lean.LinearProbing

/-- **Expected cost of a successful linear-probing search at a fixed load factor.** If a cyclic
table of `N` cells holds `n N` items with `1 ≤ n N ≤ N` for all large `N` and `n N / N → α` with
`0 ≤ α < 1`, then the average number of probes of a successful search, with independent uniform
hash addresses, tends to `(1 + 1 / (1 - α)) / 2` (Knuth, *Notes on "open" addressing*, 1963,
Section 8: the approximation `T(N, k) ≈ (1 + 1 / (1 - α)) / 2`, exact as `N → ∞`). -/
public theorem tendsto_successfulSearchCost (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (n : ℕ → ℕ)
    (hn : ∀ᶠ N in atTop, 1 ≤ n N ∧ n N ≤ N)
    (hlim : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (successfulSearchCost N (n N) : ℝ)) atTop
      (𝓝 ((1 + 1 / (1 - α)) / 2))
    := by
  have hshift : Tendsto (fun N : ℕ => ((n N - 1 : ℕ) : ℝ) / N) atTop (𝓝 α) := by
    have hsub : Tendsto (fun N : ℕ => (n N : ℝ) / N - 1 / N) atTop (𝓝 α) := by
      simpa using hlim.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    apply hsub.congr'
    filter_upwards [hn] with N hN
    rw [Nat.cast_sub hN.1, Nat.cast_one, sub_div]
  have hE : Tendsto (fun N : ℕ => (knuthE 0 N (n N - 1 + 1) : ℝ)) atTop
      (𝓝 (1 / (1 - α))) := by
    simpa using tendsto_knuthE 0 hα₀ hα₁ (fun N => n N - 1) hshift
  have hcost : Tendsto (fun N : ℕ => (1 + (knuthE 0 N (n N - 1 + 1) : ℝ)) / 2)
      atTop (𝓝 ((1 + 1 / (1 - α)) / 2)) :=
    (tendsto_const_nhds.add hE).div_const 2
  apply hcost.congr'
  filter_upwards [hn] with N hN
  rw [Nat.sub_add_cancel hN.1]
  exact_mod_cast (successfulSearchCost_eq N (n N) hN.1 hN.2).symm

end Cslib.Algorithms.Lean.LinearProbing
