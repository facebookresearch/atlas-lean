/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SidonSubsetCountDivergence

open Filter MathlibExt.Combinatorics.SidonSubsetCountErdosProblem861Wanted

-- Every fixed number of extra bits fits in the count for all sufficiently large intervals.
example (t : ℕ) : ∀ᶠ N : ℕ in atTop, 2 ^ (maxSidonSize N + t) ≤ (sidonSubsetsUpTo N).card := by
  have h := tendsto_atTop.mp sidonCountOverTwoPowMaxDiverges_holds ((2 : ℝ) ^ t)
  filter_upwards [h] with N hN
  have hpow := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ maxSidonSize N)).mp hN
  rw [← pow_add, Nat.add_comm] at hpow
  exact_mod_cast hpow
