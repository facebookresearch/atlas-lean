/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GDifferenceBases
import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Topology.Order.OrderClosed

/-! # Tests for convergence of the normalized difference basis numbers -/

namespace MathlibExtTest.Combinatorics.GDifferenceBases

open MetaMathlibExt Filter
open scoped Topology

-- The normalized `1`-difference basis numbers converge to a positive limit.
example : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => (diffBasisNumber 1 n : ℝ) / Real.sqrt n) atTop (𝓝 c) :=
  tendsto_diffBasisNumber_div_sqrt 1 one_pos

-- The limit for `g = 1` is at least `√2`, by the interval lower bound.
example : ∃ c : ℝ, Real.sqrt 2 ≤ c ∧
    Tendsto (fun n : ℕ => (diffBasisNumber 1 n : ℝ) / Real.sqrt n) atTop (𝓝 c) := by
  obtain ⟨c, -, hc_lim⟩ := tendsto_diffBasisNumber_div_sqrt 1 one_pos
  refine ⟨c, ?_, hc_lim⟩
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.sqrt 2 ≤ (diffBasisNumber 1 n : ℝ) / Real.sqrt n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have h := sqrt_two_mul_le_diffBasisNumber_div_sqrt 1 n hn
    simpa using h
  exact ge_of_tendsto hc_lim hev

end MathlibExtTest.Combinatorics.GDifferenceBases
