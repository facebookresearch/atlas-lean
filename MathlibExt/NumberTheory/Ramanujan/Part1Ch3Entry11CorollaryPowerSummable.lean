/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Corollary to Entry 11

Summability of ‖aⱼ‖ implies summability of ‖aⱼⁿ‖ for n≥1.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry11CorollaryPowerSummable

/-- **Powers of an absolutely summable sequence are absolutely summable.** Let $(a_j)_{j \ge 0}$
be a sequence of complex numbers with $\sum_j |a_j| < \infty$, and let $n \ge 1$ be an integer.
Then $\sum_j |a_j^n| < \infty$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Corollary to Entry 11, printed p.
    66 / PDF p. 76.
Proves `Wanted` entry `ramanujan_part1_ch3_entry11_corollary_power_summable`.
-/
theorem ramanujan_part1_ch3_entry11_corollary_power_summable (a : ℕ → ℂ)
    (ha : Summable (fun j => ‖a j‖)) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun j => ‖(a j) ^ n‖) := by
  have htend : Filter.Tendsto (fun j => ‖a j‖) Filter.atTop (nhds 0) :=
    ha.tendsto_atTop_zero
  have hev : ∀ᶠ j in Filter.atTop, ‖a j‖ < 1 :=
    htend.eventually (gt_mem_nhds zero_lt_one)
  have hpow : ∀ᶠ j in Filter.atTop, ‖(a j) ^ n‖ ≤ ‖a j‖ := by
    filter_upwards [hev] with j hj
    rw [norm_pow]
    exact pow_le_of_le_one (norm_nonneg _) (le_of_lt hj) (by omega)
  have hcof : ∀ᶠ j in Filter.cofinite, ‖(a j) ^ n‖ ≤ ‖a j‖ := by
    rwa [Nat.cofinite_eq_atTop]
  have hsum : Summable (fun j => (a j) ^ n) :=
    ha.of_norm_bounded_eventually hcof
  exact hsum.norm

end Entry11CorollaryPowerSummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
