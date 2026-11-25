/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import MathlibExt.NumberTheory.Ramanujan.Part1Ch2Entry7

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 5

Sum of arctan(1/(2(n+1)²)) over all n equals π/4.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example5First

/-- **Series of arctangents of 1/(2k²) (Entry 7, Example 5).** The series
$$\sum_{n=0}^{\infty} \arctan \frac{1}{2(n + 1)^2}$$
converges absolutely and its sum is $\pi/4$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 5, printed p. 37 / PDF p. 47.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example5_first`.
-/
theorem ramanujan_part1_ch2_entry7_example5_first :
    HasSum (fun n : ℕ => Real.arctan (1 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2))) (Real.pi / 4) := by
  have hnn : ∀ i : ℕ, 0 ≤ Real.arctan (1 / (2 * ((i + 1 : ℕ) : ℝ) ^ 2)) := by
    intro i
    rw [Real.arctan_nonneg]
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ r : ℕ, ∑ k ∈ Finset.range r, Real.arctan (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 2))
      = Real.arctan ((r : ℝ) / (r + 1)) := by
    intro r
    have hr : (0 : ℝ) < r + 1 := by positivity
    rw [show (r : ℝ) / (r + 1) = 2 * (r : ℝ) / (1 ^ 2 + 2 * 1 * (r : ℝ) + 1) by field_simp; ring,
      ← Entry7.ramanujan_part1_ch2_entry7 1 r one_pos]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hps]
  rw [← Real.arctan_one]
  exact (Real.continuous_arctan.tendsto _).comp (tendsto_natCast_div_add_atTop 1)

end Entry7Example5First

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
