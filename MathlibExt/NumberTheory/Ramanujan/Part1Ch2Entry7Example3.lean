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
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 3

Sum of arctan(1/(2(n+k+1)²)) equals arctan(1/(2n+1)).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example3

/-- **Arctangent series with halved squares (Entry 7, Example 3).** For every real number
$n > 0$, the series
$$\sum_{k=0}^{\infty} \arctan \frac{1}{2(n + k + 1)^2}$$
converges absolutely and its sum is $\arctan \frac{1}{2n + 1}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 3, formula (7.6), printed p. 36 / PDF p. 46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example3`.
-/
theorem ramanujan_part1_ch2_entry7_example3 (n : ℝ) (hn : 0 < n) :
    HasSum (fun k : ℕ => Real.arctan (1 / (2 * (n + (k : ℝ) + 1) ^ 2)))
      (Real.arctan (1 / (2 * n + 1))) := by
  have hnn : ∀ i : ℕ, 0 ≤ Real.arctan (1 / (2 * (n + (i : ℝ) + 1) ^ 2)) := by
    intro i
    rw [Real.arctan_nonneg]
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ r : ℕ, ∑ k ∈ Finset.range r, Real.arctan (1 / (2 * (n + (k : ℝ) + 1) ^ 2))
      = Real.arctan (2 * (r : ℝ) / ((2 * n + 1) ^ 2 + 2 * (2 * n + 1) * (r : ℝ) + 1)) := by
    intro r
    rw [← Entry7.ramanujan_part1_ch2_entry7 (2 * n + 1) r (by linarith)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    field_simp
    ring
  simp_rw [hps]
  have hlim : Filter.Tendsto
      (fun r : ℕ => 2 * (r : ℝ) / ((2 * n + 1) ^ 2 + 2 * (2 * n + 1) * (r : ℝ) + 1))
      Filter.atTop (nhds (1 / (2 * n + 1))) := by
    have h := (tendsto_natCast_div_add_atTop
      (((2 * n + 1) ^ 2 + 1) / (2 * (2 * n + 1)) : ℝ)).const_mul (1 / (2 * n + 1))
    rw [mul_one] at h
    refine h.congr fun r => ?_
    have : (0 : ℝ) < 2 * n + 1 := by linarith
    field_simp
    ring
  exact (Real.continuous_arctan.tendsto _).comp hlim

end Entry7Example3

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
