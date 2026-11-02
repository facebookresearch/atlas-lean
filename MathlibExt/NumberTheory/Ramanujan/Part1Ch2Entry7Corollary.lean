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
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 7

Infinite sum of arctan(2/(n+2k+1)²) equals arctan(1/n).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Corollary

/-- **Ramanujan's infinite arctangent series (corollary to Entry 7).** For every real number
$n > 0$, the series
$$\sum_{k=0}^{\infty} \arctan \frac{2}{(n + 2k + 1)^2}$$
converges absolutely and its sum is $\arctan(1/n)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2,
    corollary to Entry 7, formula (7.3), printed p. 36 / PDF p. 46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_corollary`.
-/
theorem ramanujan_part1_ch2_entry7_corollary (n : ℝ) (hn : 0 < n) :
    HasSum (fun k : ℕ => Real.arctan (2 / ((n + 2 * (k : ℝ) + 1) ^ 2))) (Real.arctan (1 / n)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun k => Real.arctan_nonneg.mpr (by positivity)]
  simp only [Entry7.ramanujan_part1_ch2_entry7 n _ hn]
  have hlim : Filter.Tendsto (fun N : ℕ => 2 * (N : ℝ) / (n ^ 2 + 2 * n * (N : ℝ) + 1))
      Filter.atTop (nhds (1 / n)) := by
    have h := (tendsto_natCast_div_add_atTop ((n ^ 2 + 1) / (2 * n) : ℝ)).const_mul (1 / n)
    rw [mul_one] at h
    refine h.congr fun N => ?_
    field_simp
    ring
  exact (Real.continuous_arctan.tendsto _).comp hlim

end Entry7Corollary

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
