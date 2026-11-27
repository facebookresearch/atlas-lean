/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import MathlibExt.NumberTheory.Ramanujan.Part1Ch2Entry7

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 6

Sum of arctan(1/(1+√2(k+1))²) over all k equals π/8.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example6

private lemma arctan_sqrt_two_sub_one : Real.arctan (Real.sqrt 2 - 1) = Real.pi / 8 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : 1 < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hadd := Real.arctan_add (x := Real.sqrt 2 - 1) (y := Real.sqrt 2 - 1) (by nlinarith)
  have hone : (Real.sqrt 2 - 1 + (Real.sqrt 2 - 1)) / (1 - (Real.sqrt 2 - 1) * (Real.sqrt 2 - 1))
      = 1 := by
    rw [div_eq_one_iff_eq (by nlinarith)]
    linear_combination h2
  rw [hone, Real.arctan_one] at hadd
  linarith

/-- **Series of arctangents of 1/(1 + k√2)² (Entry 7, Example 6).** The series
$$\sum_{k=0}^{\infty} \arctan \frac{1}{\bigl(1 + \sqrt{2}\,(k + 1)\bigr)^2}$$
converges absolutely and its sum is $\pi/8$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 6, printed p. 37 / PDF p. 47.
It follows from `Entry7.ramanujan_part1_ch2_entry7` at `n = 1 + √2`, whose partial sums
`arctan (2 r / (n ^ 2 + 2 n r + 1))` tend to `arctan (1 / n) = arctan (√2 - 1) = π / 8`.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example6`.
-/
theorem ramanujan_part1_ch2_entry7_example6 :
    HasSum (fun k : ℕ => Real.arctan (1 / ((1 + Real.sqrt 2 * (↑(k + 1) : ℝ)) ^ 2)))
      (Real.pi / 8) := by
  set n : ℝ := 1 + Real.sqrt 2 with hn_def
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 < n := by positivity
  have hterm (k : ℕ) :
      2 / (n + 2 * (k : ℝ) + 1) ^ 2 = 1 / (1 + Real.sqrt 2 * (↑(k + 1) : ℝ)) ^ 2 := by
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (2 * ((k : ℝ) + 1) ^ 2 - 1) * h2
  have hinv : n⁻¹ = Real.sqrt 2 - 1 := inv_eq_of_mul_eq_one_left (by linear_combination h2)
  have hlim : Filter.Tendsto (fun r : ℕ => Real.arctan (2 * (r : ℝ) / (n ^ 2 + 2 * n * r + 1)))
      Filter.atTop (nhds (Real.pi / 8)) := by
    have h := (tendsto_natCast_div_add_atTop ((n ^ 2 + 1) / (2 * n))).const_mul n⁻¹
    rw [mul_one, hinv] at h
    rw [← arctan_sqrt_two_sub_one]
    refine (Real.continuous_arctan.tendsto _).comp (h.congr fun r => ?_)
    have hr : (0 : ℝ) < r + (n ^ 2 + 1) / (2 * n) := by positivity
    rw [← hinv]
    field_simp
    ring
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun k => Real.arctan_nonneg.mpr (by positivity)) _).2 ?_
  refine hlim.congr fun r => ?_
  simp_rw [← hterm]
  exact (Entry7.ramanujan_part1_ch2_entry7 n r hn).symm

end Entry7Example6

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
