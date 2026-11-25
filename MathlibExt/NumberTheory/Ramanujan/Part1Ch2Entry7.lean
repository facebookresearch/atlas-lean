/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7

Telescoping sum of arctan(2/(n+2k+1)²) via the arctan addition formula.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7

/-- **Ramanujan's finite arctangent sum (Entry 7).** For every real number $n > 0$ and every
natural number $r$,
$$\sum_{k=0}^{r-1} \arctan \frac{2}{(n + 2k + 1)^2} = \arctan \frac{2r}{n^2 + 2nr + 1}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, formula (7.2), printed pp. 35-36 / PDF pp. 45-46.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7`.
-/
theorem ramanujan_part1_ch2_entry7 (n : ℝ) (r : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range r, Real.arctan (2 / (n + 2 * (k : ℝ) + 1) ^ 2) =
      Real.arctan (2 * (r : ℝ) / (n ^ 2 + 2 * n * (r : ℝ) + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hD : (0 : ℝ) < n ^ 2 + 2 * n * (r : ℝ) + 1 := by positivity
    have hD' : (0 : ℝ) < n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1 := by positivity
    have hE : (0 : ℝ) < n + 2 * (r : ℝ) + 1 := by positivity
    set A : ℝ := 2 * (r : ℝ) / (n ^ 2 + 2 * n * (r : ℝ) + 1) with hA
    set C : ℝ := 2 * ((r : ℝ) + 1) / (n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1) with hC
    set B : ℝ := 2 / (n + 2 * (r : ℝ) + 1) ^ 2 with hB
    have hA_nonneg : 0 ≤ A := by positivity
    have hC_nonneg : 0 ≤ C := by positivity
    have hCA : 0 ≤ C * A := mul_nonneg hC_nonneg hA_nonneg
    have h1CA : (0 : ℝ) < 1 + C * A := by linarith
    have h1CA' : (1 : ℝ) + C * A ≠ 0 := ne_of_gt h1CA
    have hcond : C * (-A) < 1 := by
      have : C * (-A) = -(C * A) := by ring
      rw [this]
      linarith
    have hadd := Real.arctan_add (x := C) (y := -A) hcond
    rw [Real.arctan_neg] at hadd
    have hsub : C + -A = C - A := by ring
    have hden : (1 : ℝ) - C * -A = 1 + C * A := by ring
    rw [hsub, hden] at hadd
    have hEq : (C - A) / (1 + C * A) = B := by
      rw [hA, hC, hB]
      have hDne : (n ^ 2 + 2 * n * (r : ℝ) + 1) ≠ 0 := ne_of_gt hD
      have hDne' : (n ^ 2 + 2 * n * ((r : ℝ) + 1) + 1) ≠ 0 := ne_of_gt hD'
      have hEne : (n + 2 * (r : ℝ) + 1) ≠ 0 := ne_of_gt hE
      have hE2ne : ((n + 2 * (r : ℝ) + 1) ^ 2) ≠ 0 := pow_ne_zero 2 hEne
      field_simp
      ring
    rw [hEq] at hadd
    -- hadd : arctan C + -arctan A = arctan B
    have hgoal : Real.arctan A + Real.arctan B = Real.arctan C := by linarith [hadd]
    -- cast alignment: goal uses ((r+1 : ℕ) : ℝ) forms
    push_cast at hgoal ⊢
    -- hgoal and goal should now match up to the definitions of A B C
    rw [hA, hC, hB] at hgoal
    linarith [hgoal]
    -- NOTE: above linarith needs exact syntactic match; fallback:
    -- exact hgoal

end Entry7

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
