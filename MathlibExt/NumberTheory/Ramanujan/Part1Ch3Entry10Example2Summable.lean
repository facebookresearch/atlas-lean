/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10 Example 2

Summability of e⁻ˣxʲ⁺¹log(j+2)/(j+1)!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example2Summable

/-- **Summability of the logarithmic Poisson series.** For every real $x$, the series
$\sum_{k=1}^{\infty} e^{-x} x^k \log(k + 1) / k!$ is summable.

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example2_summable`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 2, printed p.
    65 / PDF p. 75.
-/
theorem ramanujan_part1_ch3_entry10_example2_summable :
    ∀ (x : ℝ),
        Summable (fun j : ℕ => Real.exp (-x) * x ^ (j + 1) * Real.log ((j : ℝ) + 2) /
            (Nat.factorial (j + 1) : ℝ)) := by
  intro x
  have hsum : Summable (fun j : ℕ =>
      Real.exp (-x) * |x| * (|x| ^ j / (Nat.factorial j : ℝ))) :=
    (Real.summable_pow_div_factorial |x|).mul_left _
  refine Summable.of_norm_bounded hsum fun j => ?_
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hlog_nonneg : 0 ≤ Real.log ((j : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hlog_le : Real.log ((j : ℝ) + 2) ≤ (j : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 2)
    linarith
  simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg hlog_nonneg,
    norm_natCast]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  calc
    Real.exp (-x) * |x| ^ (j + 1) * Real.log ((j : ℝ) + 2) /
          (((j : ℝ) + 1) * (Nat.factorial j : ℝ))
        ≤ Real.exp (-x) * |x| ^ (j + 1) * ((j : ℝ) + 1) /
          (((j : ℝ) + 1) * (Nat.factorial j : ℝ)) := by
            gcongr
    _ = Real.exp (-x) * |x| * (|x| ^ j / (Nat.factorial j : ℝ)) := by
          rw [pow_succ]
          field_simp

end Entry10Example2Summable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
