/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10, Example 1

Eventual summability of xʲ⁺¹√(j+1)/(j+1)!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SummableEventually

/-- **Eventual summability of the square-root Poisson series.** For all sufficiently large
real $x$, the series $\sum_{k=1}^{\infty} x^k \sqrt{k} / k!$ is summable.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 1, printed p.
    64 / PDF p. 74.
Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example1_summable_eventually`.
-/
theorem ramanujan_part1_ch3_entry10_example1_summable_eventually :
    ∀ᶠ (x : ℝ) in Filter.atTop,
        Summable (fun j : ℕ => x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) /
            (↑(Nat.factorial (j + 1)) : ℝ)) := by
  apply Filter.Eventually.of_forall
  intro x
  have hfact : ∀ j : ℕ, (0 : ℝ) < ((Nat.factorial (j + 1) : ℕ) : ℝ) := fun j =>
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hsqrt_le : ∀ j : ℕ, Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    intro j
    rw [Real.sqrt_le_self_iff]
    right
    have : 1 ≤ j + 1 := Nat.le_add_left 1 j
    exact_mod_cast this
  have hmajor :
      Summable (fun j : ℕ => (|x| ^ (j + 1) * ((j + 1 : ℕ) : ℝ)) /
          ((Nat.factorial (j + 1) : ℕ) : ℝ)) := by
    have hbase : Summable (fun j : ℕ => |x| ^ j / ((Nat.factorial j : ℕ) : ℝ)) :=
      Real.summable_pow_div_factorial |x|
    have h2 : Summable (fun j : ℕ => (|x| ^ j / ((Nat.factorial j : ℕ) : ℝ)) * |x|) :=
      hbase.mul_right |x|
    apply h2.congr (fun j => ?_)
    have hfj : ((Nat.factorial (j + 1) : ℕ) : ℝ) =
        ((j + 1 : ℕ) : ℝ) * ((Nat.factorial j : ℕ) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hfj]
    field_simp
    ring
  apply Summable.of_norm_bounded hmajor
  intro j
  have hpos : (0 : ℝ) < ((Nat.factorial (j + 1) : ℕ) : ℝ) := hfact j
  have h1 : |Real.sqrt ((j + 1 : ℕ) : ℝ)| = Real.sqrt ((j + 1 : ℕ) : ℝ) :=
    abs_of_nonneg (Real.sqrt_nonneg _)
  have habs : |((Nat.factorial (j + 1) : ℕ) : ℝ)| = ((Nat.factorial (j + 1) : ℕ) : ℝ) :=
    abs_of_pos hpos
  have hle : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := hsqrt_le j
  have hpow_nonneg : 0 ≤ |x| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
  calc ‖x ^ (j + 1) * Real.sqrt (↑(j + 1) : ℝ) / (↑(Nat.factorial (j + 1)) : ℝ)‖
      = |x| ^ (j + 1) * Real.sqrt ((j + 1 : ℕ) : ℝ) / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, h1, habs]
    _ ≤ |x| ^ (j + 1) * ((j + 1 : ℕ) : ℝ) / ((Nat.factorial (j + 1) : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
        exact mul_le_mul_of_nonneg_left hle hpow_nonneg

end Entry10Example1SummableEventually

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
