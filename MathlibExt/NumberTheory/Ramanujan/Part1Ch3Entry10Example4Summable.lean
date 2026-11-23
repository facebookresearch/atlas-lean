/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 10 Example 4

Summability of e⁻ˣxᵏHₖ/k!.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4Summable

/-- **Summability of the harmonic Poisson series.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th
harmonic number (so $H_0 = 0$). For every real $x$, the series
$\sum_{k=0}^{\infty} e^{-x} x^k H_k / k!$ is summable.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 4, printed pp.
    65-66 / PDF pp. 75-76.
Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example4_summable`.
-/
theorem ramanujan_part1_ch3_entry10_example4_summable (x : ℝ) :
    Summable (fun k : ℕ => Real.exp (-x) * x ^ k *
        (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ)) / (Nat.factorial k : ℝ)) := by
  have hHnonneg : ∀ k : ℕ, 0 ≤ (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ)) := by
    intro k
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hHle : ∀ k : ℕ, (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ)) ≤ (k : ℝ) := by
    intro k
    calc (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ))
        ≤ ∑ _j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          simp [Finset.mem_Icc] at hj
          have h1 : (1 : ℝ) ≤ (j : ℝ) := by
            exact_mod_cast hj.1
          exact div_le_one_of_le₀ h1 (by positivity)
      _ = ((Finset.Icc (1 : ℕ) k).card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) := by
          have hcard : (Finset.Icc (1 : ℕ) k).card ≤ k := by
            by_cases hk : k = 0
            · subst hk; simp
            · have : (Finset.Icc (1 : ℕ) k).card = k := by
                rw [Nat.card_Icc]
                omega
              omega
          exact_mod_cast hcard
  have hnorm : ∀ k : ℕ, ‖Real.exp (-x) * x ^ k *
        (∑ j ∈ Finset.Icc (1 : ℕ) k, (1 : ℝ) / (j : ℝ)) / (Nat.factorial k : ℝ)‖
      ≤ ‖Real.exp (-x)‖ * ‖x‖ ^ k * (k : ℝ) / (Nat.factorial k : ℝ) := by
    intro k
    have hHk := hHnonneg k
    have hHkle := hHle k
    have hfactpos : (0 : ℝ) < (Nat.factorial k : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    rw [norm_div, norm_mul, norm_mul, norm_pow,
      Real.norm_of_nonneg hHk, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hCK : (0 : ℝ) ≤ ‖Real.exp (-x)‖ * ‖x‖ ^ k :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    have h1 : ‖Real.exp (-x)‖ * ‖x‖ ^ k * (∑ j ∈ Finset.Icc 1 k, 1 / (j : ℝ))
        ≤ ‖Real.exp (-x)‖ * ‖x‖ ^ k * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hHkle hCK
    exact div_le_div_of_nonneg_right h1 (le_of_lt hfactpos)
  have hgsumm : Summable (fun k : ℕ => ‖Real.exp (-x)‖ * ‖x‖ ^ k * (k : ℝ) / (Nat.factorial k : ℝ)) := by
    have htail : Summable (fun n : ℕ => (‖Real.exp (-x)‖ * ‖x‖) * (‖x‖ ^ n / (Nat.factorial n : ℝ))) := by
      exact (Real.summable_pow_div_factorial ‖x‖).mul_left _
    have heq : (fun n : ℕ => (‖Real.exp (-x)‖ * ‖x‖) * (‖x‖ ^ n / (Nat.factorial n : ℝ)))
        = (fun n : ℕ => (‖Real.exp (-x)‖ * ‖x‖ ^ (n + 1) * (((n + 1 : ℕ)) : ℝ) / ((Nat.factorial (n + 1) : ℕ) : ℝ))) := by
      funext n
      have hM : (((n + 1 : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hfact : ((Nat.factorial (n + 1) : ℕ) : ℝ) = (((n + 1 : ℕ)) : ℝ) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      rw [hfact, pow_succ]
      rw [mul_comm (((n + 1 : ℕ)) : ℝ) (Nat.factorial n : ℝ)]
      rw [← mul_div_mul_right _ _ hM]
      ring
    rw [heq] at htail
    exact (summable_nat_add_iff 1).mp htail
  exact Summable.of_norm_bounded hgsumm hnorm

end Entry10Example4Summable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
