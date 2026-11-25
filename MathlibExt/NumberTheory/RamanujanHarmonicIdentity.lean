/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.BinomialHarmonicConvolution

/-! # Uniqueness in the diagonal Ramanujan identity -/

public section

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

/-- Specialize the binomial–harmonic convolution at `k = n - 1`. The term at one
vanishes by symmetry of the two binomial coefficients. -/
private theorem harmonic_diagonal (n : ℕ) (hn : 2 ≤ n) :
    ∑ ν ∈ Finset.Icc 2 n,
        (((2 * n - ν - 2).choose (n - 1) : ℂ) - ((2 * n - ν - 2).choose (n - 2) : ℂ)) *
          (harmonic ν : ℂ) =
      ((2 * n - 1).choose (n - 1) : ℂ) * ((harmonic (n - 1) : ℂ) - (harmonic n : ℂ)) := by
  have h := MetaMathlibExt.binomial_harmonic_convolution (n - 1) n (by omega) (by omega)
  have top (ν : ℕ) : n + (n - 1) - ν - 1 = 2 * n - ν - 2 := by omega
  have symm : (2 * n - 1 - 2).choose (n - 1) = (2 * n - 1 - 2).choose (n - 2) :=
    Nat.choose_symm_of_eq_add (by omega)
  simp only [top] at h
  simp only [show n + (n - 1) = 2 * n - 1 by omega,
    show n - 1 - 1 = n - 2 by omega] at h
  rw [← Finset.insert_Icc_succ_left_eq_Icc (show 1 ≤ n by omega),
    Finset.sum_insert (by simp), symm, sub_self, zero_mul, zero_add] at h
  exact_mod_cast h

/-- **Uniqueness of the harmonic solution of the diagonal Ramanujan identity.** Let
$K : \mathbb{N} \to \mathbb{C}$ be a sequence such that for every integer $n \ge 2$
$$
\sum_{\nu=2}^{n} \Bigl(\binom{2n-\nu-2}{n-1} - \binom{2n-\nu-2}{n-2}\Bigr) K(\nu) =
\binom{2n-1}{n-1} \bigl(K(n-1) - K(n)\bigr).
$$
Then there is a constant $\lambda \in \mathbb{C}$ such that $K(r) = \lambda H_r$ for every integer
$r \ge 1$, where $H_r = \sum_{j=1}^{r} 1/j$ is the $r$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Theorem 8. -/
theorem eq_lambda_mul_harmonic_of_sum_choose_sub_mul_eq
    (K : ℕ → ℂ)
    (hK : ∀ n : ℕ, 2 ≤ n →
      ∑ ν ∈ Finset.Icc 2 n,
          (((Nat.choose (2 * n - ν - 2) (n - 1) : ℂ) -
            (Nat.choose (2 * n - ν - 2) (n - 2) : ℂ)) * K ν) =
        (Nat.choose (2 * n - 1) (n - 1) : ℂ) * (K (n - 1) - K n)) :
    ∃ lam : ℂ, ∀ r : ℕ, 1 ≤ r → K r = lam * (harmonic r : ℂ) := by
  let D (i : ℕ) := K i - K 1 * (harmonic i : ℂ)
  suffices h : ∀ r : ℕ, 1 ≤ r → D r = 0 from
    ⟨K 1, fun r hr => sub_eq_zero.mp (h r hr)⟩
  intro r
  induction r using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    obtain rfl | hn := eq_or_lt_of_le hn
    · simp [D, harmonic]
    let a (ν : ℕ) : ℂ :=
      ((2 * n - ν - 2).choose (n - 1) : ℂ) - ((2 * n - ν - 2).choose (n - 2) : ℂ)
    let C : ℂ := (2 * n - 1).choose (n - 1)
    have hrow : ∑ ν ∈ Finset.Icc 2 n, a ν * D ν = C * (D (n - 1) - D n) := calc
      _ = (∑ ν ∈ Finset.Icc 2 n, a ν * K ν) -
            K 1 * ∑ ν ∈ Finset.Icc 2 n, a ν * (harmonic ν : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ν _
        dsimp only [D]
        ring
      _ = _ := by
        dsimp only [a, C, D]
        rw [hK n hn, harmonic_diagonal n hn]
        ring
    -- Only the endpoint survives in the recurrence for the difference.
    rw [Finset.sum_eq_single n, ih (n - 1) (by omega) (by omega), zero_sub] at hrow
    · have ha : a n = -1 := by
        simp [a, show 2 * n - n - 2 = n - 2 by omega,
          Nat.choose_eq_zero_of_lt (show n - 2 < n - 1 by omega)]
      have hC : C - 1 ≠ 0 := by
        have hle := Nat.choose_le_choose (n - 1) (show n ≤ 2 * n - 1 by omega)
        rw [Nat.choose_symm_of_eq_add (show n = (n - 1) + 1 by omega),
          Nat.choose_one_right] at hle
        dsimp only [C]
        apply sub_ne_zero.mpr
        exact_mod_cast (show (2 * n - 1).choose (n - 1) ≠ 1 by omega)
      rw [ha] at hrow
      apply (mul_eq_zero.mp ?_).resolve_left hC
      linear_combination hrow
    · intro ν hν hne
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hν
      rw [ih ν (by omega) (by omega), mul_zero]
    · simp [hn]

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
