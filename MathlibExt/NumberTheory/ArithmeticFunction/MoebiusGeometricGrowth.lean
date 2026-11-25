/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Möbius transforms of geometrically growing sequences

The Möbius transform of a nonnegative real sequence growing by a factor of at least
$1.221$ at each positive index is nonnegative at every positive index.
-/

namespace MetaMathlibExt

open Finset
open scoped ArithmeticFunction.Moebius

private def negativeDivisors (n : ℕ) : Finset ℕ :=
  n.properDivisors.filter fun d => μ (n / d) = -1

-- For large n there are at most m = ⌊n/2⌋ proper divisors, each at least m steps from n.
private lemma half_le_growth (m : ℕ) (hm : 13 ≤ m) :
    (m : ℚ) ≤ (1221 / 1000 : ℚ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hm' : (13 : ℚ) ≤ m := by exact_mod_cast hm
    rw [pow_succ, Nat.cast_succ]
    linarith

private lemma negative_weight_le_one (n : ℕ) :
    ∑ d ∈ negativeDivisors n, (1000 / 1221 : ℚ) ^ (n - d) ≤ 1 := by
  by_cases hn : n < 26
  · -- This finite sum includes only negative Möbius terms. At n = 6 its
    -- two weights are (1000/1221)^3 and (1000/1221)^4.
    have small : ∀ k : Fin 26,
        ∑ d ∈ negativeDivisors k, (1000 / 1221 : ℚ) ^ (k.val - d) ≤ 1 := by decide +kernel
    exact small ⟨n, hn⟩
  let m := n / 2
  have hsub : negativeDivisors n ⊆ Icc 1 m := by
    intro d hd
    have hd' := (mem_filter.mp hd).1
    have hmul := (Nat.le_div_iff_mul_le (Nat.pos_of_mem_properDivisors hd')).mp
      (Nat.one_lt_div_of_mem_properDivisors hd')
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_properDivisors hd', by dsimp [m]; omega⟩
  have hcard : (negativeDivisors n).card ≤ m := by
    simpa using card_le_card hsub
  calc
    _ ≤ ∑ d ∈ negativeDivisors n, (1000 / 1221 : ℚ) ^ m := by
      refine sum_le_sum fun d hd => pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      have hd' := (mem_Icc.mp (hsub hd)).2
      dsimp [m] at *
      omega
    _ ≤ (m : ℚ) * (1000 / 1221 : ℚ) ^ m := by
      simpa using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℚ).mpr hcard)
        (show 0 ≤ (1000 / 1221 : ℚ) ^ m by positivity)
    _ ≤ 1 := by
      rw [show (1000 / 1221 : ℚ) = (1221 / 1000 : ℚ)⁻¹ by norm_num, inv_pow,
        ← div_eq_mul_inv, div_le_one (by positivity)]
      exact half_le_growth m (by dsimp [m]; omega)

/-- **Möbius transforms of sequences growing by a factor of at least $1.221$ are nonnegative.**
Let $b$ be a sequence of real numbers and $C \ge 1.221$ a real number such that $b(n) \ge 0$ and
$b(n+1) \ge C\, b(n)$ for every $n \ge 1$. Then for every $n \ge 1$, with $\mu$ the Möbius
function,
$$\sum_{d \mid n} \mu(n/d)\, b(d) \ge 0,$$
that is, the Dirichlet convolution $\mu * b$ is nonnegative at $n$.

Source: Geng-Rui Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024), Article 24.3.3, Lemma 28 (`jis-2024-24.3.3-lem-28`). -/
public theorem moebius_conv_nonneg_of_geometric_growth (b : ℕ → ℝ)
    (hb : ∀ n, 1 ≤ n → 0 ≤ b n) (C : ℝ) (hC : (1221 / 1000 : ℝ) ≤ C)
    (hgrowth : ∀ n, 1 ≤ n → C * b n ≤ b (n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) * b d := by
  have step (k : ℕ) (hk : 1 ≤ k) : b k ≤ (1000 / 1221 : ℝ) * b (k + 1) := by
    have := (mul_le_mul_of_nonneg_right hC (hb k hk)).trans (hgrowth k hk)
    linarith
  have bound (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : d ≤ k) :
      b d ≤ (1000 / 1221 : ℝ) ^ (k - d) * b k := by
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [show k + 1 - d = (k - d) + 1 by omega, pow_succ, mul_assoc]
      exact ih.trans (mul_le_mul_of_nonneg_left (step k (hd.trans hk)) (by positivity))
  have weights : ∑ d ∈ negativeDivisors n, (1000 / 1221 : ℝ) ^ (n - d) ≤ 1 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr (negative_weight_le_one n)
  have losses : ∑ d ∈ negativeDivisors n, b d ≤ b n := calc
    _ ≤ ∑ d ∈ negativeDivisors n, (1000 / 1221 : ℝ) ^ (n - d) * b n := by
      refine sum_le_sum fun d hd => ?_
      have hd' := (mem_filter.mp hd).1
      exact bound d (Nat.pos_of_mem_properDivisors hd') n (Nat.mem_properDivisors.mp hd').2.le
    _ ≤ b n := by
      rw [← sum_mul]
      simpa using mul_le_mul_of_nonneg_right weights (hb n hn)
  have lower : -(∑ d ∈ negativeDivisors n, b d) ≤
      ∑ d ∈ n.properDivisors, (μ (n / d) : ℝ) * b d := by
    rw [negativeDivisors, sum_filter, ← sum_neg_distrib]
    refine sum_le_sum fun d hd => ?_
    rcases ArithmeticFunction.moebius_eq_or (n / d) with h | h | h <;>
      simp [h, hb d (Nat.pos_of_mem_properDivisors hd)]
  rw [← Nat.cons_self_properDivisors (by omega : n ≠ 0), sum_cons,
    Nat.div_self (by omega), ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
  linarith

end MetaMathlibExt
