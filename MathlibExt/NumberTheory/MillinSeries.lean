/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Denominators of the Millin series

The Millin series is the unique expansion of $(5 - \sqrt 5)/2$ into unit fractions
whose positive integer denominators satisfy $a_n^2/a_{n+1} \le 2/3$.
-/

namespace MetaMathlibExt

namespace MillinSeries

open scoped goldenRatio

/-- The first denominator is the ceiling of the reciprocal of the sum. -/
private theorem ceil_inv_sum {a : ℕ → ℕ} {s : ℝ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) s) : ⌈s⁻¹⌉ = (a 0 : ℤ) := by
  have ha (n) : (1 : ℝ) ≤ a n := by exact_mod_cast hpos n
  have hp (n) : 0 < (a n : ℝ) := by exact_mod_cast hpos n
  have hd (n) : 0 < (a n : ℝ) - 2 / 3 := by linarith [ha n]
  -- The differences of b telescope and dominate the unit fractions term by term.
  let b (n : ℕ) : ℝ := 1 / ((a n : ℝ) - 2 / 3)
  have hstep (n) : 1 / (a n : ℝ) ≤ b n - b (n + 1) := by
    have hdiff : b n - 1 / (a n : ℝ) = (2 / 3) / ((a n : ℝ) * (a n - 2 / 3)) := by
      simp only [b, one_div, inv_sub_inv (hd n).ne' (hp n).ne', sub_sub_cancel,
        mul_comm ((a n : ℝ) - 2 / 3)]
    rw [le_sub_comm, hdiff]
    apply (div_le_div_iff₀ (hd _) (mul_pos (hp _) (hd _))).2
    nlinarith [(div_le_iff₀ (hp _)).1 (hratio n), ha n]
  have hupper : s ≤ b 0 := by
    apply le_of_tendsto hs.tendsto_sum_nat
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∑ i ∈ Finset.range n, (b i - b (i + 1)) := Finset.sum_le_sum fun i _ => hstep i
      _ = b 0 - b n := Finset.sum_range_sub' b n
      _ ≤ b 0 := sub_le_self _ (one_div_nonneg.mpr (hd n).le)
  have hlower : 1 / (a 0 : ℝ) ≤ s := le_hasSum hs 0 fun _ _ => by positivity
  have hspos := (one_div_pos.mpr (hp 0)).trans_le hlower
  apply Int.ceil_eq_iff.mpr
  simp only [Int.cast_natCast]
  rw [one_div] at hlower
  change s ≤ 1 / ((a 0 : ℝ) - 2 / 3) at hupper
  rw [one_div] at hupper
  exact ⟨by linarith [(le_inv_comm₀ hspos (hd 0)).1 hupper],
    (inv_le_comm₀ (hp 0) hspos).1 hlower⟩

private noncomputable def power (n : ℕ) : ℝ := φ ^ (2 ^ (n + 1) : ℕ)

private theorem one_lt_power (n : ℕ) : 1 < power n :=
  one_lt_pow₀ Real.one_lt_goldenRatio (by positivity)

private theorem fib_eq (n : ℕ) :
    (Nat.fib (2 ^ (n + 1)) : ℝ) = (power n - (power n)⁻¹) / √5 := by
  have he : Even (2 ^ (n + 1) : ℕ) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  rw [Real.coe_fib_eq, show ψ = -φ⁻¹ by rw [Real.inv_goldenRatio, neg_neg],
    he.neg_pow, inv_pow]
  rfl

/-- Closed form of the tail starting with the reciprocal of F_{2^{n+1}}. -/
private noncomputable def remainder (n : ℕ) : ℝ := √5 / (power n - 1)

private theorem remainder_zero : remainder 0 = (5 - √5) / 2 := by
  simp only [remainder, power, Nat.zero_add, pow_one, Real.goldenRatio_sq, add_sub_cancel_right]
  rw [Real.goldenRatio]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp
  nlinarith

private theorem ceil_inv_remainder (n : ℕ) :
    ⌈(remainder n)⁻¹⌉ = (Nat.fib (2 ^ (n + 1)) : ℤ) := by
  have hx := one_lt_power n
  have hi := inv_lt_one_of_one_lt₀ hx
  have hp : 0 < (power n)⁻¹ := inv_pos.mpr (by linarith)
  have hs : (1 : ℝ) < √5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
  rw [Int.ceil_eq_iff, Int.cast_natCast, fib_eq, remainder, inv_div]
  constructor
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity), add_mul,
      div_mul_cancel₀ _ (by positivity)]
    linarith
  · exact div_le_div_of_nonneg_right (by linarith) (by positivity)

private theorem remainder_succ (n : ℕ) :
    remainder (n + 1) = remainder n - 1 / (Nat.fib (2 ^ (n + 1)) : ℝ) := by
  have hx := one_lt_power n
  have hpow : power (n + 1) = power n ^ 2 := by
    unfold power
    rw [pow_succ (2 : ℕ) (n + 1), pow_mul]
  rw [remainder, remainder, hpow, fib_eq]
  have hne : power n ^ 2 - 1 ≠ 0 := by nlinarith
  have hpos : power n - (power n)⁻¹ ≠ 0 := by linarith [inv_lt_one_of_one_lt₀ hx]
  field_simp
  ring

end MillinSeries

open MillinSeries

/-- **Characterization of the denominators of the Millin series.** Let $(a_n)_{n \ge 0}$ be a
sequence of positive integers with $a_n^2 / a_{n+1} \le 2/3$ for all $n$ and
$\sum_n 1 / a_n = (5 - \sqrt 5) / 2$. Then $a_n = F_{2^{n+1}}$ for all $n \ge 0$, where $F_k$
is the $k$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$); that is, $a$ is the sequence
$F_2, F_4, F_8, \ldots$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 2 (`integers-2026-A28-cor-2`). -/
public theorem eq_fib_two_pow_of_ratio_le_of_hasSum_millin {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) ((5 - √5) / 2)) :
    ∀ n, a n = Nat.fib (2 ^ (n + 1)) := by
  have recover (n) (hs : HasSum (fun k => 1 / (a (k + n) : ℝ)) (remainder n)) :
      a n = Nat.fib (2 ^ (n + 1)) := by
    have h := ceil_inv_sum (a := fun k => a (k + n)) (fun k => hpos _) (fun k => by
      simpa only [Nat.succ_add] using hratio (k + n)) hs
    simpa only [Nat.zero_add, ceil_inv_remainder, Nat.cast_inj] using h.symm
  have htail (n) : HasSum (fun k => 1 / (a (k + n) : ℝ)) (remainder n) := by
    induction n with
    | zero => simpa only [Nat.add_zero, remainder_zero] using hsum
    | succ n ih =>
      have h := (hasSum_nat_add_iff' 1).2 ih
      simpa only [Finset.sum_range_one, Nat.zero_add, Nat.succ_add, Nat.add_succ, recover n ih,
        ← remainder_succ] using h
  exact fun n => recover n (htail n)

end MetaMathlibExt
