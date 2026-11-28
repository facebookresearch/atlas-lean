/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Prime reduction for summatory heights

For $H : \mathbb{N} \to \mathbb{N}$ completely additive on the positive integers there is a real
constant $C$ such that for every real $x \ge 2$ the sum of $H(m)$ over $1 \le m \le x$ differs from
its prime main term $x \sum_{p \le x} H(p)/(p - 1)$ by at most $C \log x \sum_{p \le x} H(p)$, where
both sums run over the primes $p \le x$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7, "In particular" display.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

private lemma sum_height_factorial {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    {n : ℕ} (hn : 2 ≤ n) :
    (∑ m ∈ Icc 1 n, (H m : ℝ)) =
      ∑ p ∈ (Iic n).filter Nat.Prime, (H p : ℝ) * n.factorial.factorization p := by
  classical
  rw [← Nat.cast_sum, sum_height_eq_sum_prime_powers hH hn, Nat.cast_sum]
  refine sum_congr rfl fun p hp => ?_
  have hprime := (mem_filter.mp hp).2
  have hcut : (Icc 1 n).filter (fun a => p ^ a ≤ n) = Icc 1 (Nat.log p n) := by
    ext a
    simp only [mem_filter, mem_Icc,
      ← Nat.le_log_iff_pow_le hprime.one_lt (by omega : n ≠ 0)]
    have := Nat.log_le_self p n
    omega
  rw [hcut, ← mul_sum, ← Ico_add_one_right_eq_Icc,
    ← Nat.factorization_factorial hprime (Nat.lt_add_one (Nat.log p n))]
  push_cast
  rfl

private lemma prime_factorial_error {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ x / ((p : ℝ) - 1) - ⌊x⌋₊.factorial.factorization p ∧
      x / ((p : ℝ) - 1) - ⌊x⌋₊.factorial.factorization p ≤
        (3 / Real.log 2) * Real.log x := by
  let n := ⌊x⌋₊
  have hn : 2 ≤ n := Nat.le_floor hx
  have hn₀ : n ≠ 0 := by omega
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : 0 < (p : ℝ) - 1 := by linarith
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) hp.one_le)
  have hid : ((p : ℝ) - 1) * n.factorial.factorization p +
      ((p.digits n).sum : ℝ) = n := by
    rw [← hcast, ← Nat.cast_mul, ← Nat.cast_add,
      Nat.sub_one_mul_factorization_factorial hp,
      Nat.sub_add_cancel (Nat.digit_sum_le p n)]
  have hdigits : (p.digits n).sum ≤ (Nat.log p n + 1) * (p - 1) := by
    have h := List.sum_le_length_nsmul (p.digits n) (p - 1) fun d hd =>
      Nat.le_sub_one_of_lt (Nat.digits_lt_base hp.one_lt hd)
    simpa [Nat.length_digits p n hp.one_lt hn₀, nsmul_eq_mul] using h
  have hdigits' : ((p.digits n).sum : ℝ) ≤
      ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
    rw [← hcast]
    exact_mod_cast hdigits
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith : 0 ≤ x)
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have herr : x / ((p : ℝ) - 1) - n.factorial.factorization p ≤
      (Nat.log p n : ℝ) + 2 := by
    apply (mul_le_mul_iff_left₀ hd).mp
    rw [sub_mul, div_mul_cancel₀ _ hd.ne']
    nlinarith only [hid, hdigits', hxn, hp₂]
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp₂
  have hpow : ((p : ℝ) ^ Nat.log p n) ≤ x := by
    calc
      _ ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self p hn₀
      _ ≤ x := hnx
  have hlog : (Nat.log p n : ℝ) * Real.log p ≤ Real.log x := by
    simpa only [Real.log_pow] using
      Real.log_le_log (by positivity : 0 < (p : ℝ) ^ Nat.log p n) hpow
  have hk : (Nat.log p n : ℝ) ≤ Real.log x / Real.log 2 := by
    apply (le_div_iff₀ hl₂).mpr
    exact (mul_le_mul_of_nonneg_left hlp (Nat.cast_nonneg _)).trans hlog
  refine ⟨?_, herr.trans ?_⟩
  · rw [sub_nonneg, le_div_iff₀ hd]
    nlinarith only [hid, hnx, (Nat.cast_nonneg (p.digits n).sum : (0 : ℝ) ≤ _)]
  · apply (mul_le_mul_iff_left₀ hl₂).mp
    have hc : (3 / Real.log 2 * Real.log x) * Real.log 2 = 3 * Real.log x := by
      field_simp
    rw [hc]
    nlinarith only [(le_div_iff₀ hl₂).mp hk, hlx]


/-- **Prime reduction for summatory heights.** Let $H : \mathbb{N} \to \mathbb{N}$ be completely
additive on the positive integers, and for real $x$ let $F(x) = \sum_{1 \le m \le x} H(m)$. Then
there is a real constant $C$ such that for every real $x \ge 2$,
$$\Bigl| F(x) - x \sum_{p \le x} \frac{H(p)}{p - 1} \Bigr| \le C \log x \sum_{p \le x} H(p),$$
where both sums run over the primes $p \le x$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), "In particular" display. -/
public theorem sum_height_asymptotic {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (H m : ℝ)) -
          x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ) / ((p : ℝ) - 1)| ≤
        C * Real.log x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ)
    := by
  classical
  refine ⟨3 / Real.log 2, fun x hx => ?_⟩
  rw [sum_height_factorial hH (Nat.le_floor hx), mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime,
          |(H p : ℝ) * ⌊x⌋₊.factorial.factorization p -
            x * ((H p : ℝ) / ((p : ℝ) - 1))| := abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime,
        (H p : ℝ) * (x / ((p : ℝ) - 1) - ⌊x⌋₊.factorial.factorization p) := by
      refine sum_congr rfl fun p hp => ?_
      have h := prime_factorial_error (mem_filter.mp hp).2 hx
      have heq : x * ((H p : ℝ) / ((p : ℝ) - 1)) =
          (H p : ℝ) * (x / ((p : ℝ) - 1)) := by ring
      rw [heq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_sub_comm, abs_of_nonneg h.1]
    _ ≤ ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime,
        (H p : ℝ) * ((3 / Real.log 2) * Real.log x) := by
      refine sum_le_sum fun p hp => ?_
      exact mul_le_mul_of_nonneg_left
        (prime_factorial_error (mem_filter.mp hp).2 hx).2 (Nat.cast_nonneg _)
    _ = (3 / Real.log 2) * Real.log x *
        ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => mul_comm _ _

end

end MetaMathlibExt
