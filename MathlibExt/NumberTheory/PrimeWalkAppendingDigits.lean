/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.LSeries.WeakPNT

/-!
# Infinite prime walks by appending decimal digits

The half-open interval `[10 ^ n * p, 10 ^ n * (p + 1))` consists of the numbers obtained
by appending exactly `n` decimal digits to a positive integer `p`. We find a prime strictly
inside this interval for sufficiently large `n` using Mathlib's prime-gap consequence of the
prime number theorem. Iterating this step gives the walk.

## References

* Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan Wattanawanichkul,
  *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024), Article A78,
  pp. 1–29, Theorem 2.3 (p. 12). We use the paper's interval construction, but use the prime
  number theorem rather than its short-interval estimate to find a prime.
-/

namespace MetaMathlibExt

open Filter

private theorem exists_prime_append_decimal_digits {p : ℕ} (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ k < 10 ^ n ∧ q = 10 ^ n * p + k := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : Tendsto (fun n : ℕ => (10 : ℝ) ^ n * p) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)).atTop_mul_const hpR
  obtain ⟨n, hn, q, hq, hlo, hhi⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and
      (ht.eventually (Nat.eventually_exists_prime_mem_Ioc (one_div_pos.mpr hpR)))).exists
  have hlo' : 10 ^ n * p < q := by exact_mod_cast hlo
  have hbound : (1 + 1 / (p : ℝ)) * (10 ^ n * p) = (10 : ℝ) ^ n * (p + 1) := by
    rw [mul_comm (1 + 1 / (p : ℝ)), mul_assoc, mul_add, mul_one, mul_one_div_cancel hpR.ne']
  have hhi' : q ≤ 10 ^ n * (p + 1) := by
    change (q : ℝ) ≤ (1 + 1 / (p : ℝ)) * (10 ^ n * p) at hhi
    rw [hbound] at hhi
    exact_mod_cast hhi
  have hlt : q < 10 ^ n * (p + 1) := by
    refine lt_of_le_of_ne hhi' fun heq => ?_
    have hpow : 1 < (10 : ℕ) ^ n := one_lt_pow₀ (by decide) hn.ne'
    exact Nat.not_prime_mul hpow.ne' (Nat.succ_lt_succ hp.pos).ne' (heq ▸ hq)
  refine ⟨q, hq, n, q - 10 ^ n * p, hn, Nat.sub_pos_of_lt hlo', ?_, ?_⟩
  · rw [Nat.mul_succ] at hlt
    omega
  · exact (Nat.add_sub_of_le hlo'.le).symm

/-- **Walking to infinity on primes by appending decimal digits.** For every prime $p_0$ there is
a sequence of primes $p_0, p_1, p_2, \ldots$ starting at $p_0$ such that for every $i \ge 1$ there
are integers $n_i \ge 1$ and $k_i$ with $0 < k_i < 10^{n_i}$ and $p_i = 10^{n_i} p_{i-1} + k_i$;
that is, each term is obtained from the previous one by appending $n_i$ decimal digits on the
right.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Theorem 2.3. -/
public theorem exists_prime_walk_appending_decimal_digits (p₀ : ℕ) (hp₀ : p₀.Prime) :
    ∃ p : ℕ → ℕ, p 0 = p₀ ∧ (∀ i, (p i).Prime) ∧
      ∀ i, ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ k < 10 ^ n ∧ p (i + 1) = 10 ^ n * p i + k := by
  have step (p : {p : ℕ // p.Prime}) :
      ∃ q : {q : ℕ // q.Prime}, ∃ n k : ℕ,
        0 < n ∧ 0 < k ∧ k < 10 ^ n ∧ q.val = 10 ^ n * p.val + k := by
    obtain ⟨q, hq, n, k, hn, hk, hk', heq⟩ := exists_prime_append_decimal_digits p.property
    exact ⟨⟨q, hq⟩, n, k, hn, hk, hk', heq⟩
  choose next hnext using step
  let walk : ℕ → {p : ℕ // p.Prime} := Nat.rec ⟨p₀, hp₀⟩ fun _ p => next p
  exact ⟨fun i => (walk i).val, rfl, fun i => (walk i).property, fun i => hnext (walk i)⟩

end MetaMathlibExt
