/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum

/-!
# Abundancy after removing a prime factor

For a prime power exactly dividing a positive integer, Zelinsky bounds the change in
abundancy by cancelling the coprime cofactor and comparing consecutive prime powers.
-/

public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private theorem abundancyIndex_mul_of_coprime {m n : ℕ} (hc : m.Coprime n) :
    abundancyIndex (m * n) = abundancyIndex m * abundancyIndex n := by
  simp only [abundancyIndex, hc.sum_divisors_mul, Nat.cast_mul, mul_div_mul_comm]

/-- **Abundancy ratio at an exactly dividing prime power.** Let $n$ be a positive integer, $p$ a
prime and $a \ge 1$ an integer such that $p^a$ exactly divides $n$ (that is, $p^a \mid n$ and
$p^{a+1} \nmid n$). Then $h(n)/h(n/p) \le 1 + 1/p^a$, where $h(m) = \sigma(m)/m$ is the abundancy
index and $\sigma(m)$ is the sum of the positive divisors of $m$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `correctedPAlemma`). -/
theorem abundancyIndex_div_le
    (n p a : ℕ) (hn0 : 0 < n) (hp : p.Prime) (ha : 1 ≤ a)
    (hpa : n.factorization p = a) :
    abundancyIndex n / abundancyIndex (n / p) ≤
      1 + 1 / (p : ℚ) ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  let m := ordCompl[p] n
  have hm : 0 < m := Nat.ordCompl_pos p hn0.ne'
  have hc : p.Coprime m := Nat.coprime_ordCompl hp hn0.ne'
  have hn : n = p ^ (k + 1) * m := by
    rw [show k + 1 = n.factorization p from hpa.symm]
    exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hdiv : n / p = p ^ k * m := by
    rw [hn, pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hle := one_le_abundancyIndex (pow_pos hp.pos k)
  rw [hdiv, hn, abundancyIndex_mul_of_coprime (hc.pow_left _),
    abundancyIndex_mul_of_coprime (hc.pow_left _),
    mul_div_mul_right _ _ (zero_lt_one.trans_le (one_le_abundancyIndex hm)).ne',
    abundancyIndex_prime_pow_succ hp, add_div, div_self (zero_lt_one.trans_le hle).ne']
  exact add_le_add_right (div_le_self (by positivity) hle) _

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
