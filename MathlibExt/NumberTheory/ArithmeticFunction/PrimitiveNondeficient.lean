/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Primitive non-deficient numbers

This file defines primitive non-deficient numbers and their abundancy quantities, and proves
Zelinsky's reciprocal estimate used to bound prime-power components.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

/-- **Non-deficient number.** A natural number $n$ is non-deficient when $n \ne 0$ and
$\sigma(n) \ge 2n$, where $\sigma(n)$ is the sum of the positive divisors of $n$.

Positivity is part of the notion: $0$ has no divisors in this convention, so the inequality
alone would make $0$ non-deficient. -/
def IsNondeficient (n : ℕ) : Prop :=
  n ≠ 0 ∧ 2 * n ≤ ∑ d ∈ Nat.divisors n, d

/-- **Primitive non-deficient number.** A natural number $n$ is primitive non-deficient when it
is non-deficient and every proper divisor $m$ of $n$ (a divisor with $m < n$) is deficient, that
is, $\sigma(m) < 2m$, where $\sigma(m)$ is the sum of the positive divisors of $m$. -/
def IsPrimitiveNondeficient (n : ℕ) : Prop :=
  IsNondeficient n ∧
    ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m

/-- **Abundancy index.** For a natural number $n$, the abundancy index is the rational number
$h(n) = \sigma(n)/n$, where $\sigma(n)$ is the sum of the positive divisors of $n$.

At $n = 0$ this gives $h(0) = 0$, since division by zero is $0$ in $\mathbb{Q}$; the abundancy
index is only meaningful for positive $n$. -/
noncomputable def abundancyIndex (n : ℕ) : ℚ :=
  ((∑ d ∈ Nat.divisors n, d : ℕ) : ℚ) / (n : ℚ)

/-- The abundancy index is the sum of the positive divisors divided by the number, in `ℚ`. -/
lemma abundancyIndex_eq_sum_divisors_div (n : ℕ) :
    abundancyIndex n = ((∑ d ∈ Nat.divisors n, d : ℕ) : ℚ) / (n : ℚ) := rfl

/-- The abundancy index of `1` is `1`. -/
private theorem abundancyIndex_one : abundancyIndex 1 = 1 := by
  simp [abundancyIndex, Nat.divisors_one]

/-- The abundancy index is multiplicative on coprime pairs. -/
private theorem abundancyIndex_mul_of_coprime {m n : ℕ} (hc : m.Coprime n) :
    abundancyIndex (m * n) = abundancyIndex m * abundancyIndex n := by
  simp only [abundancyIndex, hc.sum_divisors_mul, Nat.cast_mul, mul_div_mul_comm]

/-- The abundancy index of a product of pairwise coprime factors is the product of their indices. -/
lemma abundancyIndex_prod (s : Finset ℕ) (f : ℕ → ℕ)
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → (f p).Coprime (f q)) :
    abundancyIndex (∏ p ∈ s, f p) = ∏ p ∈ s, abundancyIndex (f p) := by
  revert hcop
  induction s using Finset.induction with
  | empty => intro _; simp [abundancyIndex_one]
  | insert a t ha ih =>
    intro hcop
    rw [Finset.prod_insert ha, Finset.prod_insert ha, abundancyIndex_mul_of_coprime]
    · congr 1
      apply ih
      intro p hp q hq hpq
      exact hcop p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
    · rw [← Nat.isCoprime_iff_coprime, Nat.cast_prod]
      apply IsCoprime.prod_right
      intro q hq
      rw [Nat.isCoprime_iff_coprime]
      exact hcop a (Finset.mem_insert_self a t) q (Finset.mem_insert_of_mem hq)
        (fun heq => ha (heq ▸ hq))

/-- For a prime `p`, the abundancy index of `p ^ a` is `p / (p - 1)` times `1 - 1 / p ^ (a + 1)`,
with the divisions taken in `ℚ`. -/
lemma abundancyIndex_prime_pow_eq (p a : ℕ) (hp : p.Prime) :
    abundancyIndex (p ^ a)
      = (p : ℚ) / ((p : ℚ) - 1) * (1 - 1 / (p : ℚ) ^ (a + 1)) := by
  have hgeom : ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ) * ((p : ℚ) - 1)
      = (p : ℚ) ^ (a + 1) - 1 := by
    have hcast : ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ)
        = ∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.cast_pow p i
    rw [hcast]
    exact geom_sum_mul _ _
  have hsig : (ArithmeticFunction.sigma 1) (p ^ a)
      = ∑ i ∈ Finset.range (a + 1), p ^ i :=
    ArithmeticFunction.sigma_one_apply_prime_pow hp
  have hdiv : abundancyIndex (p ^ a)
      = ((∑ i ∈ Finset.range (a + 1), p ^ i : ℕ) : ℚ) / (p : ℚ) ^ a := by
    simp only [abundancyIndex, ← ArithmeticFunction.sigma_one_apply, hsig, Nat.cast_pow]
  rw [hdiv]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
    linarith
  have hpa : (p : ℚ) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpa1 : (p : ℚ) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
  have hps : (p : ℚ) ^ (a + 1) = (p : ℚ) * (p : ℚ) ^ a := pow_succ' _ _
  field_simp
  linear_combination (p : ℚ) ^ (a + 1) * hgeom + ((p : ℚ) ^ (a + 1) - 1) * hps

/-- The abundancy index of a positive natural number is at least one. -/
lemma one_le_abundancyIndex {n : ℕ} (hn : 0 < n) : 1 ≤ abundancyIndex n := by
  rw [abundancyIndex, one_le_div (by exact_mod_cast hn)]
  exact_mod_cast Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

/-- For prime `p`, the abundancy of `p ^ (k + 1)` exceeds that of `p ^ k` by `1 / p ^ (k + 1)`. -/
lemma abundancyIndex_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    abundancyIndex (p ^ (k + 1)) = abundancyIndex (p ^ k) + 1 / (p : ℚ) ^ (k + 1) := by
  simp only [abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp, Nat.cast_pow]
  rw [geom_sum_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_div, pow_succ']
  rw [mul_div_mul_left _ _ (by exact_mod_cast hp.ne_zero : (p : ℚ) ≠ 0)]

/-- **Product of $p/(p-1)$ over the prime factors.** For a natural number $n$, let
$H(n) = \prod_p p/(p-1)$ in $\mathbb{Q}$, the product over the distinct primes $p$ dividing $n$.
For $n = 0$ the product is empty ($0$ is taken to have no prime factors), so $H(0) = 1$. -/
noncomputable def abundancySup (n : ℕ) : ℚ :=
  ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)

/-- **Zelinsky's reciprocal bound.** For real numbers $k$ and $m$ with $k \ge 2$ and
$0 < m < 1/(k(k+1))$, we have $1/(1 - km) < 1 + (k+1)m$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma (label `KMlemma`). -/
theorem one_div_one_sub_mul_lt_add
    (k m : ℝ) (hk : 2 ≤ k) (hm0 : 0 < m)
    (hm : m < 1 / (k * (k + 1))) :
    1 / (1 - k * m) < 1 + (k + 1) * m := by
  have hk0 : 0 < k := by linarith
  have hbound : m * (k * (k + 1)) < 1 :=
    (lt_div_iff₀ (mul_pos hk0 (by linarith))).mp hm
  have hkm : k * m < 1 := by
    linarith only [hbound, mul_nonneg (sq_nonneg k) hm0.le]
  apply (div_lt_iff₀ (sub_pos.mpr hkm)).2
  linarith only [mul_pos hm0 (sub_pos.mpr hbound)]

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
