/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

namespace MetaMathlibExt

@[expose] public section

/-- **Generating function of the Bernoulli numbers of the second kind.** Let $G(t)$ be the
inverse, in the ring $\mathbb{Q}[[t]]$ of formal power series, of the series
$\sum_{n \ge 0} \frac{(-1)^n}{n + 1} t^n$, which is invertible because its constant
coefficient is $1$.

Analytically this series is $\log(1 + t) / t$, so $G(t) = t / \log(1 + t)$; the logarithm
itself is not invertible, having zero constant coefficient. -/
public noncomputable def bernoulliSecondPowerSeries : PowerSeries ℚ :=
  (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹

/-- **Bernoulli numbers of the second kind.** For a natural number $n$, the Bernoulli number of
the second kind $B_n^*$ is the rational number $n!$ times the coefficient of $t^n$ in
$G(t) \in \mathbb{Q}[[t]]$, the inverse of the formal power series
$\sum_{k \ge 0} \frac{(-1)^k}{k + 1} t^k$. Thus $G(t) = \sum_{n \ge 0} B_n^* t^n / n!$.

Analytically $G(t) = t / \log(1 + t)$; this is Roman's normalization, with $B_0^* = 1$,
$B_1^* = 1/2$ and $B_2^* = -1/6$. -/
public noncomputable def bernoulliSecond (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) bernoulliSecondPowerSeries

/-- **Generating function of the Bernoulli numbers of the second kind as an inverse.** The
generating function $G(t)$ of the Bernoulli numbers of the second kind equals the inverse, in
the ring $\mathbb{Q}[[t]]$ of formal power series, of the series
$\sum_{n \ge 0} \frac{(-1)^n}{n + 1} t^n$. -/
public theorem bernoulliSecondPowerSeries_eq :
    bernoulliSecondPowerSeries =
      (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1))⁻¹ :=
  rfl

/-- **Bernoulli numbers of the second kind as scaled coefficients.** For every natural number
$n$, the Bernoulli number of the second kind $B_n^*$ equals $n!$ times the coefficient of $t^n$
in the generating function $G(t) \in \mathbb{Q}[[t]]$ of the Bernoulli numbers of the second
kind. -/
public theorem bernoulliSecond_eq (n : ℕ) :
    bernoulliSecond n =
      (n.factorial : ℚ) * (PowerSeries.coeff n) bernoulliSecondPowerSeries :=
  rfl

/-- **Defining identity of the generating function of the Bernoulli numbers of the second
kind.** In the ring $\mathbb{Q}[[t]]$ of formal power series, the generating function $G(t)$ of
the Bernoulli numbers of the second kind satisfies
$G(t) \cdot \sum_{n \ge 0} \frac{(-1)^n}{n + 1} t^n = 1$.

Analytically, $\sum_{n \ge 0} \frac{(-1)^n}{n + 1} t^n = \log(1 + t) / t$. -/
public theorem bernoulliSecondPowerSeries_mul_mk :
    bernoulliSecondPowerSeries *
        (PowerSeries.mk fun n => (-1 : ℚ) ^ n / (n + 1)) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

/-- **Coefficient identity for the generating function of the Bernoulli numbers of the second
kind.** Let $g_i$ be the coefficient of $t^i$ in the generating function $G(t) \in \mathbb{Q}[[t]]$
of the Bernoulli numbers of the second kind. For every natural number $n$, the sum of
$g_i \cdot (-1)^j / (j + 1)$ over all pairs $(i, j)$ of natural numbers with $i + j = n$ equals
$1$ if $n = 0$ and $0$ if $n \ge 1$. -/
public theorem sum_antidiagonal_bernoulliSecondPowerSeries_coeff (n : ℕ) :
    (∑ x ∈ Finset.antidiagonal n,
      (PowerSeries.coeff x.1) bernoulliSecondPowerSeries *
        ((-1 : ℚ) ^ x.2 / (x.2 + 1))) = if n = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) bernoulliSecondPowerSeries_mul_mk
  rw [PowerSeries.coeff_mul] at h
  simpa [PowerSeries.coeff_mk, PowerSeries.coeff_one] using h

/-- **Recurrence for the Bernoulli numbers of the second kind.** For every natural number
$n \ge 1$, the Bernoulli numbers of the second kind $B_k^*$ satisfy
$B_n^* / n! = -\sum_{k=0}^{n-1} (B_k^* / k!) \cdot (-1)^{n-k} / (n - k + 1)$. -/
public theorem bernoulliSecond_div_factorial_eq (n : ℕ) (hn : 1 ≤ n) :
    bernoulliSecond n / (n.factorial : ℚ) =
      -∑ k ∈ Finset.range n, (bernoulliSecond k / (k.factorial : ℚ)) *
        ((-1 : ℚ) ^ (n - k) / (n - k + 1)) := by
  have h := sum_antidiagonal_bernoulliSecondPowerSeries_coeff n
  rw [if_neg (show n ≠ 0 by omega)] at h
  have hsplit : (∑ x ∈ Finset.antidiagonal n,
        (PowerSeries.coeff x.1) bernoulliSecondPowerSeries *
          ((-1 : ℚ) ^ x.2 / (x.2 + 1))) =
      (PowerSeries.coeff n) bernoulliSecondPowerSeries +
        ∑ k ∈ Finset.range n, (PowerSeries.coeff k) bernoulliSecondPowerSeries *
          ((-1 : ℚ) ^ (n - k) / (n - k + 1)) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b : ℕ => (PowerSeries.coeff a) bernoulliSecondPowerSeries *
        ((-1 : ℚ) ^ b / (b + 1))) n, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, Nat.cast_zero, zero_add, div_one,
      mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_sub (Finset.mem_range.mp hk).le]
  rw [hsplit] at h
  have hcoeff : ∀ k : ℕ, (PowerSeries.coeff k) bernoulliSecondPowerSeries =
      bernoulliSecond k / (k.factorial : ℚ) := fun k => by
    rw [bernoulliSecond_eq]
    field_simp
  rw [hcoeff n] at h
  rw [Finset.sum_congr rfl (fun k _ => by rw [hcoeff k])] at h
  linarith

end

end MetaMathlibExt
