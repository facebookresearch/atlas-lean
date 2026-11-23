/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.SeriesDivisorProduct

/-!
# Coefficient recursion for powers of a power series

If `s` is a series-divisor of `A`, then the coefficients of `A ^ m` satisfy the
recurrence with series-divisor `m * s`.
-/

open PowerSeries

namespace MetaMathlibExt

/-- **Coefficient recursion for powers of a power series.** Let $R$ be a commutative ring, let
$A$ be a formal power series over $R$ with coefficients $a(k)$, and let $s : \mathbb{N} \to R$
satisfy $k\,a(k) = \sum_{i=1}^{k} s(i)\,a(k-i)$ for every $k \ge 0$ (that is, $s$ is a
series-divisor of $A$). For natural numbers $m$ and $k$, write $a_m(k)$ for the coefficient of
$q^k$ in $A^m$. Then for all natural numbers $m$ and $n$,
$n\,a_m(n) = m \sum_{j=1}^{n} s(j)\,a_m(n-j)$.

Source: in Corollary 4 the printed summand `σ^A(i)` is read as `σ^A(j)` (the summation index).

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Corollary 4
(`jis-2024-24.1.6-cor-4`). -/
public theorem series_divisor_pow_recursion {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (m n : ℕ) :
    (n : R) * coeff n (A ^ m) = (m : R) * ∑ j ∈ Finset.Icc 1 n, s j * coeff (n - j) (A ^ m) := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  induction m generalizing n with
  | zero => cases n <;> simp [coeff_one]
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_succ, add_one_mul] using
      series_divisor_add_of_mul (A ^ m) A (fun i ↦ (m : R) * s i) s ih hA n

end MetaMathlibExt
