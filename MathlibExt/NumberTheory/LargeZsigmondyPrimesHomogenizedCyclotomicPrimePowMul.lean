/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic
import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomicPrimeMul

/-!
# Homogenized cyclotomic values at prime-power multiples

For a prime `p`, `β ≥ 1` and `k ≥ 1` with `p ∤ k`, the value at index `p ^ β * k` equals the
value at index `p * k` with both arguments raised to `p ^ (β - 1)`, and the product of that
value with the value at index `k` of the raised arguments equals the value at index `k` with
both arguments raised to `p ^ β`
(`MetaMathlibExt.homogenizedCyclotomic_prime_pow_mul`).

Statements from Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62.
-/

namespace MetaMathlibExt

private theorem homogenizedCyclotomic_prime_pow_mul_aux {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (a b : ℤ) (γ : ℕ) :
    homogenizedCyclotomic (p ^ (γ + 1) * k) a b =
      homogenizedCyclotomic (p * k) (a ^ p ^ γ) (b ^ p ^ γ) := by
  induction γ generalizing a b with
  | zero => simp
  | succ γ ih =>
    have hpos : 0 < p ^ (γ + 1) * k := Nat.mul_pos (pow_pos hp.pos _) hk
    have hdvd : p ∣ p ^ (γ + 1) * k :=
      dvd_mul_of_dvd_left (⟨p ^ γ, pow_succ' p γ⟩ : p ∣ p ^ (γ + 1)) k
    have hstep := (homogenizedCyclotomic_prime_mul hp hpos a b).1 hdvd
    have hexp : p ^ (γ + 1 + 1) * k = p * (p ^ (γ + 1) * k) := by
      rw [pow_succ', mul_assoc]
    have e1 : ((a ^ p) ^ p ^ γ : ℤ) = a ^ p ^ (γ + 1) := by
      rw [← pow_mul, pow_succ']
    have e2 : ((b ^ p) ^ p ^ γ : ℤ) = b ^ p ^ (γ + 1) := by
      rw [← pow_mul, pow_succ']
    rw [hexp, hstep, ih, e1, e2]

/-- **Homogenized cyclotomic values at $p^\beta k$.** Let $p$ be a prime, let $\beta \ge 1$ and
$k \ge 1$ be integers with $p \nmid k$, and let $a, b$ be integers; write $\Phi_m(a, b)$ for the
homogenized cyclotomic value. Then
$\Phi_{p^\beta k}(a, b) = \Phi_{pk}(a^{p^{\beta - 1}}, b^{p^{\beta - 1}})$ and
$\Phi_{p^\beta k}(a, b) \cdot \Phi_k(a^{p^{\beta - 1}}, b^{p^{\beta - 1}}) =
\Phi_k(a^{p^\beta}, b^{p^\beta})$.

The paper states the second identity as a quotient; here it is cleared of its denominator.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Corollary 1. -/
public theorem homogenizedCyclotomic_prime_pow_mul {p β k : ℕ} (hp : p.Prime) (hβ : 0 < β)
    (hk : 0 < k) (hpk : ¬ p ∣ k) (a b : ℤ) :
    homogenizedCyclotomic (p ^ β * k) a b =
        homogenizedCyclotomic (p * k) (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) ∧
      homogenizedCyclotomic (p ^ β * k) a b *
          homogenizedCyclotomic k (a ^ p ^ (β - 1)) (b ^ p ^ (β - 1)) =
        homogenizedCyclotomic k (a ^ p ^ β) (b ^ p ^ β) := by
  obtain ⟨γ, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hβ)
  rw [Nat.add_sub_cancel]
  refine ⟨homogenizedCyclotomic_prime_pow_mul_aux hp hk a b γ, ?_⟩
  have hbase :=
    (homogenizedCyclotomic_prime_mul hp hk (a ^ p ^ γ) (b ^ p ^ γ)).2 hpk
  have e1 : ((a ^ p ^ γ) ^ p : ℤ) = a ^ p ^ (γ + 1) := by
    rw [← pow_mul, pow_succ]
  have e2 : ((b ^ p ^ γ) ^ p : ℤ) = b ^ p ^ (γ + 1) := by
    rw [← pow_mul, pow_succ]
  rw [homogenizedCyclotomic_prime_pow_mul_aux hp hk a b γ, hbase, e1, e2]

end MetaMathlibExt
