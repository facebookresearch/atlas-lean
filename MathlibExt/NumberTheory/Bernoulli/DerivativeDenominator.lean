/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.BernoulliPolynomials
public import MathlibExt.Algebra.Polynomial.CoefficientDenominator
import Mathlib.Algebra.BigOperators.Associated

/-!
# Denominators of Bernoulli polynomials

For positive `n`, the large-prime part of the denominator of `Bₙ(X) - Bₙ` divides its coprime part.
A prime divides the coprime part precisely when it does not divide `n` and the base-prime digit
sum of `n` is at least the prime. The module also defines the indices `n ≥ 1` for which the
`k`-th derivative of a Bernoulli polynomial has integer coefficients.

## References

* Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
  Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, pp. 1–11,
  Sections 1–3, in particular equation (13) for the coprime part.
* Bernd C. Kellner and Jonathan Sondow, *On Carmichael and polygonal numbers, Bernoulli
  polynomials, and sums of base-p digits*, INTEGERS 21 (2021), Article A52, pp. 1–21,
  Section 3, for the decomposition into prime products.
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial Filter Asymptotics

/-- **The Bernoulli polynomial $B_0(x)$ has denominator one.** The Bernoulli polynomial
$B_0(x) = 1$ has denominator $\operatorname{denom}(B_0(x)) = 1$. In the source's notation
$\mathfrak{D}_n = \operatorname{denom}(B_n(x))$, this is the convention $\mathfrak{D}_0 = 1$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, after
Theorem 7. -/
theorem polynomialDenominator_bernoulli_zero :
    polynomialDenominator (Polynomial.bernoulli 0) = 1 := by
  rw [polynomialDenominator_eq_one_iff, Polynomial.bernoulli_zero]
  intro i
  rw [Polynomial.coeff_one]
  split_ifs <;> rfl

/-- **Denominator of $B_n(x) - B_n$.** For a natural number $n$ and a prime $p$, let $s_p(n)$ be
the sum of the base-$p$ digits of $n$. Define
$\mathbb{D}_n = \prod_{p \text{ prime},\ s_p(n) \ge p} p$, the product of all primes $p$ with
$s_p(n) \ge p$; every such prime satisfies $p \le n$, so the product is finite.

By a theorem of Kellner (2017, Section 5), for $n \ge 1$ the number $\mathbb{D}_n$ is the
denominator of $B_n(x) - B_n$, where $B_n(x)$ is the $n$-th Bernoulli polynomial and $B_n$ the
$n$-th Bernoulli number.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.3) (`eq:ddprod`); OEIS A195441. -/
def bernoulliDiffDenominator (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ≤ (Nat.digits p n).sum), p

/-- **First values of $\mathbb{D}_n$.** For a natural number $n$ let $\mathbb{D}_n$ be the product
of the primes $p$ whose base-$p$ digit sum $s_p(n)$ satisfies $s_p(n) \ge p$. Then
$(\mathbb{D}_1, \mathbb{D}_2, \dots, \mathbb{D}_{10}) = (1, 1, 2, 1, 6, 2, 6, 3, 10, 2)$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2 (displayed
values of `𝔻_n`). -/
theorem bernoulliDiffDenominator_small :
    [bernoulliDiffDenominator 1, bernoulliDiffDenominator 2, bernoulliDiffDenominator 3,
      bernoulliDiffDenominator 4, bernoulliDiffDenominator 5, bernoulliDiffDenominator 6,
      bernoulliDiffDenominator 7, bernoulliDiffDenominator 8, bernoulliDiffDenominator 9,
      bernoulliDiffDenominator 10] = [1, 1, 2, 1, 6, 2, 6, 3, 10, 2] := by
  decide +kernel

/-- **Kellner's product $\mathbb{D}^\perp_n$ over primes not dividing $n$.** For
$n \in \mathbb{N}$, write $s_p(n)$ for the sum of the base-$p$ digits of $n$. The number
$\mathbb{D}^\perp_n$ is the product of all primes $p$ with $p \nmid n$ and $s_p(n) \ge p$; every
such prime satisfies $p \le n$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.8) (`eq:ddprod2`); OEIS A324370. -/
def bernoulliDiffDenominatorCoprimePart (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ ¬ p ∣ n ∧ p ≤ (Nat.digits p n).sum), p

/-- **Prime divisors of the coprime part.** Let $n \in \mathbb{N}$, let $p$ be a prime, and
write $s_p(n)$ for the base-$p$ digit sum of $n$. For the coprime part $\mathbb{D}^{\perp}_n$
of the denominator of $B_n(x)-B_n$, we have $p \mid \mathbb{D}^{\perp}_n$ if and only if
$p \nmid n$ and $s_p(n) \ge p$. -/
theorem prime_dvd_bernoulliDiffDenominatorCoprimePart_iff {p n : ℕ} (hp : p.Prime) :
    p ∣ bernoulliDiffDenominatorCoprimePart n ↔ ¬ p ∣ n ∧ p ≤ (p.digits n).sum := by
  rw [bernoulliDiffDenominatorCoprimePart, hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨-, hprime, hndvd, hsum⟩ := Finset.mem_filter.mp hq
    rw [Nat.prime_dvd_prime_iff_eq hp hprime |>.mp hpq]
    exact ⟨hndvd, hsum⟩
  · rintro ⟨hndvd, hsum⟩
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range_succ_iff.mpr ?_, hp, hndvd, hsum⟩, dvd_rfl⟩
    exact hsum.trans (Nat.digit_sum_le p n)

/-- **Small values of $\mathbb{D}^\perp_n$.** Write $s_p(n)$ for the sum of the base-$p$ digits
of $n$, and let $\mathbb{D}^\perp_n$ be the product of the primes $p$ with $p \nmid n$ and
$s_p(n) \ge p$. Then $\mathbb{D}^\perp_1 = 1$, $\mathbb{D}^\perp_2 = 1$,
$\mathbb{D}^\perp_3 = 2$, $\mathbb{D}^\perp_5 = 6$ and $\mathbb{D}^\perp_9 = 10$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 2, equation
(2.8). -/
theorem bernoulliDiffDenominatorCoprimePart_small :
    [bernoulliDiffDenominatorCoprimePart 1, bernoulliDiffDenominatorCoprimePart 2,
      bernoulliDiffDenominatorCoprimePart 3, bernoulliDiffDenominatorCoprimePart 5,
      bernoulliDiffDenominatorCoprimePart 9] = [1, 1, 2, 6, 10] := by
  decide +kernel

/-- **Kellner's product $\mathbb{D}^+_n$ over primes above $\sqrt{n}$.** For $n \in \mathbb{N}$,
write $s_p(n)$ for the sum of the base-$p$ digits of $n$. The number $\mathbb{D}^+_n$ is the
product of all primes $p$ with $p > \sqrt{n}$ (that is, $p^2 > n$) and $s_p(n) \ge p$; every
such prime satisfies $p \le n$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1, equation
(1.4) (`eq:ddp`). -/
def bernoulliDiffDenominatorLargePart (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ n < p ^ 2 ∧ p ≤ (Nat.digits p n).sum), p

/-- **Small values of $\mathbb{D}^+_n$.** Write $s_p(n)$ for the sum of the base-$p$ digits of
$n$, and let $\mathbb{D}^+_n$ be the product of the primes $p$ with $p^2 > n$ and
$s_p(n) \ge p$. Then $\mathbb{D}^+_4 = 1$, $\mathbb{D}^+_5 = 3$ and $\mathbb{D}^+_9 = 5$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1, equation
(1.4). -/
theorem bernoulliDiffDenominatorLargePart_small :
    [bernoulliDiffDenominatorLargePart 4, bernoulliDiffDenominatorLargePart 5,
      bernoulliDiffDenominatorLargePart 9] = [1, 3, 5] := by
  decide +kernel

/-- **The large-prime part divides the coprime part.** Write $s_p(n)$ for the sum of the base-$p$
digits of $n$, let $\mathbb{D}^+_n$ be the product of the primes $p$ with $p^2 > n$ and
$s_p(n) \ge p$, and let $\mathbb{D}^\perp_n$ be the product of the primes $p$ with $p \nmid n$
and $s_p(n) \ge p$. Then $\mathbb{D}^+_n$ divides $\mathbb{D}^\perp_n$ for every $n \ge 1$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 17
(`jis-2024-24.2.8-lem-17`). -/
theorem bernoulliDiffDenominatorLargePart_dvd_coprimePart (n : ℕ) (hn : 1 ≤ n) :
    bernoulliDiffDenominatorLargePart n ∣ bernoulliDiffDenominatorCoprimePart n := by
  apply Finset.prod_dvd_prod_of_subset
  apply Finset.monotone_filter_right
  intro p _ ⟨hp, hsquare, hsum⟩
  refine ⟨hp, ?_, hsum⟩
  rintro ⟨k, rfl⟩
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  have hkp : k < p := Nat.lt_of_mul_lt_mul_left (by simpa only [pow_two] using hsquare)
  rw [Nat.digits_base_mul hp.one_lt hk, Nat.digits_of_lt p k hk.ne' hkp] at hsum
  exact hkp.not_ge (by simpa using hsum)

/-- **Indices of Bernoulli polynomials with integral $k$-th derivative.** For $k \in \mathbb{N}$,
$\overline{\mathcal{S}}_k$ is the set of $n \ge 1$ such that the $k$-th derivative $B_n^{(k)}(x)$
of the Bernoulli polynomial $B_n(x)$ has only integer coefficients, that is, has denominator
equal to $1$. We write $\overline{\mathcal{S}}$ for $\overline{\mathcal{S}}_1$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1
(`\overline{𝒮}`) and Section 3 (`\overline{𝒮}_k`). -/
def bernoulliIntegralDerivativeIndices (k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ polynomialDenominator (derivative^[k] (Polynomial.bernoulli n)) = 1}

/-- **Coefficient criterion for integral Bernoulli derivatives.** For $k,n\in\mathbb{N}$,
$n \in \overline{\mathcal{S}}_k$ if and only if $n \ge 1$ and every coefficient
$[x^i]B_n^{(k)}(x)$, for $i \in \mathbb{N}$, has denominator $1$. -/
theorem mem_bernoulliIntegralDerivativeIndices_iff {k n : ℕ} :
    n ∈ bernoulliIntegralDerivativeIndices k ↔
      1 ≤ n ∧ ∀ i, ((derivative^[k] (Polynomial.bernoulli n)).coeff i).den = 1 := by
  simp only [bernoulliIntegralDerivativeIndices, Set.mem_ofPred_eq,
    polynomialDenominator_eq_one_iff]

/-- **The derivative of $B_1(x)$ has integer coefficients.** The Bernoulli polynomial
$B_1(x) = x - \tfrac{1}{2}$ has derivative $B_1'(x) = 1 \in \mathbb{Z}[x]$, so $1$ belongs to
the set $\overline{\mathcal{S}}$ of indices $n \ge 1$ for which $B_n'(x)$ has only integer
coefficients.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Section 1 (`1 ∈ 𝒮`).
-/
theorem one_mem_bernoulliIntegralDerivativeIndices_one :
    1 ∈ bernoulliIntegralDerivativeIndices 1 := by
  refine ⟨le_rfl, ?_⟩
  rw [polynomialDenominator_eq_one_iff]
  intro i
  simp only [Function.iterate_one, Polynomial.bernoulli_one, derivative_sub, derivative_X,
    derivative_C, sub_zero, Polynomial.coeff_one]
  split_ifs <;> rfl

private theorem natCast_mul_den_eq_one_iff (q : ℚ) (n : ℕ) :
    ((n : ℚ) * q).den = 1 ↔ q.den ∣ n := by
  have h := Rat.den_mul_den_eq_den_mul_gcd (n : ℚ) q
  simp only [Rat.den_natCast, one_mul, Rat.num_natCast, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.gcd_comm (n * _) _, q.reduced.gcd_mul_right_cancel_right] at h
  constructor
  · intro h₁
    rw [h₁, one_mul] at h
    exact (dvd_of_eq h).trans (Nat.gcd_dvd_right _ _)
  · intro hd
    rw [Nat.gcd_eq_left hd] at h
    exact Nat.eq_of_mul_eq_mul_right q.den_pos (by simpa using h.symm)

/-- **Integral derivative criterion via the predecessor's denominator.** For every
$m \in \mathbb{N}$, the derivative $B_{m+1}'(x)$ of the Bernoulli polynomial $B_{m+1}(x)$ has only
integer coefficients, that is, $m + 1 \in \overline{\mathcal{S}}$, if and only if the denominator
of $B_m(x)$ divides $m + 1$. This follows from $B_{m+1}'(x) = (m + 1) B_m(x)$. -/
theorem succ_mem_bernoulliIntegralDerivativeIndices_one_iff (m : ℕ) :
    m + 1 ∈ bernoulliIntegralDerivativeIndices 1 ↔
      polynomialDenominator (Polynomial.bernoulli m) ∣ m + 1 := by
  simp only [bernoulliIntegralDerivativeIndices, Set.mem_ofPred_eq, Nat.le_add_left,
    true_and, Function.iterate_one, polynomialDenominator_eq_one_iff,
    derivative_bernoulli_add_one, ← Nat.cast_add_one, coeff_natCast_mul,
    natCast_mul_den_eq_one_iff]
  constructor
  · exact fun h => Finset.lcm_dvd fun i _ => h i
  · exact fun h i => (coeff_den_dvd_polynomialDenominator _ i).trans h

/-- **Kellner's large-part conjecture.** For a natural number $n$, let $\mathbb{D}^+_n$ be the
product of the primes $p > \sqrt{n}$ with $s_p(n) \ge p$, where $s_p(n)$ is the sum of the
base-$p$ digits of $n$. This definition is the proposition that $\mathbb{D}^+_n > 1$ for every
natural number $n > 192$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Conjecture 2 (i),
quoting Kellner (2017), Conjectures 1, 2. -/
def KellnerLargePartConjecture : Prop :=
  ∀ n : ℕ, 192 < n → 1 < bernoulliDiffDenominatorLargePart n

/-- **Kellner's asymptotic conjecture on large prime factors.** For $n \in \mathbb{N}$ let
$\mathbb{D}^{+}_n$ be the product of the primes $p > \sqrt{n}$ whose base-$p$ digit sum $s_p(n)$
satisfies $s_p(n) \ge p$, and let $\omega(m)$ be the number of distinct prime factors of $m$. The
conjecture asserts that there is a real number $\kappa > 1$ such that
$\omega(\mathbb{D}^{+}_n) \sim \kappa \sqrt{n} / \log n$ as $n \to \infty$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Conjecture 2 (ii),
equation (1.6). -/
def KellnerLargePartAsymptoticConjecture : Prop :=
  ∃ κ : ℝ, 1 < κ ∧
    (fun n : ℕ => (ArithmeticFunction.cardDistinctFactors (bernoulliDiffDenominatorLargePart n) :
      ℝ)) ~[atTop] fun n : ℕ => κ * Real.sqrt n / Real.log n

end MetaMathlibExt
