/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import MathlibExt.NumberTheory.Bernoulli.DerivativeDenominator
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Radical.NatInt
import MathlibExt.NumberTheory.Bernoulli.KellnerSondowBernoulliDenominator

/-!
# Denominators of Bernoulli polynomials are even

For `n ≥ 1`, the denominator of the Bernoulli polynomial `Bₙ(x)` is the radical of the
denominator of `Sₙ(x) = (Bₙ₊₁(x) - Bₙ₊₁) / (n + 1)` and is even, so `Bₙ(x)` never has integer
coefficients; Kellner's product of the primes `p ∤ n` with `s_p(n) ≥ p` is even for odd `n ≥ 3`
and odd for `n = 1` and for even `n`. This is `bernoulli_polynomial_denominator_rad_even`.

The proof combines the Kellner–Sondow product formula for the denominator of `Bₙ(x)`
(`kellner_sondow_bernoulli_denom`) with Kummer's theorem on the `p`-adic valuation of binomial
coefficients: a prime divides the denominator of a coefficient
`binom(n + 1, k) Bₖ / (n + 1)` of `Sₙ(x)` only if it divides `n + 1` or its base-`p` digit sum
`s_p(n + 1)` is at least `p`.
-/

namespace MetaMathlibExt

open Polynomial UniqueFactorizationMonoid

/-- The primes `p ≤ n + 1` with `p ∣ n + 1` or `s_p(n + 1) ≥ p`; by Kellner and Sondow, their
product is the denominator of `Bₙ(x)` for `n ≥ 1`. -/
private def bernoulliDenPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 2)).filter fun p => p.Prime ∧ (p ∣ n + 1 ∨ p ≤ (p.digits (n + 1)).sum)

/-- The Kellner–Sondow triple product, merged into one product over `bernoulliDenPrimes n`. -/
private theorem polynomialDenominator_bernoulli_eq_prod {n : ℕ} (hn : 1 ≤ n) :
    polynomialDenominator (Polynomial.bernoulli n) = ∏ p ∈ bernoulliDenPrimes n, p := by
  have e1 : (bernoulliDenPrimes n).filter (fun p => ¬ p ∣ n + 1) =
      (Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ ¬ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum) := by
    ext p
    simp only [bernoulliDenPrimes, Finset.mem_filter]
    tauto
  have e2 : ((bernoulliDenPrimes n).filter (fun p => p ∣ n + 1)).filter
      (fun p => p ≤ (p.digits (n + 1)).sum) = (Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ p ≤ (Nat.digits p (n + 1)).sum) := by
    ext p
    simp only [bernoulliDenPrimes, Finset.mem_filter]
    tauto
  have e3 : ((bernoulliDenPrimes n).filter (fun p => p ∣ n + 1)).filter
      (fun p => ¬ p ≤ (p.digits (n + 1)).sum) = (Finset.range (n + 2)).filter
        (fun p => Nat.Prime p ∧ p ∣ (n + 1) ∧ (Nat.digits p (n + 1)).sum < p) := by
    ext p
    simp only [bernoulliDenPrimes, Finset.mem_filter, not_le]
    tauto
  rw [polynomialDenominator, kellner_sondow_bernoulli_denom n hn, ← e1, ← e2, ← e3, mul_assoc,
    Finset.prod_filter_mul_prod_filter_not, mul_comm, Finset.prod_filter_mul_prod_filter_not]

private theorem prime_dvd_prod_bernoulliDenPrimes_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ bernoulliDenPrimes n, q ↔ p ∈ bernoulliDenPrimes n := by
  refine ⟨fun h => ?_, fun h => Finset.dvd_prod_of_mem _ h⟩
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (Finset.mem_filter.mp hq).2.1).mp hpq]

/-- A prime dividing the denominator of a polynomial divides the denominator of a coefficient. -/
private theorem exists_prime_dvd_coeff_den {P : ℚ[X]} {p : ℕ} (hp : p.Prime)
    (h : p ∣ polynomialDenominator P) : ∃ i, p ∣ (P.coeff i).den := by
  obtain ⟨i, -, hi⟩ := hp.prime.exists_mem_finset_dvd (h.trans (Finset.lcm_dvd_prod _ _))
  exact ⟨i, hi⟩

/-- A rational number that becomes an integer after multiplication by a natural number prime
to `p` has a denominator prime to `p`. -/
private theorem not_dvd_den_of_mul_eq_intCast {p : ℕ} [Fact p.Prime] {x : ℚ} {m : ℕ}
    (hm : ¬ p ∣ m) {z : ℤ} (h : x * m = z) : ¬ p ∣ x.den := by
  rw [← Rat.padicValuation_le_one_iff]
  have hv := congrArg (Rat.padicValuation p) h
  rw [map_mul, Rat.padicValuation_natCast, Rat.padicValuation_cast,
    Int.padicValuation_eq_one_iff.mpr (by exact_mod_cast hm), mul_one] at hv
  exact hv ▸ Int.padicValuation_le_one p z

private theorem digit_sum_eq_mod_add {p : ℕ} (hp : 1 < p) (m : ℕ) :
    (p.digits m).sum = m % p + (p.digits (m / p)).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.digits_def' hp hm, List.sum_cons]

private theorem digit_sum_pos {p m : ℕ} (hm : m ≠ 0) : 0 < (p.digits m).sum := by
  have hne := (Nat.digits_ne_nil_iff_ne_zero (b := p)).mpr hm
  have h1 := List.le_sum_of_mem (List.getLast_mem hne)
  have h2 := Nat.getLast_digit_ne_zero p hm
  omega

/-- Adding one without a carry raises the base-`p` digit sum by one. -/
private theorem digit_sum_succ {p m : ℕ} (hp : 1 < p) (h : ¬ p ∣ m + 1) :
    (p.digits (m + 1)).sum = (p.digits m).sum + 1 := by
  have hdiv := Nat.succ_div_of_not_dvd h
  have hmod : (m + 1) % p = m % p + 1 := by
    have h1 := Nat.div_add_mod (m + 1) p
    have h2 := Nat.div_add_mod m p
    rw [hdiv] at h1
    omega
  rw [digit_sum_eq_mod_add hp (m + 1), digit_sum_eq_mod_add hp m, hdiv, hmod]
  ring

/-- If `p ∣ m + 1`, then the units digit of `m` in base `p` is `p - 1`. -/
private theorem sub_one_le_digit_sum_of_dvd_succ {p m : ℕ} (hp : 1 < p) (h : p ∣ m + 1) :
    p - 1 ≤ (p.digits m).sum := by
  have hmod : m % p = p - 1 := by
    have h0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.add_mod, Nat.mod_eq_of_lt hp] at h0
    have h2 := Nat.mod_lt m (by omega : 0 < p)
    by_contra hne
    rw [Nat.mod_eq_of_lt (by omega : m % p + 1 < p)] at h0
    omega
  rw [digit_sum_eq_mod_add hp m]
  omega

/-- A number `m ≥ p` not divisible by `p` has base-`p` digit sum at least `2`. -/
private theorem two_le_digit_sum {p m : ℕ} (hp : 1 < p) (hpm : p ≤ m) (h : ¬ p ∣ m) :
    2 ≤ (p.digits m).sum := by
  have h1 : m % p ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
  have h2 : m / p ≠ 0 := by
    have := (Nat.one_le_div_iff (by omega : 0 < p)).mpr hpm
    omega
  have h3 := digit_sum_pos (p := p) h2
  rw [digit_sum_eq_mod_add hp m]
  omega

/-- Kummer's theorem: if `s_p(k) ≥ p - 1` and `s_p(n + 1) < p` with `k ≤ n`, then adding `k` and
`n + 1 - k` in base `p` carries, so `p` divides `binom(n + 1, k)`. -/
private theorem prime_dvd_choose_succ {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hk : p - 1 ≤ (p.digits k).sum) (hs : (p.digits (n + 1)).sum < p) :
    p ∣ (n + 1).choose k := by
  have := Fact.mk hp
  by_contra h
  have hkum := sub_one_mul_multiplicity_choose_eq_sub_sum_digits (p := p) (by omega : k ≤ n + 1)
  rw [Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr h)), mul_zero] at hkum
  have hpos := digit_sum_pos (p := p) (by omega : n + 1 - k ≠ 0)
  have := hp.two_le
  omega

/-- If `s_p(n + 1) < p` and `k ≤ n`, then `binom(n + 1, k) Bₖ` has a denominator prime to `p`.
When `p` divides the denominator of `Bₖ`, the Kellner–Sondow formula for `Bₖ(x)` gives
`s_p(k) ≥ p - 1`, so `p ∣ binom(n + 1, k)` by Kummer's theorem, and it shows that `p` divides
the denominator of `Bₖ` only once. -/
private theorem not_dvd_den_bernoulli_mul_choose {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hs : (p.digits (n + 1)).sum < p) :
    ¬ p ∣ (_root_.bernoulli k * ((n + 1).choose k : ℚ)).den := by
  have := Fact.mk hp
  by_cases hB : p ∣ (_root_.bernoulli k).den
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [_root_.bernoulli_zero, Rat.den_one, Nat.dvd_one] at hB
        exact absurd hB hp.ne_one
      · exact hk
    have hden : (_root_.bernoulli k).den ∣ ∏ q ∈ bernoulliDenPrimes k, q := by
      rw [← polynomialDenominator_bernoulli_eq_prod hk]
      simpa [Polynomial.coeff_bernoulli] using
        coeff_den_dvd_polynomialDenominator (Polynomial.bernoulli k) 0
    have hpk : p ∈ bernoulliDenPrimes k :=
      (prime_dvd_prod_bernoulliDenPrimes_iff hp).mp (hB.trans hden)
    have hsk : p - 1 ≤ (p.digits k).sum := by
      rcases (Finset.mem_filter.mp hpk).2.2 with hdvd | hle
      · exact sub_one_le_digit_sum_of_dvd_succ hp.one_lt hdvd
      · by_cases hd : p ∣ k + 1
        · exact sub_one_le_digit_sum_of_dvd_succ hp.one_lt hd
        · rw [digit_sum_succ hp.one_lt hd] at hle
          omega
    obtain ⟨c, hc⟩ := prime_dvd_choose_succ hp hkn hsk hs
    obtain ⟨e, he⟩ := hden
    have hD := Finset.mul_prod_erase (bernoulliDenPrimes k) (fun q => q) hpk
    refine not_dvd_den_of_mul_eq_intCast (m := ∏ q ∈ (bernoulliDenPrimes k).erase p, q) ?_
      (z := (_root_.bernoulli k).num * e * c) ?_
    · intro h
      obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h
      have hq' := Finset.mem_erase.mp hq
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hp (Finset.mem_filter.mp hq'.2).2.1).mp hpq).symm
    · have hcast : (p : ℚ) * ((∏ q ∈ (bernoulliDenPrimes k).erase p, q : ℕ) : ℚ) =
          ((_root_.bernoulli k).den : ℚ) * e := by
        exact_mod_cast hD.trans he
      rw [hc]
      push_cast at hcast ⊢
      rw [← Rat.mul_den_eq_num]
      linear_combination (_root_.bernoulli k) * c * hcast
  · refine not_dvd_den_of_mul_eq_intCast (m := (_root_.bernoulli k).den) hB
      (z := (_root_.bernoulli k).num * (n + 1).choose k) ?_
    rw [mul_right_comm, Rat.mul_den_eq_num]
    push_cast
    ring

/-- The denominator of `Bₙ(x)` is the radical of the denominator of
`Sₙ(x) = (Bₙ₊₁(x) - Bₙ₊₁) / (n + 1)`: both have the prime factors `bernoulliDenPrimes n`. -/
private theorem radical_polynomialDenominator_powerSum {n : ℕ} (hn : 1 ≤ n) :
    radical (polynomialDenominator
      (C ((n : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1))))) =
      polynomialDenominator (Polynomial.bernoulli n) := by
  set S := C ((n : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1)))
    with hS
  have hcoeff : ∀ j, S.coeff j = ((n : ℚ) + 1)⁻¹ * ((Polynomial.bernoulli (n + 1)).coeff j -
      if j = 0 then _root_.bernoulli (n + 1) else 0) := by
    intro j
    rw [hS, coeff_C_mul, coeff_sub, coeff_C]
  -- `Sₙ(x)` is an antiderivative of `Bₙ(x)`.
  have hshift : ∀ i, (Polynomial.bernoulli n).coeff i = S.coeff (i + 1) * ((i + 1 : ℕ) : ℚ) := by
    intro i
    have h := congrArg (fun P => P.coeff i) (derivative_bernoulli_add_one n)
    simp only [coeff_derivative, ← Nat.cast_add_one, coeff_natCast_mul] at h
    rw [hcoeff, ite_eq_right (Nat.succ_ne_zero i), sub_zero, mul_assoc, h, ← mul_assoc,
      Nat.cast_add_one, inv_mul_cancel₀ (by positivity), one_mul]
  have hE0 : polynomialDenominator S ≠ 0 := by
    rw [polynomialDenominator, Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨i, -, hi⟩
    exact (S.coeff i).den_nz hi
  have hdvd : polynomialDenominator (Polynomial.bernoulli n) ∣ polynomialDenominator S := by
    apply Finset.lcm_dvd
    intro i _
    rw [hshift i]
    refine (Rat.mul_den_dvd _ _).trans ?_
    rw [Rat.den_natCast, mul_one]
    exact coeff_den_dvd_polynomialDenominator S (i + 1)
  have hprimes : (polynomialDenominator S).primeFactors = bernoulliDenPrimes n := by
    ext p
    rw [Nat.mem_primeFactors_of_ne_zero hE0]
    constructor
    · rintro ⟨hp, hpS⟩
      obtain ⟨j, hj⟩ := exists_prime_dvd_coeff_den hp hpS
      by_contra hT
      have hn1 : ¬ p ∣ n + 1 := fun h => hT (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by have := Nat.le_of_dvd (by omega) h; omega), hp, Or.inl h⟩)
      have hs : (p.digits (n + 1)).sum < p := by
        by_contra hle
        push Not at hle
        exact hT (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (by have := Nat.digit_sum_le p (n + 1); omega), hp, Or.inr hle⟩)
      rw [hcoeff j, Polynomial.coeff_bernoulli] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [zero_le, ite_true, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
          mul_one, sub_self, mul_zero, Rat.den_zero, Nat.dvd_one] at hj
        exact hp.ne_one hj
      · rw [ite_eq_right hj0.ne', sub_zero] at hj
        split_ifs at hj with hjn
        · have hcore := not_dvd_den_bernoulli_mul_choose hp (k := n + 1 - j) (by omega) hs
          rw [Nat.choose_symm hjn] at hcore
          have h1 := hj.trans (Rat.mul_den_dvd _ _)
          rw [← Nat.cast_add_one, Rat.inv_natCast_den, ite_eq_right (Nat.succ_ne_zero n)] at h1
          rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
          · exact hn1 h
          · exact hcore h
        · simp only [mul_zero, Rat.den_zero, Nat.dvd_one] at hj
          exact hp.ne_one hj
    · intro hp
      have hpp := (Finset.mem_filter.mp hp).2.1
      refine ⟨hpp, ((prime_dvd_prod_bernoulliDenPrimes_iff hpp).mpr hp).trans ?_⟩
      rw [← polynomialDenominator_bernoulli_eq_prod hn]
      exact hdvd
  rw [Nat.radical_eq_prod_primeFactors, hprimes, polynomialDenominator_bernoulli_eq_prod hn]

/-- **Denominators of Bernoulli polynomials are even.** Let $n \ge 1$. Write $\mathfrak{D}_n$ for
the denominator of the Bernoulli polynomial $B_n(x)$, $\mathcal{D}_n$ for the denominator of
$S_n(x) = (B_{n+1}(x) - B_{n+1}) / (n + 1)$, where $B_{n+1}$ is the Bernoulli number,
$\operatorname{rad}(m)$ for the product of the primes dividing $m$, and $\mathbb{D}^{\perp}_n$ for
the product of the primes $p \nmid n$ whose base-$p$ digit sum $s_p(n)$ satisfies $s_p(n) \ge p$.
Then $\mathfrak{D}_n = \operatorname{rad}(\mathcal{D}_n)$; $\mathfrak{D}_n$ is even; some
coefficient of $B_n(x)$ is not an integer; $\mathbb{D}^{\perp}_n$ is even if $n \ge 3$ is odd;
and $\mathbb{D}^{\perp}_n$ is odd if $n = 1$ or $n$ is even.

Part (iii) of Corollary 8 is printed as "otherwise, $\mathbb{D}^{\perp}_n$ is even", which fails
at $n = 2$, where $\mathbb{D}^{\perp}_2 = 1$; the proof in the paper shows
$\mathbb{D}^{\perp}_1 = 1$ and $2 \nmid \mathbb{D}^{\perp}_n$ for even $n$, and the statement
above follows that proof.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Corollary 8
(`jis-2024-24.2.8-cor-8`). -/
public theorem bernoulli_polynomial_denominator_rad_even (n : ℕ) (hn : 1 ≤ n) :
    polynomialDenominator (Polynomial.bernoulli n) =
        radical (polynomialDenominator
          (C ((n : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1))))) ∧
      Even (polynomialDenominator (Polynomial.bernoulli n)) ∧
      (∃ i, ((Polynomial.bernoulli n).coeff i).den ≠ 1) ∧
      (3 ≤ n → Odd n → Even (bernoulliDiffDenominatorCoprimePart n)) ∧
      (n = 1 ∨ Even n → Odd (bernoulliDiffDenominatorCoprimePart n)) := by
  have h2 : 2 ∈ bernoulliDenPrimes n := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, ?_⟩
    by_cases h : 2 ∣ n + 1
    · exact Or.inl h
    · exact Or.inr (two_le_digit_sum (by norm_num) (by omega) h)
  have heven : Even (polynomialDenominator (Polynomial.bernoulli n)) := by
    rw [polynomialDenominator_bernoulli_eq_prod hn, even_iff_two_dvd]
    exact Finset.dvd_prod_of_mem _ h2
  refine ⟨(radical_polynomialDenominator_powerSum hn).symm, heven, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    rw [(polynomialDenominator_eq_one_iff _).mpr h] at heven
    exact Nat.not_even_one heven
  · intro h3 hodd
    have h2n : ¬ 2 ∣ n := by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]
    rw [even_iff_two_dvd, bernoulliDiffDenominatorCoprimePart]
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, h2n, two_le_digit_sum (by norm_num) (by omega) h2n⟩
  · intro h
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, bernoulliDiffDenominatorCoprimePart]
    intro h2
    obtain ⟨q, hq, h2q⟩ := Nat.prime_two.prime.exists_mem_finset_dvd h2
    rw [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqn, hqp, hqdvd, -⟩ := hq
    rw [← (Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).mp h2q] at hqn hqdvd
    rcases h with rfl | ⟨r, rfl⟩
    · omega
    · exact hqdvd ⟨r, by ring⟩

end MetaMathlibExt
