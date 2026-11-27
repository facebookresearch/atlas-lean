/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.NatInt
public import MathlibExt.NumberTheory.Bernoulli.DerivativeDenominator
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Parity and the lcm recursion for Bernoulli difference denominators

We compare the prime supports in the defining products using base-`p` digit sums.

## References

* Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
  Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, pp. 1–11,
  Lemma 16 (Section 4).
* Bernd C. Kellner and Jonathan Sondow, *Power-Sum Denominators*, American Mathematical Monthly
  124 (2017), pp. 695–709, Theorem 1 (parity).
* Bernd C. Kellner, *On a product of certain primes*, Journal of Number Theory 179 (2017),
  pp. 126–141, Theorem 1 (radical divisibility for the full product).
* Bernd C. Kellner and Jonathan Sondow, *The denominators of power sums of arithmetic
  progressions*, INTEGERS 18 (2018), Article A95, pp. 1–17, Corollary 2(i) (lcm recursion).
* Bernd C. Kellner and Jonathan Sondow, *On Carmichael and polygonal numbers, Bernoulli
  polynomials, and sums of base-p digits*, INTEGERS 21 (2021), Article A52, pp. 1–21,
  Theorem 3.2(ii) (radical divisibility for the coprime part) and equation (3.6) (lcm recursion).
-/

namespace MetaMathlibExt

open UniqueFactorizationMonoid

private def diffDenominatorPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun p => p.Prime ∧ p ≤ (p.digits n).sum

private theorem mem_diffDenominatorPrimes {n p : ℕ} :
    p ∈ diffDenominatorPrimes n ↔ p.Prime ∧ p ≤ (p.digits n).sum := by
  simp only [diffDenominatorPrimes, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨Nat.lt_succ_of_le (h.2.trans (Nat.digit_sum_le p n)), h⟩⟩

private theorem prime_dvd_diffDenominator_iff {n p : ℕ} (hp : p.Prime) :
    p ∣ bernoulliDiffDenominator n ↔ p ∈ diffDenominatorPrimes n := by
  change (p ∣ ∏ q ∈ diffDenominatorPrimes n, q) ↔ _
  refine ⟨fun h => ?_, fun h => Finset.dvd_prod_of_mem _ h⟩
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h
  rwa [Nat.prime_dvd_prime_iff_eq hp (mem_diffDenominatorPrimes.mp hq).1 |>.mp hpq]

private theorem digit_sum_pos {p n : ℕ} (hn : n ≠ 0) : 0 < (p.digits n).sum := by
  have hne := (Nat.digits_ne_nil_iff_ne_zero (b := p)).mpr hn
  exact (Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)).trans_le
    (List.le_sum_of_mem (List.getLast_mem hne))

private theorem binary_digit_sum_lt_two_iff {n : ℕ} (hn : 0 < n) :
    (Nat.digits 2 n).sum < 2 ↔ ∃ e : ℕ, n = 2 ^ e := by
  refine ⟨?_, ?_⟩
  · induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hs
      by_cases h : n = 1
      · exact ⟨0, h⟩
      have hq : 0 < n / 2 := by omega
      have hsum := digit_sum_pos (p := 2) hq.ne'
      rw [Nat.digits_def' (by decide : 1 < 2) hn, List.sum_cons] at hs
      obtain ⟨e, he⟩ := ih (n / 2) (by omega) hq (by omega)
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, ← he]
      omega
  · rintro ⟨e, rfl⟩
    have h := Nat.digits_base_pow_mul (b := 2) (k := e) (m := 1) (by decide) (by decide)
    rw [mul_one] at h
    rw [h, List.sum_append]
    simp

-- For a proper prime divisor of n + 1, the last digit of n is p - 1 and there is an upper digit.
private theorem primeFactor_succ_mem {n p : ℕ} (hcomp : ¬ (n + 1).Prime)
    (hp : p.Prime) (hd : p ∣ n + 1) : p ∈ diffDenominatorPrimes n := by
  have hle := Nat.le_of_dvd (Nat.succ_pos n) hd
  have hne : p ≠ n + 1 := fun h => hcomp (h ▸ hp)
  have hpn : p ≤ n := by omega
  have hq : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).mpr hpn
  have hrest := digit_sum_pos (p := p) (by omega : n / p ≠ 0)
  have hl : n % p + 1 = p := by
    have hmod := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mod_eq_ite, Nat.mod_eq_of_lt hp.one_lt] at hmod
    have := Nat.mod_lt n hp.pos
    split at hmod <;> omega
  refine mem_diffDenominatorPrimes.mpr ⟨hp, ?_⟩
  rw [Nat.digits_def' hp.one_lt (hp.pos.trans_le hpn), List.sum_cons]
  omega

private theorem digit_sum_succ_of_not_dvd {p n : ℕ} (hp : 1 < p) (hn : 0 < n)
    (hd : ¬ p ∣ n + 1) : (p.digits (n + 1)).sum = (p.digits n).sum + 1 := by
  have hdiv := Nat.succ_div_of_not_dvd hd
  have hmod : (n + 1) % p = n % p + 1 := by
    have h₁ := Nat.div_add_mod (n + 1) p
    have h₂ := Nat.div_add_mod n p
    rw [hdiv] at h₁
    omega
  rw [Nat.digits_def' hp (Nat.succ_pos n), Nat.digits_def' hp hn, List.sum_cons, List.sum_cons,
    hdiv, hmod]
  ac_rfl

private theorem diffDenominatorPrimes_eq_union {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    diffDenominatorPrimes n = diffDenominatorPrimes (n + 1) ∪ (n + 1).primeFactors := by
  have hnmod := Nat.odd_iff.mp ho
  have heven : 2 ∣ n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hcomp : ¬ (n + 1).Prime := fun hp =>
    (by omega : 2 ≠ n + 1) ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp heven)
  ext p
  rw [Finset.mem_union, Nat.mem_primeFactors_of_ne_zero (Nat.succ_ne_zero n)]
  constructor
  · intro h
    obtain ⟨hp, hs⟩ := mem_diffDenominatorPrimes.mp h
    by_cases hd : p ∣ n + 1
    · exact Or.inr ⟨hp, hd⟩
    · refine Or.inl (mem_diffDenominatorPrimes.mpr ⟨hp, ?_⟩)
      rw [digit_sum_succ_of_not_dvd hp.one_lt (by omega) hd]
      omega
  · rintro (h | ⟨hp, hd⟩)
    · obtain ⟨hp, hs⟩ := mem_diffDenominatorPrimes.mp h
      by_cases hd : p ∣ n + 1
      · exact primeFactor_succ_mem hcomp hp hd
      · have hpmod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left fun h => hd (h ▸ heven)
        have hparity := Nat.modEq_digits_sum 2 p hpmod n
        change n % 2 = (p.digits n).sum % 2 at hparity
        rw [digit_sum_succ_of_not_dvd hp.one_lt (by omega) hd] at hs
        exact mem_diffDenominatorPrimes.mpr ⟨hp, by omega⟩
    · exact primeFactor_succ_mem hcomp hp hd

private theorem lcm_eq_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    s.lcm id = ∏ p ∈ s, p :=
  Finset.lcm_eq_prod fun p hp q hq hpq => (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq

private theorem prime_prod_union {s t : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (ht : ∀ p ∈ t, Nat.Prime p) : (∏ p ∈ s ∪ t, p) = Nat.lcm (∏ p ∈ s, p) (∏ p ∈ t, p) := by
  have hu (p : ℕ) (hp : p ∈ s ∪ t) : p.Prime :=
    (Finset.mem_union.mp hp).elim (hs p) (ht p)
  rw [← lcm_eq_prod_primes hu, ← lcm_eq_prod_primes hs, ← lcm_eq_prod_primes ht]
  exact Finset.lcm_union

/-- **Parity, radical divisibility and an lcm recursion for $\mathbb{D}_n$.** Write $s_p(m)$ for
the sum of the base-$p$ digits of $m$, let $\mathbb{D}_m$ be the product of the primes $p$ with
$s_p(m) \ge p$, and let $\mathbb{D}^\perp_m$ be the product of the primes $p$ with $p \nmid m$
and $s_p(m) \ge p$. Let $n \ge 1$. Then $\mathbb{D}_n$ is odd if and only if $n = 2^e$ for some
$e \ge 0$. If $n + 1$ is not prime, then the radical $\operatorname{rad}(n + 1)$ divides both
$\mathbb{D}_n$ and $\mathbb{D}^\perp_n$. If $n \ge 3$ is odd, then
$\mathbb{D}_n = \operatorname{lcm}(\mathbb{D}_{n+1}, \operatorname{rad}(n + 1))$.

Source: Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only
Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Lemma 16
(`jis-2024-24.2.8-lem-16`). -/
public theorem bernoulliDiffDenominator_parity_radical_lcm (n : ℕ) (hn : 1 ≤ n) :
    (Odd (bernoulliDiffDenominator n) ↔ ∃ e, n = 2 ^ e) ∧
    (¬ (n + 1).Prime → radical (n + 1) ∣ bernoulliDiffDenominator n ∧
      radical (n + 1) ∣ bernoulliDiffDenominatorCoprimePart n) ∧
    (3 ≤ n → Odd n →
      bernoulliDiffDenominator n =
        Nat.lcm (bernoulliDiffDenominator (n + 1)) (radical (n + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.coprime_two_left, Nat.prime_two.coprime_iff_not_dvd,
      prime_dvd_diffDenominator_iff Nat.prime_two, mem_diffDenominatorPrimes]
    simpa only [Nat.prime_two, true_and, not_le] using binary_digit_sum_lt_two_iff hn
  · intro hcomp
    rw [Nat.radical_eq_prod_primeFactors]
    have hmem (p : ℕ) (hp : p ∈ (n + 1).primeFactors) :
        p ∈ diffDenominatorPrimes n :=
      primeFactor_succ_mem hcomp (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
    refine ⟨Finset.prod_dvd_prod_of_subset _ _ _ hmem, ?_⟩
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    have h := hmem p hp
    obtain ⟨hbound, hprime, hsum⟩ := Finset.mem_filter.mp h
    refine Finset.mem_filter.mpr ⟨hbound, hprime, ?_, hsum⟩
    intro hdn
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hone : p ∣ 1 := by simpa using Nat.dvd_sub hd hdn
    exact hprime.not_dvd_one hone
  · intro hthree hodd
    change (∏ p ∈ diffDenominatorPrimes n, p) =
      Nat.lcm (∏ p ∈ diffDenominatorPrimes (n + 1), p) (radical (n + 1))
    rw [Nat.radical_eq_prod_primeFactors, diffDenominatorPrimes_eq_union hthree hodd]
    exact prime_prod_union (fun _ hp => (mem_diffDenominatorPrimes.mp hp).1)
      (fun _ hp => Nat.prime_of_mem_primeFactors hp)

end MetaMathlibExt
