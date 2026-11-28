/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.RatResidue
import Mathlib.Algebra.Field.ZMod

/-!
# The congruence $\sum_{j=0}^{p} pB_j \equiv -1 \pmod p$

For an odd prime $p$, the rational number $S = \sum_{j=0}^{p} p B_j$ is $p$-integral and
$S \equiv -1 \pmod p$, a congruence of Kargın and Mutluer.

## Main statements

* `MetaMathlibExt.sum_prime_mul_bernoulli_mod_prime`: the denominator of $S$ is prime to $p$ and
  the residue of $S$ modulo $p$ is that of $-1$.

## Implementation notes

The proof is the von Staudt–Clausen argument that the source gives as an alternative proof
(Remark 5 of the arXiv version), with Mathlib's `Bernoulli.vonStaudt_clausen`; the source's main
proof goes through its expression of $\sum_j B_j$ by Stirling and harmonic numbers instead.
Write $p = 2k + 1$. By von Staudt–Clausen, $B_{2k} + 1/p + R$ is an integer, where $R$ is a sum
of reciprocals of primes other than $p$, so $p B_{2k} = -1 + p V$ with $V$ $p$-integral. Every
other $B_j$ with $j \le p$ is $p$-integral: $B_0 = 1$, $B_1 = -\tfrac12$, $B_j = 0$ for odd
$j \ge 3$, and von Staudt–Clausen again for even $j < p - 1$, since then $p - 1$ does not divide
$j$. Hence $S = -1 + p W$ with $W$ $p$-integral. Residues are computed through the cast
`ℚ → ZMod p`, which agrees with `ratResidue p` and is additive and multiplicative on rational
numbers whose denominators are prime to $p$.

## References

* Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli Numbers and Its
  Applications*, arXiv:2602.03440v1 (2026), Corollary 4, congruence (16), and Remark 5. The
  theorem's docstring cites the published version (INTEGERS 26 (2026), Article A120,
  Corollary 4, equation (23)).
-/

namespace MetaMathlibExt

open Finset

namespace sum_prime_mul_bernoulli_mod_prime

/-- An integer has `p`-adic valuation at most `1`. -/
private theorem padicValuation_intCast_le_one (p : ℕ) [Fact p.Prime] (z : ℤ) :
    Rat.padicValuation p (z : ℚ) ≤ 1 :=
  Rat.padicValuation_le_one_iff.mpr (by simp [(Fact.out : p.Prime).ne_one])

/-- The reciprocal of a prime `q ≠ p` is `p`-integral. -/
private theorem padicValuation_one_div_prime_le_one {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hqp : q ≠ p) : Rat.padicValuation p ((1 : ℚ) / q) ≤ 1 := by
  rw [Rat.padicValuation_le_one_iff, show ((1 : ℚ) / q).den = q by simp [hq.ne_zero]]
  intro hpq
  exact hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hpq).symm

/-- A sum of reciprocals of primes different from `p` is `p`-integral. -/
private theorem padicValuation_sum_one_div_prime_le_one {p : ℕ} [Fact p.Prime] (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime ∧ q ≠ p) :
    Rat.padicValuation p (∑ q ∈ s, (1 : ℚ) / q) ≤ 1 :=
  (Rat.padicValuation p).map_sum_le fun q hq =>
    padicValuation_one_div_prime_le_one (hs q hq).1 (hs q hq).2

/-- By von Staudt–Clausen, `B_{2m}` is `p`-integral when `p - 1` does not divide `2m`. -/
private theorem padicValuation_bernoulli_two_mul_le_one {p : ℕ} [Fact p.Prime] {m : ℕ}
    (hpm : ¬(p - 1) ∣ 2 * m) : Rat.padicValuation p (bernoulli (2 * m)) ≤ 1 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
  rw [eq_sub_of_add_eq hz.symm]
  refine (Rat.padicValuation p).map_sub_le (padicValuation_intCast_le_one p z)
    (padicValuation_sum_one_div_prime_le_one _ fun q hq => ?_)
  simp only [mem_filter, mem_range] at hq
  exact ⟨hq.2.1, fun hqp => hpm (hqp ▸ hq.2.2)⟩

/-- For `p = 2k + 1` an odd prime, every `B_j` with `j ≤ p` and `j ≠ 2k` is `p`-integral. -/
public theorem padicValuation_bernoulli_le_one {p k j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : p = 2 * k + 1) (hj : j ≤ p) (hjk : j ≠ 2 * k) :
    Rat.padicValuation p (bernoulli j) ≤ 1 := by
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · simp
    · rw [bernoulli_one, Rat.padicValuation_le_one_iff,
        show (-1 / 2 : ℚ).den = 2 by norm_num]
      intro hp
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp)
  · rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
    · rw [← two_mul]
      refine padicValuation_bernoulli_two_mul_le_one fun hdvd => ?_
      have hm : 0 < 2 * m := by omega
      have := Nat.le_of_dvd hm hdvd
      omega
    · simp [bernoulli_eq_zero_of_odd hodd (by omega)]

/-- For an odd prime `p`, the sum `∑_{j=0}^{p} p B_j` is `-1 + p V` with `V` `p`-integral. -/
private theorem exists_sum_prime_mul_bernoulli_eq {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ V : ℚ, Rat.padicValuation p V ≤ 1 ∧
      ∑ j ∈ range (p + 1), (p : ℚ) * bernoulli j = -1 + p * V := by
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  set Q := (range (2 * k + 2)).filter fun q => q.Prime ∧ (q - 1) ∣ 2 * k with hQ
  have hpQ : p ∈ Q := by
    simp only [hQ, mem_filter, mem_range]
    exact ⟨by omega, hp.out, by rw [hk, Nat.add_sub_cancel]⟩
  have hkp : 2 * k ∈ range (p + 1) := mem_range.mpr (by omega)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  refine ⟨z - ∑ q ∈ Q.erase p, (1 : ℚ) / q + ∑ j ∈ (range (p + 1)).erase (2 * k), bernoulli j,
    ?_, ?_⟩
  · refine (Rat.padicValuation p).map_add_le
      ((Rat.padicValuation p).map_sub_le (padicValuation_intCast_le_one p z)
        (padicValuation_sum_one_div_prime_le_one _ fun q hq => ?_))
      ((Rat.padicValuation p).map_sum_le fun j hj => ?_)
    · obtain ⟨hqp, hq⟩ := mem_erase.mp hq
      exact ⟨(mem_filter.mp hq).2.1, hqp⟩
    · obtain ⟨hjk, hj⟩ := mem_erase.mp hj
      exact padicValuation_bernoulli_le_one hp2 hk (by simpa [Nat.lt_succ_iff] using hj) hjk
  · have hsum : ∑ q ∈ Q, (1 : ℚ) / q = 1 / p + ∑ q ∈ Q.erase p, (1 : ℚ) / q :=
      (add_sum_erase Q _ hpQ).symm
    rw [← mul_sum, ← add_sum_erase _ _ hkp, eq_sub_of_add_eq hz.symm, hsum]
    field_simp
    ring

/-- With `ZMod p` a field, `ratResidue p` is the cast `ℚ → ZMod p`. -/
private theorem ratResidue_eq_ratCast {p : ℕ} [Fact p.Prime] (x : ℚ) :
    ratResidue p x = (x : ZMod p) := by
  rw [Rat.cast_def, div_eq_mul_inv]
  rfl

end sum_prime_mul_bernoulli_mod_prime

open sum_prime_mul_bernoulli_mod_prime

/--
**The congruence $\sum_{j=0}^{p} pB_j \equiv -1 \pmod p$.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$. For every odd prime $p$, the rational number
$S = \sum_{j=0}^{p} p B_j$ has denominator not divisible by $p$, and its residue modulo $p$ (its
numerator times the inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (23).
-/
public theorem sum_prime_mul_bernoulli_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j) =
        ratResidue p (-1) := by
  have := Fact.mk hp
  obtain ⟨V, hV, hS⟩ := exists_sum_prime_mul_bernoulli_eq hp2
  have hpV : Rat.padicValuation p ((p : ℚ) * V) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (by exact_mod_cast padicValuation_intCast_le_one p p) hV
  have hden : ¬p ∣ ((p : ℚ) * V).den := Rat.padicValuation_le_one_iff.mp hpV
  have hVden : ¬p ∣ V.den := Rat.padicValuation_le_one_iff.mp hV
  rw [hS]
  refine ⟨Rat.padicValuation_le_one_iff.mp ((Rat.padicValuation p).map_add_le
    (by simp) hpV), ?_⟩
  rw [ratResidue_eq_ratCast, ratResidue_eq_ratCast,
    Rat.cast_add_of_ne_zero (by simp) (by rwa [Ne, ZMod.natCast_eq_zero_iff]),
    Rat.cast_mul_of_ne_zero (by simp) (by rwa [Ne, ZMod.natCast_eq_zero_iff])]
  simp

end MetaMathlibExt
