/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution

/-!
# Parity of the biunitary divisor sum

Only the odd biunitary divisors contribute to parity, and these are exactly the biunitary divisors
of the odd part. Unless that part is `1`, its biunitary divisors pair with their distinct
complements.
-/

namespace MetaMathlibExt

open Finset

private theorem mem_unitaryDivisors_mul_iff_of_coprime {d m a : ℕ} (hm : m ≠ 0) (ha : a ≠ 0)
    (hda : d.Coprime a) : d ∈ (m * a).unitaryDivisors ↔ d ∈ m.unitaryDivisors := by
  simp only [Nat.mem_unitaryDivisors, hda.dvd_mul_right]
  refine and_congr_right fun hd ↦ ?_
  have hdiv : (m * a) / d = (m / d) * a := by
    rw [Nat.mul_comm m a, Nat.mul_div_assoc _ hd, Nat.mul_comm a (m / d)]
  rw [hdiv, Nat.coprime_mul_iff_right]
  exact ⟨fun h ↦ ⟨hm, h.2.1⟩, fun h ↦ ⟨mul_ne_zero hm ha, h.2, hda⟩⟩

private theorem mem_biunitaryDivisors_mul_iff_of_coprime {d m a : ℕ} (hm : m ≠ 0) (ha : a ≠ 0)
    (hda : d.Coprime a) : d ∈ biunitaryDivisors (m * a) ↔ d ∈ biunitaryDivisors m := by
  simp only [mem_biunitaryDivisors, hda.dvd_mul_right]
  refine and_congr_right fun hd ↦ ?_
  have hdiv : (m * a) / d = (m / d) * a := by
    rw [Nat.mul_comm m a, Nat.mul_div_assoc _ hd, Nat.mul_comm a (m / d)]
  have hq : m / d ≠ 0 := by
    intro h
    exact hm (by simpa [h] using (Nat.div_mul_cancel hd).symm)
  have hinter : d.unitaryDivisors ∩ (m / d * a).unitaryDivisors =
      d.unitaryDivisors ∩ (m / d).unitaryDivisors := by
    ext e
    simp only [Finset.mem_inter]
    exact and_congr_right fun he ↦
      mem_unitaryDivisors_mul_iff_of_coprime hq ha
        (hda.of_dvd_left (Nat.dvd_of_mem_unitaryDivisors he))
  simp [hm, ha, hdiv, gcdUnitary, hinter]

private theorem odd_of_dvd_odd {d m : ℕ} (hd : d ∣ m) (hm : Odd m) : Odd d := by
  obtain ⟨a, rfl⟩ := hd
  exact Nat.Odd.of_mul_left hm

private theorem cast_sigmaBiunitary_mul_two_pow {m : ℕ} (hm : Odd m) (k : ℕ) :
    (sigmaBiunitary (m * 2 ^ k) : ZMod 2) = (sigmaBiunitary m : ZMod 2) := by
  have hm0 : m ≠ 0 := fun h ↦ Nat.not_odd_zero (h ▸ hm)
  have hmem (d : ℕ) (hodd : Odd d) :
      d ∈ biunitaryDivisors (m * 2 ^ k) ↔ d ∈ biunitaryDivisors m := by
    have hcop : d.Coprime 2 :=
      ((Nat.coprime_or_dvd_of_prime Nat.prime_two d).resolve_right hodd.not_two_dvd_nat).symm
    exact mem_biunitaryDivisors_mul_iff_of_coprime hm0 (by simp) (hcop.pow_right k)
  have hfilter : (biunitaryDivisors (m * 2 ^ k)).filter Odd = biunitaryDivisors m := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hodd⟩
      exact (hmem d hodd).mp hd
    · intro hd
      have hodd := odd_of_dvd_odd (dvd_of_mem_biunitaryDivisors hd) hm
      exact ⟨(hmem d hodd).mpr hd, hodd⟩
  simp only [sigmaBiunitary, Nat.cast_sum]
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  split_ifs with h
  · rfl
  · exact ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h)

private theorem even_sigmaBiunitary_of_odd {m : ℕ} (hm : Odd m) (hm1 : m ≠ 1) :
    Even (sigmaBiunitary m) := by
  rw [← ZMod.natCast_eq_zero_iff_even, sigmaBiunitary, Nat.cast_sum]
  have hm0 : m ≠ 0 := fun h ↦ Nat.not_odd_zero (h ▸ hm)
  have hdiv (d : ℕ) (hd : d ∈ biunitaryDivisors m) : m / (m / d) = d :=
    Nat.div_div_self (dvd_of_mem_biunitaryDivisors hd) hm0
  refine Finset.sum_involution (fun d _ ↦ m / d) ?_ ?_ ?_ hdiv
  · intro d hd
    have hdd := dvd_of_mem_biunitaryDivisors hd
    have hadd := (odd_of_dvd_odd hdd hm).add_odd (odd_of_dvd_odd (Nat.div_dvd_of_dvd hdd) hm)
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff_even]
    exact hadd
  · intro d hd _ hfix
    obtain ⟨hdd, -, hunit⟩ := mem_biunitaryDivisors.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos hdd (Nat.pos_of_ne_zero hm0)
    have hself : d ∈ d.unitaryDivisors := by simp [hdpos.ne', Nat.div_self hdpos]
    rw [hfix] at hunit
    have hle := le_gcdUnitary hself hself
    rw [hunit] at hle
    have hd1 : d = 1 := le_antisymm hle hdpos
    exact hm1 (by simpa [hd1] using hfix)
  · intro d hd
    obtain ⟨hdd, hm0, hunit⟩ := mem_biunitaryDivisors.mp hd
    exact mem_biunitaryDivisors.mpr
      ⟨Nat.div_dvd_of_dvd hdd, hm0, by rwa [hdiv d hd, gcdUnitary_comm]⟩

/-- **Parity of the biunitary divisor sum.** For every positive integer $n$, the biunitary divisor
sum $\sigma^{**}(n)$ is odd if and only if $n = 2^k$ for some natural number $k$ (so $n = 1$ is
included).

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem odd_sigmaBiunitary_iff (n : ℕ) (hn : 0 < n) :
    Odd (sigmaBiunitary n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  have hm : Odd (ordCompl[2] n) :=
    Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp (Nat.not_dvd_ordCompl Nat.prime_two hn.ne'))
  have hfac : ordCompl[2] n * 2 ^ n.factorization 2 = n :=
    (Nat.mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n 2)
  have hcast : (sigmaBiunitary n : ZMod 2) = (sigmaBiunitary (ordCompl[2] n) : ZMod 2) := by
    rw [← cast_sigmaBiunitary_mul_two_pow hm (n.factorization 2), hfac]
  have hpar : Odd (sigmaBiunitary n) ↔ Odd (sigmaBiunitary (ordCompl[2] n)) := by
    simp only [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, hcast]
  rw [hpar]
  constructor
  · intro h
    have h1 : ordCompl[2] n = 1 := by
      by_contra hne
      exact (Nat.not_odd_iff_even.mpr (even_sigmaBiunitary_of_odd hm hne)) h
    exact ⟨n.factorization 2, by simpa only [h1, mul_one] using
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
  · rintro ⟨k, rfl⟩
    rw [Nat.ordCompl_self_pow Nat.prime_two, sigmaBiunitary_one]
    exact odd_one

private theorem gcdUnitary_eq_one_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔ ∀ u ∈ a.unitaryDivisors, u ∈ b.unitaryDivisors → u = 1 := by
  constructor
  · intro h u hua hub
    exact le_antisymm (h ▸ le_gcdUnitary hua hub)
      (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_unitaryDivisors hua) ha.bot_lt)
  · intro h
    obtain ⟨hu, hv⟩ := gcdUnitary_mem_unitaryDivisors ha hb
    exact h _ hu hv

private theorem gcdUnitary_mul_eq_one_iff {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (h : (a * c).Coprime (b * d)) :
    gcdUnitary (a * b) (c * d) = 1 ↔ gcdUnitary a c = 1 ∧ gcdUnitary b d = 1 := by
  have hab := h.of_dvd (dvd_mul_right a c) (dvd_mul_right b d)
  have had := h.of_dvd (dvd_mul_right a c) (dvd_mul_left d b)
  have hcb := h.of_dvd (dvd_mul_left c a) (dvd_mul_right b d)
  have hcd := h.of_dvd (dvd_mul_left c a) (dvd_mul_left d b)
  rw [gcdUnitary_eq_one_iff (mul_ne_zero ha hb) (mul_ne_zero hc hd),
    gcdUnitary_eq_one_iff ha hc, gcdUnitary_eq_one_iff hb hd]
  constructor
  · intro h
    refine ⟨fun u hua huc ↦ h u ?_ ?_, fun u hub hud ↦ h u ?_ ?_⟩
    · simpa using Nat.mul_mem_unitaryDivisors_mul hab hua (by simp [hb] : 1 ∈ b.unitaryDivisors)
    · simpa using Nat.mul_mem_unitaryDivisors_mul hcd huc (by simp [hd] : 1 ∈ d.unitaryDivisors)
    · simpa using Nat.mul_mem_unitaryDivisors_mul hab (by simp [ha] : 1 ∈ a.unitaryDivisors) hub
    · simpa using Nat.mul_mem_unitaryDivisors_mul hcd (by simp [hc] : 1 ∈ c.unitaryDivisors) hud
  · rintro ⟨h₁, h₂⟩ u hu hv
    have hu' := Nat.dvd_of_mem_unitaryDivisors hu
    have hv' := Nat.dvd_of_mem_unitaryDivisors hv
    have gcd_dvd_gcd_of_dvd_mul {x y z : ℕ} (hxz : x.Coprime z) (huyz : u ∣ y * z) :
        u.gcd x ∣ u.gcd y :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((hxz.of_dvd_left (Nat.gcd_dvd_right _ _)).dvd_mul_right.mp
          ((Nat.gcd_dvd_left _ _).trans huyz))
    have hleft : u.gcd a = u.gcd c := Nat.dvd_antisymm
      (gcd_dvd_gcd_of_dvd_mul had hv') (gcd_dvd_gcd_of_dvd_mul hcb hu')
    have hright : u.gcd b = u.gcd d := Nat.dvd_antisymm
      (gcd_dvd_gcd_of_dvd_mul hcb.symm (mul_comm c d ▸ hv'))
      (gcd_dvd_gcd_of_dvd_mul had.symm (mul_comm a b ▸ hu'))
    have hga := h₁ _ (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab hu)
      (hleft ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd hv)
    have hgb := h₂ _ (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab.symm (mul_comm a b ▸ hu))
      (hright ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd.symm (mul_comm c d ▸ hv))
    rw [← Nat.gcd_eq_left hu', hab.gcd_mul, hga, hgb, mul_one]

private theorem sigmaBiunitary_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  have hmem (a b : ℕ) (ha : a ∣ m) (hb : b ∣ n) :
      a * b ∈ biunitaryDivisors (m * n) ↔ a ∈ biunitaryDivisors m ∧ b ∈ biunitaryDivisors n := by
    have ha' := Nat.div_dvd_of_dvd ha
    have hb' := Nat.div_dvd_of_dvd hb
    have hcop : (a * (m / a)).Coprime (b * (n / b)) := by
      rwa [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb]
    simp only [mem_biunitaryDivisors, Nat.mul_dvd_mul ha hb, ha, hb, true_and,
      ← Nat.div_mul_div_comm ha hb]
    rw [and_iff_right (mul_ne_zero hm hn), and_iff_right hm, and_iff_right hn]
    exact gcdUnitary_mul_eq_one_iff (ne_zero_of_dvd_ne_zero hm ha) (ne_zero_of_dvd_ne_zero hn hb)
      (ne_zero_of_dvd_ne_zero hm ha') (ne_zero_of_dvd_ne_zero hn hb') hcop
  have hsplit {u : ℕ} (hu : u ∈ biunitaryDivisors (m * n)) : u.gcd m * u.gcd n = u := by
    rw [← hmn.gcd_mul, Nat.gcd_eq_left (dvd_of_mem_biunitaryDivisors hu)]
  simp only [sigmaBiunitary, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  -- Coprimality gives a bijection via multiplication and the two gcd projections.
  refine Finset.sum_nbij' (fun x ↦ x.1 * x.2) (fun u ↦ (u.gcd m, u.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
    exact (hmem a b (dvd_of_mem_biunitaryDivisors ha)
      (dvd_of_mem_biunitaryDivisors hb)).mpr ⟨ha, hb⟩
  · intro u hu
    exact Finset.mem_product.mpr ((hmem _ _ (Nat.gcd_dvd_right u m) (Nat.gcd_dvd_right u n)).mp
      (by rwa [hsplit hu]))
  · rintro ⟨a, b⟩ hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
    have ham := dvd_of_mem_biunitaryDivisors ha
    have hbn := dvd_of_mem_biunitaryDivisors hb
    simp only [Prod.mk.injEq]
    exact ⟨by rw [Nat.Coprime.gcd_mul_right_cancel a (hmn.symm.of_dvd_left hbn),
        Nat.gcd_eq_left ham],
      by rw [Nat.Coprime.gcd_mul_left_cancel b (hmn.of_dvd_left ham), Nat.gcd_eq_left hbn]⟩
  · exact fun _ hu ↦ hsplit hu
  · intro _ _
    rfl

/-- The sum of biunitary divisors, bundled as a natural-valued arithmetic function. -/
@[expose] public def sigmaBiunitaryArithmeticFunction : ArithmeticFunction ℕ :=
  ⟨sigmaBiunitary, sigmaBiunitary_zero⟩

@[simp] public theorem sigmaBiunitaryArithmeticFunction_apply (n : ℕ) :
    sigmaBiunitaryArithmeticFunction n = sigmaBiunitary n := rfl

/-- **Multiplicativity of the biunitary divisor sum.** The biunitary divisor sum satisfies
$\sigma^{**}(1) = 1$. For coprime natural numbers $m$ and $n$, it satisfies
$\sigma^{**}(mn) = \sigma^{**}(m)\sigma^{**}(n)$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Section 2 (after Wall). -/
public theorem isMultiplicative_sigmaBiunitaryArithmeticFunction :
    sigmaBiunitaryArithmeticFunction.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
    ⟨sigmaBiunitary_one, fun hm hn hmn ↦ sigmaBiunitary_mul_of_coprime hmn hm hn⟩

/-- **Divisibility of the biunitary divisor sum of an even number by a power of two.** For every
positive even natural number $n$, writing $\omega(n)$ for the number of distinct prime factors of
$n$, the power $2^{\omega(n) - 1}$ divides the biunitary divisor sum $\sigma^{**}(n)$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem two_pow_card_primeFactors_sub_one_dvd_sigmaBiunitary_of_even (n : ℕ)
    (hn : 0 < n) (he : Even n) : 2 ^ (n.primeFactors.card - 1) ∣ sigmaBiunitary n := by
  have hprod : sigmaBiunitary n = ∏ p ∈ n.primeFactors, sigmaBiunitary (p ^ n.factorization p) := by
    calc
      sigmaBiunitary n = sigmaBiunitaryArithmeticFunction (∏ p ∈ n.primeFactors,
          p ^ n.factorization p) := by
        rw [← Nat.prod_primeFactors_pow_factorization hn.ne']
        rfl
      _ = _ := isMultiplicative_sigmaBiunitaryArithmeticFunction.map_prod _ _ fun p hp q hq hpq ↦
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hq)).mpr hpq).pow _ _
  have htwo := Nat.prime_two.mem_primeFactors (even_iff_two_dvd.mp he) hn.ne'
  rw [hprod, ← Finset.card_erase_of_mem htwo, ← Finset.prod_const,
    ← Finset.prod_erase_mul _ _ htwo]
  refine (Finset.prod_dvd_prod_of_dvd _ _ fun p hp ↦ ?_).trans (dvd_mul_right _ _)
  obtain ⟨hp₂, hp⟩ := Finset.mem_erase.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have he' := hprime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
  exact even_iff_two_dvd.mp (even_sigmaBiunitary_of_odd (hprime.odd_of_ne_two hp₂).pow
    (Nat.one_lt_pow he'.ne' hprime.one_lt).ne')

end MetaMathlibExt
