/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor
import Mathlib.Data.Finset.NatDivisors
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity
import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution
import Mathlib.Tactic.Linarith

/-!
# Biunitary triperfect numbers with exact exponent four at two

The biunitary triperfect numbers with exact exponent four at two and exponent three or four
at three equal `2160`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 14.
-/

namespace MetaMathlibExt

open Finset

private theorem gcdUnitary_eq_one_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gcdUnitary a b = 1 ↔
      ∀ d, d ∈ a.unitaryDivisors → d ∈ b.unitaryDivisors → d = 1 := by
  constructor
  · intro h d hda hdb
    apply le_antisymm
    · simpa only [h] using le_gcdUnitary hda hdb
    · exact Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_unitaryDivisors hda)
        (Nat.pos_of_ne_zero ha)
  · intro h
    obtain ⟨hda, hdb⟩ := gcdUnitary_mem_unitaryDivisors ha hb
    exact h _ hda hdb

private theorem gcd_eq_of_dvd_products {a b c d e : ℕ}
    (h : (a * c).Coprime (b * d)) (he : e ∣ a * b) (he' : e ∣ c * d) :
    e.gcd a = e.gcd c := by
  have had : a.Coprime d :=
    (h.coprime_dvd_left (Nat.dvd_mul_right a c)).coprime_dvd_right (Nat.dvd_mul_left d b)
  have hcb : c.Coprime b :=
    (h.coprime_dvd_left (Nat.dvd_mul_left c a)).coprime_dvd_right (Nat.dvd_mul_right b d)
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left e a)
    exact (had.coprime_dvd_left (Nat.gcd_dvd_right e a)).dvd_of_dvd_mul_right
      ((Nat.gcd_dvd_left e a).trans he')
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left e c)
    exact (hcb.coprime_dvd_left (Nat.gcd_dvd_right e c)).dvd_of_dvd_mul_right
      ((Nat.gcd_dvd_left e c).trans he)

private theorem gcdUnitary_mul_eq_one_iff {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (a * c).Coprime (b * d)) :
    gcdUnitary (a * b) (c * d) = 1 ↔ gcdUnitary a c = 1 ∧ gcdUnitary b d = 1 := by
  have hab : a.Coprime b :=
    (h.coprime_dvd_left (Nat.dvd_mul_right a c)).coprime_dvd_right (Nat.dvd_mul_right b d)
  have hcd : c.Coprime d :=
    (h.coprime_dvd_left (Nat.dvd_mul_left c a)).coprime_dvd_right (Nat.dvd_mul_left d b)
  rw [gcdUnitary_eq_one_iff (mul_ne_zero ha hb) (mul_ne_zero hc hd),
    gcdUnitary_eq_one_iff ha hc, gcdUnitary_eq_one_iff hb hd]
  constructor
  · intro hu
    constructor
    · intro e hea hec
      apply hu e
      · simpa only [mul_one] using
          Nat.mul_mem_unitaryDivisors_mul hab hea (show 1 ∈ b.unitaryDivisors by simp [hb])
      · simpa only [mul_one] using
          Nat.mul_mem_unitaryDivisors_mul hcd hec (show 1 ∈ d.unitaryDivisors by simp [hd])
    · intro e heb hed
      apply hu e
      · simpa only [one_mul] using
          Nat.mul_mem_unitaryDivisors_mul hab (show 1 ∈ a.unitaryDivisors by simp [ha]) heb
      · simpa only [one_mul] using
          Nat.mul_mem_unitaryDivisors_mul hcd (show 1 ∈ c.unitaryDivisors by simp [hc]) hed
  · rintro ⟨hu, hv⟩ e hea hec
    have he := Nat.dvd_of_mem_unitaryDivisors hea
    have he' := Nat.dvd_of_mem_unitaryDivisors hec
    have heac := gcd_eq_of_dvd_products h he he'
    have hebd : e.gcd b = e.gcd d := by
      exact gcd_eq_of_dvd_products (a := b) (b := a) (c := d) (d := c) h.symm
        (by simpa only [mul_comm] using he) (by simpa only [mul_comm] using he')
    have hga : e.gcd a = 1 := hu _
      (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab hea)
      (heac ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd hec)
    have hgb : e.gcd b = 1 := hv _
      (Nat.gcd_mem_unitaryDivisors_of_mem_mul hab.symm (by rwa [mul_comm]))
      (hebd ▸ Nat.gcd_mem_unitaryDivisors_of_mem_mul hcd.symm (by rwa [mul_comm]))
    simpa only [hga, hgb, one_mul] using
      ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hab).mpr he).symm

private theorem mul_mem_biunitaryDivisors_iff {m n a b : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) :
    a * b ∈ biunitaryDivisors (m * n) ↔
      a ∈ biunitaryDivisors m ∧ b ∈ biunitaryDivisors n := by
  have ha0 := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero hm)
  have hb0 := Nat.pos_of_dvd_of_pos hb (Nat.pos_of_ne_zero hn)
  have hma := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) ha) ha0
  have hnb := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hb) hb0
  simp only [mem_biunitaryDivisors, ha, hb, Nat.mul_dvd_mul ha hb, ne_eq, hm, hn,
    mul_ne_zero hm hn, not_false_eq_true, true_and]
  rw [← Nat.div_mul_div_comm ha hb]
  apply gcdUnitary_mul_eq_one_iff ha0.ne' hb0.ne' hma.ne' hnb.ne'
  rwa [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb]

private theorem sigmaBiunitary_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m.Coprime n) : sigmaBiunitary (m * n) = sigmaBiunitary m * sigmaBiunitary n := by
  simp only [sigmaBiunitary, biunitaryDivisors, sum_filter]
  rw [h.divisors_mul, sum_map]
  change (∑ x ∈ (m.divisors ×ˢ n.divisors).attach,
    if gcdUnitary (x.1.1 * x.1.2) (m * n / (x.1.1 * x.1.2)) = 1
      then x.1.1 * x.1.2 else 0) = _
  rw [sum_attach (f := fun x : ℕ × ℕ =>
    if gcdUnitary (x.1 * x.2) (m * n / (x.1 * x.2)) = 1 then x.1 * x.2 else 0),
    sum_product, sum_mul_sum]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  have ha' := (Nat.mem_divisors.mp ha).1
  have hb' := (Nat.mem_divisors.mp hb).1
  have hi := mul_mem_biunitaryDivisors_iff hm hn h ha' hb'
  simp only [mem_biunitaryDivisors, ha', hb', Nat.mul_dvd_mul ha' hb', ne_eq, hm, hn,
    mul_ne_zero hm hn, not_false_eq_true, true_and] at hi
  change (if gcdUnitary (a * b) (m * n / (a * b)) = 1 then a * b else 0) = _
  simp only [hi]
  by_cases ha'' : gcdUnitary a (m / a) = 1
  · by_cases hb'' : gcdUnitary b (n / b) = 1 <;> simp [ha'', hb'']
  · simp [ha'']

private theorem gcdUnitary_one_left {n : ℕ} (hn : n ≠ 0) : gcdUnitary 1 n = 1 := by
  simp [gcdUnitary, show (1 : ℕ).unitaryDivisors = {1} by decide,
    hn]

private theorem odd_sigmaBiunitary_of_odd_iff {n : ℕ} (hn : Odd n) :
    Odd (sigmaBiunitary n) ↔ n = 1 := by
  have hn0 : n ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hn)
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := (odd_sigmaBiunitary_iff n (Nat.pos_of_ne_zero hn0)).mp hs
    have hk0 : k = 0 := by
      by_contra hk0
      exact (by decide : ¬ Odd (2 : ℕ)) ((Nat.odd_pow_iff hk0).mp (hk ▸ hn))
    simpa only [hk0, pow_zero] using hk
  · intro h
    simpa only [h, sigmaBiunitary_one] using (odd_one : Odd (1 : ℕ))

private theorem gcdUnitary_five_pow_five {k : ℕ} (hk : 2 ≤ k) :
    gcdUnitary (5 ^ k) 5 = 1 := by
  apply (gcdUnitary_eq_one_iff (pow_ne_zero _ (by decide)) (by decide)).mpr
  intro d hd hd'
  change d ∈ (5 ^ 1 : ℕ).unitaryDivisors at hd'
  simp only [Nat.unitaryDivisors_prime_pow (by decide : Nat.Prime 5),
    mem_insert, mem_singleton] at hd hd'
  rcases hd with h | h
  · exact h
  rcases hd' with h' | h'
  · exact h'
  have he := Nat.pow_right_injective (by decide : 1 < (5 : ℕ)) (h.symm.trans h')
  omega

private theorem five_mul_sigmaBiunitary_five_pow_gt {g : ℕ} (hg : 3 ≤ g) :
    6 * 5 ^ g < 5 * sigmaBiunitary (5 ^ g) := by
  have hn : (5 : ℕ) ^ g ≠ 0 := pow_ne_zero _ (by decide)
  have hpow : (5 : ℕ) ^ g = 5 ^ (g - 1) * 5 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ g)]
  have h1 : 1 ∈ biunitaryDivisors (5 ^ g) :=
    mem_biunitaryDivisors.mpr ⟨one_dvd _, hn, by
      simpa only [Nat.div_one] using gcdUnitary_one_left hn⟩
  have htop : 5 ^ g ∈ biunitaryDivisors (5 ^ g) :=
    mem_biunitaryDivisors.mpr ⟨dvd_rfl, hn, by
      rw [Nat.div_self (Nat.pos_of_ne_zero hn), gcdUnitary_comm]
      exact gcdUnitary_one_left hn⟩
  have hprev : 5 ^ (g - 1) ∈ biunitaryDivisors (5 ^ g) :=
    mem_biunitaryDivisors.mpr ⟨⟨5, hpow⟩, hn, by
      rw [hpow, Nat.mul_div_cancel_left _ (pow_pos (by decide : 0 < (5 : ℕ)) _)]
      exact gcdUnitary_five_pow_five (by omega)⟩
  have hsmall : 1 < (5 : ℕ) ^ (g - 1) := Nat.one_lt_pow (by omega) (by decide)
  have hlarge : (5 : ℕ) ^ (g - 1) < 5 ^ g := by
    rw [hpow]
    omega
  have hs : ({1, 5 ^ (g - 1), 5 ^ g} : Finset ℕ) ⊆ biunitaryDivisors (5 ^ g) := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact h1
    · exact hprev
    · exact htop
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => d) hs
    (fun d _ _ => Nat.zero_le d)
  have hbound : 1 + 5 ^ (g - 1) + 5 ^ g ≤ sigmaBiunitary (5 ^ g) := by
    simpa [Finset.sum_insert, hsmall.ne, hlarge.ne, (hsmall.trans hlarge).ne, add_assoc,
      sigmaBiunitary] using hsum
  omega

private theorem eq_five_of_sigmaBiunitary_ratio {m : ℕ} (hm : Odd m)
    (hs : 5 * sigmaBiunitary m = 6 * m) : m = 5 := by
  have hm0 : m ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hm)
  have h5 : 5 ∣ m := (by decide : Nat.Coprime 5 6).dvd_of_dvd_mul_left
    (hs ▸ Nat.dvd_mul_right 5 (sigmaBiunitary m))
  let g := m.factorization 5
  let r := ordCompl[5] m
  have hg : 0 < g := (by decide : Nat.Prime 5).factorization_pos_of_dvd hm0 h5
  have hr0 : r ≠ 0 := (Nat.ordCompl_pos 5 hm0).ne'
  have hmr : 5 ^ g * r = m := Nat.ordProj_mul_ordCompl_eq_self m 5
  have hpr : (5 ^ g).Coprime r :=
    (Nat.coprime_ordCompl (by decide : Nat.Prime 5) hm0).pow_left g
  have hmul := sigmaBiunitary_mul (pow_ne_zero g (by decide : (5 : ℕ) ≠ 0)) hr0 hpr
  have hro : Odd r := Nat.Odd.of_mul_right (hmr ▸ hm)
  have hpo : Odd ((5 : ℕ) ^ g) := (by decide : Odd (5 : ℕ)).pow
  have hpe : Even (sigmaBiunitary (5 ^ g)) := Nat.not_odd_iff_even.mp
    ((not_congr (odd_sigmaBiunitary_of_odd_iff hpo)).mpr
      (Nat.one_lt_pow hg.ne' (by decide : 1 < (5 : ℕ))).ne')
  have hr1 : r = 1 := by
    by_contra hr1
    have hre : Even (sigmaBiunitary r) := Nat.not_odd_iff_even.mp
      ((not_congr (odd_sigmaBiunitary_of_odd_iff hro)).mpr hr1)
    obtain ⟨a, ha⟩ := hpe
    obtain ⟨b, hb⟩ := hre
    have hmul' : sigmaBiunitary m = sigmaBiunitary (5 ^ g) * sigmaBiunitary r := by
      simpa only [hmr] using hmul
    have hme : Even (3 * m) := ⟨5 * a * b, by nlinarith [hmul']⟩
    exact (Nat.not_odd_iff_even.mpr
      ((Nat.even_mul.mp hme).resolve_left (by decide : ¬ Even (3 : ℕ)))) hm
  have hmp : m = 5 ^ g := by simpa only [hr1, mul_one] using hmr.symm
  have hsg : 5 * sigmaBiunitary (5 ^ g) = 6 * 5 ^ g := by simpa only [hmp] using hs
  have hgle : g ≤ 2 := by
    by_contra h
    have := five_mul_sigmaBiunitary_five_pow_gt (by omega : 3 ≤ g)
    omega
  have hg2 : g ≠ 2 := by
    intro h
    have h25 : 5 * sigmaBiunitary 25 = 6 * 25 := by
      simpa only [h, show (5 : ℕ) ^ 2 = 25 by decide] using hsg
    rw [show sigmaBiunitary 25 = 26 by decide] at h25
    omega
  have hg1 : g = 1 := by omega
  simpa only [hg1, pow_one] using hmp

/-- **Biunitary triperfect numbers exactly divisible by $2^4$ and by $3^3$ or $3^4$.** Let $N$ be
a biunitary triperfect number, that is, a positive integer with $\sigma^{**}(N) = 3N$, where
$\sigma^{**}$ is the biunitary divisor sum. If the exact power of $2$ dividing $N$ is $2^4$ and the
exact power of $3$ dividing $N$ is $3^3$ or $3^4$, then $N = 2160$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 14 (`jis-2025-25.4.5-lem-14`). -/
public theorem eq_2160_of_factorization_two_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3)
    (he : N.factorization 2 = 4) (hf4 : N.factorization 3 ≤ 4) : N = 2160 := by
  let a := ordCompl[2] N
  have ha0 : a ≠ 0 := (Nat.ordCompl_pos 2 hN.ne').ne'
  have hna : 16 * a = N := by
    simpa only [a, he, show (2 : ℕ) ^ 4 = 16 by decide] using
      Nat.ordProj_mul_ordCompl_eq_self N 2
  have ha2 : Nat.Coprime 16 a := by
    simpa only [show (2 : ℕ) ^ 4 = 16 by decide] using
      (Nat.coprime_ordCompl Nat.prime_two hN.ne').pow_left 4
  have hao : Odd a := Nat.not_even_iff_odd.mp
    (mt even_iff_two_dvd.mp (Nat.not_dvd_ordCompl Nat.prime_two hN.ne'))
  have ha3 : a.factorization 3 = N.factorization 3 := by
    dsimp only [a]
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne (by decide : (3 : ℕ) ≠ 2)]
  have hsa := sigmaBiunitary_mul (by decide : (16 : ℕ) ≠ 0) ha0 ha2
  rw [hna, sigmaBiunitary_sixteen, hσ] at hsa
  have hsa' : 27 * sigmaBiunitary a = 48 * a := by omega
  let m := ordCompl[3] a
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 3 ha0).ne'
  have ham : 3 ^ N.factorization 3 * m = a := by
    simpa only [m, ha3] using Nat.ordProj_mul_ordCompl_eq_self a 3
  have hmo : Odd m := Nat.Odd.of_mul_right (ham ▸ hao)
  have hm3 : (3 ^ N.factorization 3).Coprime m :=
    (Nat.coprime_ordCompl (by decide : Nat.Prime 3) ha0).pow_left _
  have hsm := sigmaBiunitary_mul
    (pow_ne_zero (N.factorization 3) (by decide : (3 : ℕ) ≠ 0)) hm0 hm3
  rw [ham] at hsm
  rw [hsm, ← ham] at hsa'
  have hcases : N.factorization 3 = 3 ∨ N.factorization 3 = 4 := by omega
  rcases hcases with h3 | h4
  · rw [h3, show (3 : ℕ) ^ 3 = 27 by decide, sigmaBiunitary_twentySeven] at hsa'
    have hm5 : m = 5 := eq_five_of_sigmaBiunitary_ratio hmo (by omega)
    rw [← hna, ← ham, h3, hm5]
    decide
  · rw [h4, show (3 : ℕ) ^ 4 = 81 by decide,
      show sigmaBiunitary 81 = 112 by decide] at hsa'
    have hratio : 7 * sigmaBiunitary m = 9 * m := by omega
    have hso : Odd (sigmaBiunitary m) := Nat.Odd.of_mul_right (by
      rw [hratio]
      exact (by decide : Odd (9 : ℕ)).mul hmo)
    have hm1 := (odd_sigmaBiunitary_of_odd_iff hmo).mp hso
    rw [hm1, sigmaBiunitary_one] at hratio
    omega

end MetaMathlibExt
