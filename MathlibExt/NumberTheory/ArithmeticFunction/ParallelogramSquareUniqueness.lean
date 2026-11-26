/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination

/-!
# Induction steps for the parallelogram identity on squares

A multiplicative function satisfying the parallelogram identity on squares takes the square
value at `p ^ 2 + 1` if it takes square values at the odd prime `p` and at powers of smaller primes.
If `p % 4 = 3`, knowing the values at powers of smaller primes already determines the values at
`p + 2` and `(p + 2) ^ 2`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Parallelogram induction: the value at p² + 1.**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p$ is odd and $f(p) = p^2$, then $f(p^2 + 1) = (p^2 + 1)^2$.

The hypothesis $p \ne 2$ is needed: the function with $f(n) = 0$ if $4 \mid n$, $f(n) = 4$ if
$n \equiv 2 \pmod 4$ and $f(n) = 1$ otherwise satisfies the hypotheses for $p = 2$, but
$f(5) = 1$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 1 (`integers-2024-A108-lem-1`). -/
public theorem parallelogram_multiplicative_sq_add_one (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp2 : p ≠ 2) (hfp : f p = (p : ℂ) ^ 2) :
    f (p ^ 2 + 1) = ((p ^ 2 + 1 : ℕ) : ℂ) ^ 2 := by
  -- Extend the prime-power hypothesis to squares with base below p.
  have hsq (n : ℕ) : n < p → f (n ^ 2) = (n : ℂ) ^ 4 := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow q s hq hs =>
      intro hlt
      have hqp := (Nat.le_self_pow hs.ne' q).trans_lt hlt
      rw [← pow_mul, hind q (s * 2) hq hqp (by omega), Nat.cast_pow, ← pow_mul]
      congr 1
      omega
    | zero => simp
    | one => simp [hf]
    | coprime a b ha hb hab iha ihb =>
      intro hlt
      have ha' := (Nat.le_mul_of_pos_right a (by omega : 0 < b)).trans_lt hlt
      have hb' := (Nat.le_mul_of_pos_left b (by omega : 0 < a)).trans_lt hlt
      rw [mul_pow, hf.map_mul_of_coprime (hab.pow 2 2), iha ha', ihb hb', Nat.cast_mul, mul_pow]
  obtain ⟨k, hpk⟩ := hp.odd_of_ne_two hp2
  have hpgt := hp.two_le
  have hk : 0 < k := by omega
  have hf2 : f 2 = (2 : ℂ) ^ 2 := by
    simpa using hind 2 1 Nat.prime_two (by omega) (by decide)
  -- The difference of the consecutive squares is p, and their sum is odd.
  have hdiff : (k + 1) ^ 2 - k ^ 2 = p := by
    apply Nat.sub_eq_of_eq_add
    rw [hpk]
    ring
  have hsum := hpar (k + 1) k hk (Nat.lt_succ_self k)
  rw [hdiff, hfp, hsq (k + 1) (by omega), hsq k (by omega)] at hsum
  have hcop : Nat.Coprime 2 ((k + 1) ^ 2 + k ^ 2) :=
    Nat.coprime_two_left.mpr ⟨k ^ 2 + k, by ring⟩
  have hfactor : p ^ 2 + 1 = 2 * ((k + 1) ^ 2 + k ^ 2) := by
    rw [hpk]
    ring
  rw [hfactor, hf.map_mul_of_coprime hcop, hf2]
  rw [hpk] at hsum
  push_cast at hsum ⊢
  linear_combination 4 * hsum

private theorem parallelogram_add_two_at_three (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (htwo : ∀ s : ℕ, 1 ≤ s → f (2 ^ s) = (2 : ℂ) ^ (2 * s)) :
    f 5 = 25 ∧ f 25 = 625 := by
  -- Use the small-argument equations from Park's initial system, with the powers of two fixed.
  have h2 := htwo 1 (by decide)
  have h4 := htwo 2 (by decide)
  have h8 := htwo 3 (by decide)
  have h16 := htwo 4 (by decide)
  norm_num at h2 h4 h8 h16
  have h10 : f 10 = 4 * f 5 := by
    rw [show 10 = 2 * 5 by decide, hf.map_mul_of_coprime (by decide), h2]
  have h15 : f 15 = f 3 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 3 5)
  have h24 : f 24 = 64 * f 3 := by
    rw [show 24 = 8 * 3 by decide, hf.map_mul_of_coprime (by decide), h8]
  have h26 : f 26 = 4 * f 13 := by
    rw [show 26 = 2 * 13 by decide, hf.map_mul_of_coprime (by decide), h2]
  have h34 : f 34 = 4 * f 17 := by
    rw [show 34 = 2 * 17 by decide, hf.map_mul_of_coprime (by decide), h2]
  have h36 : f 36 = 16 * f 9 := by
    rw [show 36 = 4 * 9 by decide, hf.map_mul_of_coprime (by decide), h4]
  have h48 : f 48 = 256 * f 3 := by
    rw [show 48 = 16 * 3 by decide, hf.map_mul_of_coprime (by decide), h16]
  have h50 : f 50 = 4 * f 25 := by
    rw [show 50 = 2 * 25 by decide, hf.map_mul_of_coprime (by decide), h2]
  have h85 : f 85 = f 5 * f 17 := hf.map_mul_of_coprime (by decide : Nat.Coprime 5 17)
  have e21 : f 5 + f 3 = 2 * f 4 + 2 * f 1 := hpar 2 1 (by decide) (by decide)
  have e31 : f 10 + f 8 = 2 * f 9 + 2 * f 1 := hpar 3 1 (by decide) (by decide)
  have e32 : f 13 + f 5 = 2 * f 9 + 2 * f 4 := hpar 3 2 (by decide) (by decide)
  have e51 : f 26 + f 24 = 2 * f 25 + 2 * f 1 := hpar 5 1 (by decide) (by decide)
  have e53 : f 34 + f 16 = 2 * f 25 + 2 * f 9 := hpar 5 3 (by decide) (by decide)
  have e41 : f 17 + f 15 = 2 * f 16 + 2 * f 1 := hpar 4 1 (by decide) (by decide)
  have e71 : f 50 + f 48 = 2 * f 49 + 2 * f 1 := hpar 7 1 (by decide) (by decide)
  have e76 : f 85 + f 13 = 2 * f 49 + 2 * f 36 := hpar 7 6 (by decide) (by decide)
  rw [h4, hf.map_one] at e21
  rw [h10, h8, hf.map_one] at e31
  rw [h4] at e32
  rw [h26, h24, hf.map_one] at e51
  rw [h34, h16] at e53
  rw [h15, h16, hf.map_one] at e41
  rw [h50, h48, hf.map_one] at e71
  rw [h85, h36] at e76
  have h3 : f 3 = 34 - f 5 := by linear_combination e21
  have h9 : f 9 = 2 * f 5 + 31 := by linear_combination -e31 / 2
  have h13 : f 13 = 3 * f 5 + 94 := by linear_combination e32 - e31
  have h25 : f 25 = 1275 - 26 * f 5 := by
    linear_combination -e51 / 2 + 2 * e32 - 2 * e31 + 32 * e21
  have h17 : f 17 = 589 - 12 * f 5 := by linear_combination e53 / 4 + h25 / 2 + h9 / 2
  -- The two remaining equations' quadratic terms cancel.
  rw [h3, h17] at e41
  rw [h25, h3] at e71
  rw [h17, h13, h9] at e76
  have h5 : f 5 = 25 := by linear_combination (e76 - e71 - 12 * e41) / 624
  exact ⟨h5, by rw [h25, h5]; norm_num⟩

/-- **Parallelogram induction: the values at p + 2 and (p + 2)².**
Let $f$ be a complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$.
Let $p$ be a prime such that $f(q^s) = q^{2s}$ for every prime $q < p$ and every integer
$s \ge 1$.
If $p \equiv 3 \pmod 4$, then $f(p + 2) = (p + 2)^2$ and $f((p + 2)^2) = (p + 2)^4$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Lemma 2 (`integers-2024-A108-lem-2`). -/
public theorem parallelogram_multiplicative_add_two (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    {p : ℕ} (hp : p.Prime)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hp4 : p % 4 = 3) :
    f (p + 2) = ((p + 2 : ℕ) : ℂ) ^ 2 ∧ f ((p + 2) ^ 2) = ((p + 2 : ℕ) : ℂ) ^ 4 := by
  have hp3 : 3 ≤ p := by omega
  by_cases hthree : p = 3
  · subst p
    have htwo (s : ℕ) (hs : 1 ≤ s) := hind 2 s Nat.prime_two (by decide) hs
    have h := parallelogram_add_two_at_three f hf hpar htwo
    norm_num at h ⊢
    exact h
  have hpgt : 3 < p := lt_of_le_of_ne hp3 (Ne.symm hthree)
  -- Multiplicativity extends the induction hypothesis to numbers with only smaller prime factors.
  have hsmooth (n : ℕ) (hn : ∀ q : ℕ, q.Prime → q ∣ n → q < p) : f n = (n : ℂ) ^ 2 := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp [hf]
    | prime_pow q s hq hs =>
      rw [hind q s hq (hn q hq (dvd_pow_self q hs.ne')) hs, Nat.cast_pow, ← pow_mul, mul_comm s]
    | coprime a b _ _ hab iha ihb =>
      rw [hf.map_mul_of_coprime hab, Nat.cast_mul, mul_pow,
        iha (fun q hq h => hn q hq (dvd_mul_of_dvd_left h b)),
        ihb (fun q hq h => hn q hq (dvd_mul_of_dvd_right h a))]
  have hpow (n k : ℕ) (hn : ∀ q : ℕ, q.Prime → q ∣ n → q < p) :
      f (n ^ k) = (n : ℂ) ^ (k * 2) := by
    rw [hsmooth _ (fun q hq h => hn q hq (hq.dvd_of_dvd_pow h)), Nat.cast_pow, ← pow_mul]
  have hsmall {n : ℕ} (hpos : 0 < n) (hlt : n < p) (q : ℕ) (_ : q.Prime) (hd : q ∣ n) :
      q < p := (Nat.le_of_dvd hpos hd).trans_lt hlt
  by_cases ht : (p + 2).Prime
  swap
  · have hs : ∀ q : ℕ, q.Prime → q ∣ p + 2 → q < p := by
      intro q hq hd
      obtain ⟨k, hk⟩ := hd
      have hk2 : 2 ≤ k := by
        by_contra! hk2
        interval_cases k
        · simp at hk
        · exact ht (by rw [show p + 2 = q by simpa using hk]; exact hq)
      have h := Nat.mul_le_mul_left q hk2
      omega
    exact ⟨hsmooth _ hs, hpow _ 2 hs⟩
  -- In the prime case write p + 2 as a sum of two distinct positive squares.
  obtain ⟨x, y, hxy⟩ := @Nat.Prime.sq_add_sq (p + 2) ⟨ht⟩ (by omega)
  obtain ⟨a, b, hba, hsum⟩ : ∃ a b : ℕ, b ≤ a ∧ a ^ 2 + b ^ 2 = p + 2 := by
    rcases le_total y x with h | h
    · exact ⟨x, y, h, hxy⟩
    · exact ⟨y, x, h, by simpa [add_comm] using hxy⟩
  have ha : 2 ≤ a := by
    by_contra! h
    have ha' : a ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left (show a ≤ 1 by omega) 2
    have hb' : b ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left (show b ≤ 1 by omega) 2
    omega
  have hb : 0 < b := by
    by_contra! h
    have hfactors : a * a = p + 2 := by simpa [show b = 0 by omega, pow_two] using hsum
    exact (Nat.not_prime_mul (by omega : a ≠ 1) (by omega : a ≠ 1)) (hfactors ▸ ht)
  have hlt : b < a := by
    by_contra! h
    have he : b = a := le_antisymm hba h
    rw [he] at hsum
    omega
  have hap : a < p := by
    have := Nat.mul_le_mul_left a ha
    nlinarith
  have hbp : b < p := hlt.trans hap
  let c := a ^ 2 - b ^ 2
  have habsq : b ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
  have hca : c + b ^ 2 = a ^ 2 := Nat.sub_add_cancel habsq.le
  have hcpos : 0 < c := Nat.sub_pos_of_lt habsq
  have hcp : c < p := by
    by_contra! hc
    have hb1 : b = 1 := by nlinarith
    have hprod : (a - 1) * (a + 1) = p := by
      have hsucc : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
      rw [hb1] at hsum
      nlinarith [congrArg (fun x : ℕ => x * (a + 1)) hsucc]
    have ha3 : 3 ≤ a := by
      by_contra! h
      have h2 : a = 2 := by omega
      norm_num [h2] at hprod
      omega
    exact (Nat.not_prime_mul (by omega : a - 1 ≠ 1) (by omega : a + 1 ≠ 1)) (hprod ▸ hp)
  have ha2 := hpow a 2 (hsmall (by omega) hap)
  have hb2 := hpow b 2 (hsmall hb hbp)
  have hc1 := hsmooth c (hsmall hcpos hcp)
  have hc2 := hpow c 2 (hsmall hcpos hcp)
  have hc_cast : (c : ℂ) = (a : ℂ) ^ 2 - (b : ℂ) ^ 2 := by
    dsimp [c]
    rw [Nat.cast_sub habsq.le, Nat.cast_pow, Nat.cast_pow]
  have ht_cast : ((p + 2 : ℕ) : ℂ) = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    rw [← hsum, Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
  have e₁ := hpar a b hb hlt
  rw [hsum, show a ^ 2 - b ^ 2 = c by rfl, hc1, ha2, hb2, hc_cast] at e₁
  have ht1 : f (p + 2) = ((p + 2 : ℕ) : ℂ) ^ 2 := by
    rw [ht_cast]
    linear_combination e₁
  refine ⟨ht1, ?_⟩
  -- Instead of applying the law to the Pythagorean legs (whose difference of squares need not
  -- be smooth), first evaluate a⁴ + b⁴ using a⁴ - b⁴ = c * (p + 2).
  have hcop : (p + 2).Coprime c := ht.coprime_iff_not_dvd.mpr fun h =>
    (Nat.le_of_dvd hcpos h).not_gt (by omega)
  have hdiff : (a ^ 2) ^ 2 - (b ^ 2) ^ 2 = (p + 2) * c := by
    apply Nat.sub_eq_of_eq_add
    rw [← hsum]
    nlinarith [congrArg (fun x : ℕ => (a ^ 2 + b ^ 2) * x) hca]
  have ha4 : f ((a ^ 2) ^ 2) = (a : ℂ) ^ 8 := by
    rw [← pow_mul]
    exact hpow a 4 (hsmall (by omega) hap)
  have hb4 : f ((b ^ 2) ^ 2) = (b : ℂ) ^ 8 := by
    rw [← pow_mul]
    exact hpow b 4 (hsmall hb hbp)
  have e₂ := hpar (a ^ 2) (b ^ 2) (by positivity) habsq
  rw [hdiff, hf.map_mul_of_coprime hcop, ht1, hc1, ha4, hb4, ht_cast, hc_cast] at e₂
  have hsum_odd : Odd ((a ^ 2) ^ 2 + (b ^ 2) ^ 2) := by
    have mod_sq (n : ℕ) : n ^ 2 % 2 = n % 2 := by
      have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
      conv_lhs => rw [Nat.pow_mod]
      rcases h with h | h <;> simp [h]
    rw [Nat.odd_iff, Nat.add_mod, mod_sq (a ^ 2), mod_sq (b ^ 2), ← Nat.add_mod, hsum]
    omega
  have hdouble : (p + 2) ^ 2 + c ^ 2 = 2 * ((a ^ 2) ^ 2 + (b ^ 2) ^ 2) := by
    rw [← hsum]
    nlinarith [congrArg (fun x : ℕ => x ^ 2) hca]
  have hlegs : (p + 2) ^ 2 - c ^ 2 = (2 * a * b) ^ 2 := by
    apply Nat.sub_eq_of_eq_add
    rw [← hsum]
    nlinarith [congrArg (fun x : ℕ => x ^ 2) hca]
  have hlegs_val : f ((2 * a * b) ^ 2) = ((2 * a * b : ℕ) : ℂ) ^ 4 := by
    apply hpow
    intro q hq hd
    rcases hq.dvd_mul.mp hd with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · exact hsmall (by decide) (by omega : 2 < p) q hq h
      · exact hsmall (by omega) hap q hq h
    · exact hsmall hb hbp q hq h
  have htwo : f 2 = (2 : ℂ) ^ 2 := by
    simpa using hind 2 1 Nat.prime_two (by omega) (by decide)
  have e₃ := hpar (p + 2) c hcpos (by omega)
  rw [hdouble, hlegs, hf.map_mul_of_coprime (Nat.coprime_two_left.mpr hsum_odd), htwo,
    hlegs_val, hc2, hc_cast] at e₃
  push_cast at e₃
  rw [ht_cast]
  linear_combination 2 * e₂ - e₃ / 2

end MetaMathlibExt
