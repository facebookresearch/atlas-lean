/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.CohnTwiceSquareLucas
import MathlibExt.NumberTheory.Recurrences.SquareFibonacciLucas

@[expose] public section

namespace MetaMathlibExt

section
/-! # Square and twice-square Fibonacci and Lucas numbers

Source: Refik Keskin and Zafer Yosma, "On Fibonacci and Lucas Numbers of the
Form cx^2", Journal of Integer Sequences 14 (2011), Theorem 2.1, source
lines 129–132,
https://cs.uwaterloo.ca/journals/JIS/VOL14/Keskin/keskin3.tex
complete-source SHA-256
`f0f1dc8d3be32d14f8ad1f44e3c0fcf8c4081345df25ae0e814055b033901ea7`;
raw source-lines 129–132 SHA-256
`c8faa3153ac602a1bfc8d7488b4a14b64315ca1c39ad4ddf97245e574cb203dc`.

The source states: if `Fₙ = x²` then `n = 1, 2, 12`; if `Fₙ = 2x²` then
`n = 3, 6`; if `Lₙ = x²` then `n = 1, 3`; and if `Lₙ = 2x²` then `n = 6`.
The paper attributes the square-Fibonacci classification to J. H. E. Cohn,
"Square Fibonacci numbers, etc.", Fibonacci Quarterly 2.2 (1964), 109–113,
and the Lucas/twice-square classifications to Cohn's related work, including
"Lucas and Fibonacci numbers and some Diophantine equations", Proc. Glasgow
Math. Assoc. 7 (1965), 24–28.

The surrounding paper defines the Fibonacci and Lucas sequences at indices
`0` and `1` and discusses integer indices, but the displayed lists omit the
zero-index exceptions `F₀ = 0` and `L₀ = 2`. Each declaration below therefore
takes `(hn : 0 < n)` to formalize the intended positive-natural-index form.

`Nat.fib` is the Fibonacci sequence and `MetaMathlibExt.lucasNumber` is the
repository's canonical Lucas-number sequence; no parallel `Fₙ₋₁ + Fₙ₊₁`
encoding is used. -/

private theorem lucasNumber_add_fib (n : ℕ) : lucasNumber n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have hL : lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := rfl
    have hF : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hF2 : Nat.fib (n + 1 + 1 + 1)
        = Nat.fib (n + 1) + Nat.fib (n + 1 + 1) :=
      Nat.fib_add_two (n := n + 1)
    have : n + 2 + 1 = n + 1 + 1 + 1 := by omega
    rw [hL, hF, this, hF2]
    omega

private theorem fib_succ_sq_sub_fib_mul_sub_fib_sq (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ)) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ)
      - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hF : ((Nat.fib (n + 2) : ℤ)) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    rw [show n + 1 + 1 = n + 2 from rfl, hF]
    rw [pow_succ]
    linear_combination -ih

private theorem fib_two_mul_eq_fib_mul_lucasNumber (n : ℕ) :
    Nat.fib (2 * n) = Nat.fib n * lucasNumber n := by
  have h := Nat.fib_two_mul n
  have hN1 := lucasNumber_add_fib n
  have hsub : lucasNumber n = 2 * Nat.fib (n + 1) - Nat.fib n := by omega
  rw [hsub, h]

private theorem fib_add_two_mul_add_neg_one_pow_mul (m k : ℕ) :
    ((Nat.fib (m + 2 * k) : ℤ)) + (-1 : ℤ) ^ k * (Nat.fib m : ℤ)
      = (Nat.fib (m + k) : ℤ) * (lucasNumber k : ℤ) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    have h0 : 0 + 2 * k = 2 * k := by omega
    have h1 : (0 : ℕ) + k = k := by omega
    rw [h0, h1]
    simp only [Nat.fib_zero, Nat.cast_zero, mul_zero, add_zero]
    have hN2 := fib_two_mul_eq_fib_mul_lucasNumber k
    have : ((Nat.fib (2 * k) : ℤ)) = (Nat.fib k : ℤ) * (lucasNumber k : ℤ) := by
      exact_mod_cast hN2
    exact this
  | one =>
    have h0 : 1 + 2 * k = 2 * k + 1 := by omega
    have h1 : 1 + k = k + 1 := by omega
    rw [h0, h1]
    have hF := Nat.fib_two_mul_add_one k
    have hN1 : ((lucasNumber k : ℤ)) = 2 * (Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ) := by
      have h := lucasNumber_add_fib k
      have hc : ((lucasNumber k : ℤ)) + (Nat.fib k : ℤ) = 2 * (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast h
      linarith
    have hN3 := fib_succ_sq_sub_fib_mul_sub_fib_sq k
    have hcast : ((Nat.fib (2 * k + 1) : ℤ)) = (Nat.fib (k + 1) : ℤ) ^ 2 + (Nat.fib k : ℤ) ^ 2 := by
      exact_mod_cast hF
    rw [hcast]
    simp only [Nat.fib_one, Nat.cast_one]
    rw [hN1]
    linear_combination -hN3
  | more m ih1 ih2 =>
    have e1 : m + 2 + 2 * k = (m + 2 * k) + 2 := by omega
    have e2 : m + 2 + k = (m + k) + 2 := by omega
    rw [e1, e2]
    have r1 : ((Nat.fib ((m + 2 * k) + 2) : ℤ))
        = (Nat.fib (m + 2 * k) : ℤ) + (Nat.fib ((m + 2 * k) + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    have r2 : ((Nat.fib (m + 2) : ℤ))
        = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    have r3 : ((Nat.fib ((m + k) + 2) : ℤ))
        = (Nat.fib (m + k) : ℤ) + (Nat.fib ((m + k) + 1) : ℤ) := by
      exact_mod_cast Nat.fib_add_two
    have e3 : (m + 2 * k) + 1 = (m + 1) + 2 * k := by omega
    have e4 : (m + k) + 1 = (m + 1) + k := by omega
    rw [e3] at r1
    rw [e4] at r3
    rw [r1, r2, r3]
    linear_combination ih1 + ih2

private theorem lucasNumber_dvd_fib_add_two_mul_mul_sub (k : ℕ) (hk : Even k) (m j : ℕ) :
    ((lucasNumber k : ℤ)) ∣ (Nat.fib (m + 2 * k * j) : ℤ) - (-1 : ℤ) ^ j * (Nat.fib m : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hidx : m + 2 * k * (j + 1) = (m + 2 * k * j) + 2 * k := by ring
    rw [hidx]
    have hN4 := fib_add_two_mul_add_neg_one_pow_mul (m + 2 * k * j) k
    have hk1 : (-1 : ℤ) ^ k = 1 := hk.neg_one_pow
    rw [hk1, one_mul] at hN4
    have hpow : (-1 : ℤ) ^ (j + 1) = (-1 : ℤ) ^ j * (-1) := by rw [pow_succ]
    have hdecomp : ((Nat.fib ((m + 2 * k * j) + 2 * k) : ℤ)) - (-1 : ℤ) ^ (j + 1) * (Nat.fib m : ℤ)
        = ((lucasNumber k : ℤ)) * (Nat.fib (m + 2 * k * j + k) : ℤ)
          - (((Nat.fib (m + 2 * k * j) : ℤ)) - (-1 : ℤ) ^ j * (Nat.fib m : ℤ)) := by
      rw [hpow]
      linear_combination hN4
    rw [hdecomp]
    exact dvd_sub (dvd_mul_right _ _) ih

private theorem exists_eq_three_pow_mul_even_not_dvd (s : ℕ) (hs0 : s ≠ 0) (hseven : Even s) :
    ∃ r k : ℕ, s = 3 ^ r * k ∧ Even k ∧ ¬ 3 ∣ k := by
  obtain ⟨r, k, hk3, hsk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hs0 3 (by norm_num)
  refine ⟨r, k, hsk, ?_, hk3⟩
  have h2dvd : 2 ∣ s := even_iff_two_dvd.mp hseven
  rw [hsk] at h2dvd
  have hcop : Nat.Coprime 2 (3 ^ r) := by
    apply Nat.Coprime.pow_right
    decide
  have := (Nat.Coprime.dvd_mul_left hcop).mp h2dvd
  exact even_iff_two_dvd.mpr this

private theorem nat_gcd_fib_lucasNumber_dvd_two (m : ℕ) :
    Nat.gcd (Nat.fib m) (lucasNumber m) ∣ 2 := by
  set g := Nat.gcd (Nat.fib m) (lucasNumber m) with hg
  have h1 : g ∣ Nat.fib m := Nat.gcd_dvd_left _ _
  have h2 : g ∣ lucasNumber m := Nat.gcd_dvd_right _ _
  have hN1 := lucasNumber_add_fib m
  have hdiv : g ∣ 2 * Nat.fib (m + 1) := by
    have := dvd_add h2 h1
    rw [hN1] at this
    exact this
  have hcop : Nat.Coprime g (Nat.fib (m + 1)) :=
    (Nat.Coprime.coprime_dvd_left h1 (Nat.fib_coprime_fib_succ m))
  exact (Nat.Coprime.dvd_of_dvd_mul_right hcop hdiv)

-- N9
private theorem lucasNumber_dvd_fib_add_one_of_mod_four_eq_one (n : ℕ)
    (hn : n % 4 = 1) (hn1 : n ≠ 1) :
    ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧ ((lucasNumber k : ℤ)) ∣ (Nat.fib n : ℤ) + 1 := by
  set s := (n - 1) / 2 with hs
  have hn5 : 5 ≤ n := by omega
  have hs0 : s ≠ 0 := by omega
  have hseven : Even s := by
    rw [hs]
    have hdiv : n = 4 * (n / 4) + 1 := by omega
    have hs_eq : s = 2 * (n / 4) := by omega
    rw [← hs, hs_eq]
    exact even_two_mul _
  have hn_eq : n = 1 + 2 * s := by omega
  obtain ⟨r, k, hsk, hke, hk3⟩ := exists_eq_three_pow_mul_even_not_dvd s hs0 hseven
  refine ⟨k, hke, hk3, ?_⟩
  have hn_eq2 : n = 1 + 2 * k * 3 ^ r := by
    rw [hsk] at hn_eq
    ring_nf at hn_eq ⊢
    omega
  have hN5 := lucasNumber_dvd_fib_add_two_mul_mul_sub k hke 1 (3 ^ r)
  have hodd : Odd (3 ^ r) := Odd.pow (by decide : Odd 3)
  have hpow : (-1 : ℤ) ^ (3 ^ r) = -1 := hodd.neg_one_pow
  rw [hpow] at hN5
  -- hN5 : L_k ∣ F_{1+2*k*3^r} - (-1)*F_1
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at hN5
  have hidx : 1 + 2 * k * 3 ^ r = n := by omega
  rw [hidx] at hN5
  -- hN5 : L_k ∣ F_n - (-1)*1 = F_n + 1
  have : ((Nat.fib n : ℤ)) - (-1 : ℤ) = (Nat.fib n : ℤ) + 1 := by ring
  rw [this] at hN5
  exact hN5

private theorem lucasNumber_add_six (i : ℕ) :
    lucasNumber (i + 6) = 8 * lucasNumber (i + 1) + 5 * lucasNumber i := by
  have h2 : lucasNumber (i + 2) = lucasNumber (i + 1) + lucasNumber i := rfl
  have h3 : lucasNumber (i + 3) = lucasNumber (i + 2) + lucasNumber (i + 1) := rfl
  have h4 : lucasNumber (i + 4) = lucasNumber (i + 3) + lucasNumber (i + 2) := rfl
  have h5 : lucasNumber (i + 5) = lucasNumber (i + 4) + lucasNumber (i + 3) := rfl
  have h6 : lucasNumber (i + 6) = lucasNumber (i + 5) + lucasNumber (i + 4) := rfl
  omega

private theorem lucasNumber_six_mul_add (q r : ℕ) :
    lucasNumber (6 * q + r) % 4 = lucasNumber r % 4 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : 6 * (q + 1) + r = (6 * q + r) + 6 := by omega
    rw [this]
    have h6 : ∀ i, lucasNumber (i + 6) % 4 = lucasNumber i % 4 := by
      intro i
      rw [lucasNumber_add_six i]
      omega
    rw [h6]
    exact ih

private theorem lucasNumber_mod_four_of_even_of_not_three_dvd (k : ℕ)
    (hke : Even k) (hk3 : ¬ 3 ∣ k) :
    lucasNumber k % 4 = 3 := by
  have hdecomp : k = 6 * (k / 6) + k % 6 := (Nat.div_add_mod k 6).symm
  rw [hdecomp, lucasNumber_six_mul_add]
  have hmod : k % 6 = 2 ∨ k % 6 = 4 := by
    obtain ⟨t, ht⟩ := hke
    have h1 : k % 2 = 0 := by omega
    have h2 : k % 3 ≠ 0 := by
      intro hc
      apply hk3
      omega
    omega
  rcases hmod with h | h
  · rw [h]; decide
  · rw [h]; decide

private theorem not_dvd_sq_add_one_of_mod_four_eq_three (b : ℕ) (hb : b % 4 = 3) (y : ℤ)
    (hdiv : ((b : ℤ)) ∣ y ^ 2 + 1) : False := by
  have hbodd : Odd b := by
    rw [Nat.odd_iff]
    omega
  have hmod : (-1 : ℤ) ≡ y ^ 2 [ZMOD (b : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have : y ^ 2 - (-1 : ℤ) = y ^ 2 + 1 := by ring
    rw [this]
    exact hdiv
  have heq : (-1 : ℤ) % (b : ℤ) = (y ^ 2) % (b : ℤ) := hmod.eq
  have hjac : jacobiSym (-1 : ℤ) b = jacobiSym (y ^ 2) b := jacobiSym.mod_left' heq
  have hleft : jacobiSym (-1 : ℤ) b = -1 := by
    rw [jacobiSym.at_neg_one hbodd]
    exact ZMod.χ₄_nat_three_mod_four hb
  have hright : jacobiSym (y ^ 2 : ℤ) b = 0 ∨ jacobiSym (y ^ 2 : ℤ) b = 1 := by
    rw [jacobiSym.pow_left]
    have htri := jacobiSym.trichotomy y b
    rcases htri with h0 | h1 | hm1
    · simp [h0]
    · simp [h1]
    · simp [hm1]
  rw [hleft] at hjac
  rcases hright with h0 | h1
  · omega
  · omega

private theorem lucasNumber_dvd_fib_add_one_of_mod_four_eq_three (n : ℕ) (hn : n % 4 = 3) :
    ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧ ((lucasNumber k : ℤ)) ∣ (Nat.fib n : ℤ) + 1 := by
  set s := (n + 1) / 2 with hs
  have hs0 : s ≠ 0 := by omega
  have hseven : Even s := by
    have hdiv : n = 4 * (n / 4) + 3 := by omega
    have hs_eq : s = 2 * (n / 4) + 2 := by omega
    rw [hs_eq]
    exact ⟨n / 4 + 1, by ring⟩
  have hn_eq : n + 1 = 2 * s := by omega
  obtain ⟨r, k, hsk, hke, hk3⟩ := exists_eq_three_pow_mul_even_not_dvd s hs0 hseven
  refine ⟨k, hke, hk3, ?_⟩
  have hn1 : n + 1 = 0 + 2 * k * 3 ^ r := by
    rw [hsk] at hn_eq
    ring_nf at hn_eq ⊢
    omega
  have hn2 : n + 2 = 1 + 2 * k * 3 ^ r := by omega
  have hodd : Odd (3 ^ r) := Odd.pow (by decide : Odd 3)
  have hpow : (-1 : ℤ) ^ (3 ^ r) = -1 := hodd.neg_one_pow
  have hN5_0 := lucasNumber_dvd_fib_add_two_mul_mul_sub k hke 0 (3 ^ r)
  have hN5_1 := lucasNumber_dvd_fib_add_two_mul_mul_sub k hke 1 (3 ^ r)
  rw [hpow] at hN5_0 hN5_1
  simp only [Nat.fib_zero, Nat.cast_zero, mul_zero, sub_zero] at hN5_0
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at hN5_1
  -- rewrite indices to n+1 and n+2
  have e0 : 0 + 2 * k * 3 ^ r = n + 1 := by omega
  have e1 : 1 + 2 * k * 3 ^ r = n + 2 := by omega
  rw [e0] at hN5_0
  rw [e1] at hN5_1
  -- hN5_0 : L_k ∣ F_{n+1}, hN5_1 : L_k ∣ F_{n+2} - -1
  have hF : ((Nat.fib (n + 2) : ℤ)) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
    exact_mod_cast Nat.fib_add_two
  have h1 : ((Nat.fib (n + 2) : ℤ)) - (-1 : ℤ) = (Nat.fib n : ℤ) + 1 + (Nat.fib (n + 1) : ℤ) := by
    rw [hF]; ring
  -- F_n + 1 = (F_{n+2} - -1) - F_{n+1}
  have hdecomp : ((Nat.fib n : ℤ)) + 1
      = (((Nat.fib (n + 2) : ℤ)) - (-1 : ℤ)) - (Nat.fib (n + 1) : ℤ) := by
    rw [hF]; ring
  rw [hdecomp]
  exact dvd_sub hN5_1 hN5_0

private theorem fib_odd_ne_sq (n x : ℕ) (hodd : Odd n) (hn1 : n ≠ 1)
    (h : Nat.fib n = x ^ 2) : False := by
  have hmod : n % 4 = 1 ∨ n % 4 = 3 := by
    obtain ⟨t, ht⟩ := hodd
    omega
  obtain ⟨k, hke, hk3, hdiv⟩ :
      ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧ ((lucasNumber k : ℤ)) ∣ (Nat.fib n : ℤ) + 1 := by
    rcases hmod with h1 | h3
    · obtain ⟨k, hke, hk3, hd⟩ := lucasNumber_dvd_fib_add_one_of_mod_four_eq_one n h1 hn1
      exact ⟨k, hke, hk3, hd⟩
    · obtain ⟨k, hke, hk3, hd⟩ := lucasNumber_dvd_fib_add_one_of_mod_four_eq_three n h3
      exact ⟨k, hke, hk3, hd⟩
  have hLmod : lucasNumber k % 4 = 3 :=
    lucasNumber_mod_four_of_even_of_not_three_dvd k hke hk3
  -- cast h to Z: F_n = x^2 in Z, so L_k ∣ x^2+1
  have hcast : ((Nat.fib n : ℤ)) = (x : ℤ) ^ 2 := by
    exact_mod_cast h
  have hdiv2 : ((lucasNumber k : ℤ)) ∣ (x : ℤ) ^ 2 + 1 := by
    rw [← hcast]
    exact hdiv
  exact not_dvd_sq_add_one_of_mod_four_eq_three (lucasNumber k) hLmod (x : ℤ) hdiv2

private theorem eq_gcd_mul_sq_of_mul_eq_sq (a b x : ℕ) (h : a * b = x ^ 2) :
    ∃ c : ℕ, b = Nat.gcd a b * c ^ 2 := by
  obtain ⟨a', b', hcop, ha, hb⟩ := Nat.exists_coprime a b
  set g := Nat.gcd a b with hg
  by_cases hg0 : g = 0
  · -- then b = 0
    have hb0 : b = 0 := by rw [hb, hg0, mul_zero]
    exact ⟨0, by rw [hb0, hg0, zero_mul]⟩
  · -- g > 0
    have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
    -- a'*g * (b'*g) = x^2
    have hprod : (a' * g) * (b' * g) = x ^ 2 := by rw [← ha, ← hb]; exact h
    have hgsq_dvd : g ^ 2 ∣ x ^ 2 := by
      refine ⟨a' * b', ?_⟩
      calc x ^ 2 = (a' * g) * (b' * g) := hprod.symm
        _ = g ^ 2 * (a' * b') := by ring
    have hg_dvd : g ∣ x := (Nat.pow_dvd_pow_iff (by norm_num : (2:ℕ) ≠ 0)).mp hgsq_dvd
    obtain ⟨y, rfl⟩ := hg_dvd
    -- g*y squared = ...
    have hcancel : b' * a' = y ^ 2 := by
      have h1 : g ^ 2 * (b' * a') = g ^ 2 * y ^ 2 := by
        linear_combination hprod
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < g ^ 2) h1
    -- b' * a' = y^2 with coprime => b' is square
    have hcop' : Nat.Coprime b' a' := hcop.symm
    have hunit : IsUnit (b'.gcd a') := by
      rw [Nat.isUnit_iff]
      exact Nat.Coprime.gcd_eq_one hcop'
    have hmul : b' * a' = y ^ 2 := hcancel
    obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow hunit hmul
    exact ⟨c, by rw [hb, hc, mul_comm]⟩

private theorem fib_two_mul_eq_sq_of_helpers (m x : ℕ) (hm : 0 < m)
    (h : Nat.fib (2 * m) = x ^ 2) : m = 1 ∨ m = 6 := by
  have hN2 := fib_two_mul_eq_fib_mul_lucasNumber m
  rw [hN2] at h
  obtain ⟨c, hc⟩ := eq_gcd_mul_sq_of_mul_eq_sq (Nat.fib m) (lucasNumber m) x h
  have hg := nat_gcd_fib_lucasNumber_dvd_two m
  have hcases := (Nat.dvd_prime Nat.prime_two).mp hg
  rcases hcases with hg1 | hg2
  · have hL : lucasNumber m = c ^ 2 := by rw [hc, hg1, one_mul]
    have hm13 := cohn_square_lucas m c hm hL
    rcases hm13 with h1 | h3
    · left; exact h1
    · exfalso
      have hcontra : Nat.gcd (Nat.fib m) (lucasNumber m) = 2 := by
        rw [h3]; decide
      omega
  · have hL : lucasNumber m = 2 * c ^ 2 := by rw [hc, hg2]
    have h6 := cohn_twice_square_lucas m c hm hL
    right; exact h6

/-- **Cohn's theorem on square Fibonacci numbers.** Let $F_n$ denote the Fibonacci numbers,
with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. If $n$ and $x$ are natural numbers
with $n \ge 1$ and $F_n = x^2$, then $n \in \{1, 2, 12\}$.

This is the first claim of Theorem 2.1 of Keskin and Yosma.

Proves `Wanted` entry `cohn_square_fibonacci`.
-/
theorem cohn_square_fibonacci (n x : ℕ) (hn : 0 < n)
    (h : Nat.fib n = x ^ 2) : n = 1 ∨ n = 2 ∨ n = 12 := by
  rcases Nat.even_or_odd n with heven | hodd
  · -- even case: n = 2m via the even-index helper
    obtain ⟨m, hm_eq⟩ := heven
    have hm : 0 < m := by omega
    have h2eq : 2 * m = n := by omega
    have h2 : Nat.fib (2 * m) = x ^ 2 := by rw [h2eq]; exact h
    have hmain := fib_two_mul_eq_sq_of_helpers m x hm h2
    rcases hmain with h1 | h6
    · subst h1
      right; left; omega
    · subst h6
      right; right; omega
  · -- odd case via the odd-index helper
    by_cases hn1 : n = 1
    · left; exact hn1
    · exact (fib_odd_ne_sq n x hodd hn1 h).elim

end
end MetaMathlibExt
