/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.Recurrences.SquareFibonacciLucas
public import MathlibExt.NumberTheory.Recurrences.CohnTwiceSquareLucas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
      rw [hL, Nat.fib_add_two]
      have h1 : n + 2 + 1 = (n + 1) + 2 := by omega
      rw [h1, Nat.fib_add_two]
      omega

private theorem fib_two_mul_eq_fib_mul_lucasNumber (n : ℕ) :
    Nat.fib (2 * n) = Nat.fib n * lucasNumber n := by
  have h := Nat.fib_two_mul n
  have hN1 := lucasNumber_add_fib n
  have hL : lucasNumber n = 2 * Nat.fib (n + 1) - Nat.fib n := by omega
  rw [hL, h]

private theorem fib_succ_sq_sub_fib_mul_sub_fib_sq (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 1) : ℤ) -
      (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hfib : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have h1 : ((Nat.fib (n + 1 + 1) : ℤ)) = (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
        exact_mod_cast hfib
      rw [h1]
      linear_combination -ih

-- N4
private theorem fib_add_two_mul_add_neg_one_pow_mul (m k : ℕ) :
    (Nat.fib (m + 2 * k) : ℤ) + (-1) ^ k * (Nat.fib m : ℤ)
      = (Nat.fib (m + k) : ℤ) * (lucasNumber k : ℤ) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      have hN2 := fib_two_mul_eq_fib_mul_lucasNumber k
      have hidx0 : 0 + 2 * k = 2 * k := by omega
      have hidx1 : 0 + k = k := by omega
      have hcast : ((Nat.fib (0 + 2 * k) : ℕ) : ℤ) = ((Nat.fib (2 * k) : ℕ) : ℤ) := by
        rw [hidx0]
      have hmk : ((Nat.fib (0 + k) : ℕ) : ℤ) = ((Nat.fib k : ℕ) : ℤ) := by
        rw [hidx1]
      have hthis :
          ((Nat.fib (2 * k) : ℕ) : ℤ)
            = ((Nat.fib k : ℕ) : ℤ) * ((lucasNumber k : ℕ) : ℤ) := by
        exact_mod_cast hN2
      simp only [Nat.fib_zero, Nat.cast_zero, mul_zero, add_zero]
      rw [hcast, hmk]
      exact hthis
  | one =>
      have hfib := Nat.fib_two_mul_add_one k
      have hN1 := lucasNumber_add_fib k
      have hN1z : (lucasNumber k : ℤ) = 2 * (Nat.fib (k + 1) : ℤ) - (Nat.fib k : ℤ) := by
        have h2 : ((lucasNumber k : ℤ) + (Nat.fib k : ℤ) = 2 * (Nat.fib (k + 1) : ℤ)) := by
          exact_mod_cast hN1
        linarith
      have hCass := fib_succ_sq_sub_fib_mul_sub_fib_sq k
      have idx1 : 1 + 2 * k = 2 * k + 1 := by omega
      have idx2 : 1 + k = k + 1 := by omega
      have hcast : ((Nat.fib (1 + 2 * k) : ℕ) : ℤ) = ((Nat.fib (2 * k + 1) : ℕ) : ℤ) := by
        rw [idx1]
      have hmk : ((Nat.fib (1 + k) : ℕ) : ℤ) = ((Nat.fib (k + 1) : ℕ) : ℤ) := by
        rw [idx2]
      rw [hcast, hfib]
      push_cast
      rw [hmk, hN1z]
      have hF1 : ((Nat.fib 1 : ℕ) : ℤ) = 1 := by decide
      rw [hF1, mul_one]
      linear_combination -hCass
  | more m ih1 ih2 =>
      have e1 : m + 2 + 2 * k = (m + 2 * k) + 2 := by omega
      have e3 : m + 2 + k = (m + k) + 2 := by omega
      have e5 : (m + 2 * k) + 1 = m + 1 + 2 * k := by omega
      have e6 : (m + k) + 1 = m + 1 + k := by omega
      have e7 : m + 2 = m + 1 + 1 := by omega
      have f1 : Nat.fib (m + 2 + 2 * k) = Nat.fib (m + 2 * k) + Nat.fib (m + 1 + 2 * k) := by
        conv_lhs => rw [e1]
        rw [Nat.fib_add_two, e5]
      have f2 : Nat.fib (m + 2 + k) = Nat.fib (m + k) + Nat.fib (m + 1 + k) := by
        conv_lhs => rw [e3]
        rw [Nat.fib_add_two, e6]
      have f3 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      have g1 : ((Nat.fib (m + 2 + 2 * k) : ℕ) : ℤ)
          = (Nat.fib (m + 2 * k) : ℤ) + (Nat.fib (m + 1 + 2 * k) : ℤ) := by exact_mod_cast f1
      have g2 : ((Nat.fib (m + 2 + k) : ℕ) : ℤ)
          = (Nat.fib (m + k) : ℤ) + (Nat.fib (m + 1 + k) : ℤ) := by exact_mod_cast f2
      have g3 : ((Nat.fib (m + 2) : ℕ) : ℤ) =
          (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
        exact_mod_cast f3
      rw [g1, g2, g3]
      linear_combination ih1 + ih2

-- N5
private theorem lucasNumber_dvd_fib_add_two_mul_mul_sub (k : ℕ) (hk : Even k) (m j : ℕ) :
    ((lucasNumber k : ℕ) : ℤ) ∣ (Nat.fib (m + 2 * k * j) : ℤ) - (-1) ^ j * (Nat.fib m : ℤ) := by
  have hk1 : ((-1 : ℤ)) ^ k = 1 := hk.neg_one_pow
  induction j with
  | zero => simp
  | succ j ih =>
      have hN4 := fib_add_two_mul_add_neg_one_pow_mul (m + 2 * k * j) k
      have eA : (m + 2 * k * j) + 2 * k = m + 2 * k * (j + 1) := by ring
      have eB : (m + 2 * k * j) + k = m + 2 * k * j + k := by ring
      rw [eA, hk1, one_mul] at hN4
      have hpow : ((-1 : ℤ)) ^ (j + 1) = -((-1) ^ j) := by ring
      have hmem : ((lucasNumber k : ℕ) : ℤ) ∣
          ((Nat.fib (m + 2 * k * j + k) : ℤ) * (lucasNumber k : ℤ)) :=
        dvd_mul_left _ _
      have key : (Nat.fib (m + 2 * k * (j + 1)) : ℤ) - (-1) ^ (j + 1) * (Nat.fib m : ℤ)
          = ((Nat.fib (m + 2 * k * j + k) : ℤ) * (lucasNumber k : ℤ))
          - ((Nat.fib (m + 2 * k * j) : ℤ) - (-1) ^ j * (Nat.fib m : ℤ)) := by
        rw [hpow]
        linear_combination hN4
      rw [key]
      exact dvd_sub hmem ih

-- N6 helper: six-step closed form
private theorem lucasNumber_add_six (i : ℕ) :
    lucasNumber (i + 6) = 8 * lucasNumber (i + 1) + 5 * lucasNumber i := by
  have h1 : lucasNumber (i + 6) = lucasNumber (i + 5) + lucasNumber (i + 4) := rfl
  have h2 : lucasNumber (i + 5) = lucasNumber (i + 4) + lucasNumber (i + 3) := rfl
  have h3 : lucasNumber (i + 4) = lucasNumber (i + 3) + lucasNumber (i + 2) := rfl
  have h4 : lucasNumber (i + 3) = lucasNumber (i + 2) + lucasNumber (i + 1) := rfl
  have h5 : lucasNumber (i + 2) = lucasNumber (i + 1) + lucasNumber i := rfl
  omega

private theorem lucasNumber_add_six_mod_four (i : ℕ) :
    lucasNumber (i + 6) % 4 = lucasNumber i % 4 := by
  have h := lucasNumber_add_six i
  omega

private theorem lucasNumber_period_aux (q r : ℕ) :
    lucasNumber (6 * q + r) % 4 = lucasNumber r % 4 := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h : 6 * (q + 1) + r = (6 * q + r) + 6 := by ring
      rw [h]
      have h2 : (6 * q + r) + 6 = (6 * q + r) + 6 := rfl
      have hper := lucasNumber_add_six_mod_four (6 * q + r)
      have hidx : (6 * q + r) + 6 = (6 * q + r) + 6 := rfl
      rw [show (6 * q + r) + 6 = (6 * q + r) + 6 from rfl] at hper
      rw [hper, ih]

-- N6
private theorem lucasNumber_mod_four_of_even_of_not_three_dvd (k : ℕ) (hk : Even k) (h3 : ¬ 3 ∣ k) :
    lucasNumber k % 4 = 3 := by
  have hmod6 : k % 6 = 2 ∨ k % 6 = 4 := by
    have hev : k % 2 = 0 := Nat.even_iff.mp hk
    have h6lt : k % 6 < 6 := Nat.mod_lt _ (by decide)
    have h32 : (k % 6) % 2 = 0 := by omega
    have h33 : ¬ (k % 6) % 3 = 0 := by
      intro hc
      apply h3
      have := Nat.mod_mod_of_dvd k (by decide : 3 ∣ 6)
      omega
    omega
  have hdecomp : 6 * (k / 6) + k % 6 = k := by omega
  conv_lhs => rw [← hdecomp]
  rw [lucasNumber_period_aux]
  rcases hmod6 with h | h <;> rw [h] <;> decide

-- N7
private theorem not_dvd_sq_add_one_of_mod_four_eq_three (b : ℕ) (hb : b % 4 = 3) (y : ℤ) :
    ¬ ((b : ℤ) ∣ y ^ 2 + 1) := by
  intro hdvd
  have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
  have hmod : y ^ 2 ≡ (-1) [ZMOD (b : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hneg : ((-1 : ℤ) - y ^ 2) = -(y ^ 2 + 1) := by ring
    rw [hneg]
    exact dvd_neg.mpr hdvd
  have heq : y ^ 2 % ((b : ℤ)) = (-1) % ((b : ℤ)) := hmod.eq
  have hjac : jacobiSym (y ^ 2) b = jacobiSym (-1) b := jacobiSym.mod_left' heq
  have hleft : jacobiSym (-1) b = -1 := by
    rw [jacobiSym.at_neg_one hbodd]
    exact ZMod.χ₄_nat_three_mod_four hb
  have hright : jacobiSym (y ^ 2) b = jacobiSym y b ^ 2 := jacobiSym.pow_left y 2 b
  rw [hright, hleft] at hjac
  rcases jacobiSym.trichotomy y b with h | h | h <;> rw [h] at hjac <;> norm_num at hjac

-- N8
private theorem exists_eq_three_pow_mul_even_not_dvd (s : ℕ) (hs0 : s ≠ 0) (hsev : Even s) :
    ∃ r k : ℕ, s = 3 ^ r * k ∧ Even k ∧ ¬ 3 ∣ k := by
  obtain ⟨r, k, hk3, hsk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hs0 3 (by decide)
  refine ⟨r, k, hsk, ?_, hk3⟩
  have h2dvd : 2 ∣ s := even_iff_two_dvd.mp hsev
  rw [hsk] at h2dvd
  have h23 : Nat.Coprime 2 3 := by decide
  have hcop : Nat.Coprime 2 (3 ^ r) := h23.pow_right r
  have hk2 : 2 ∣ k := (hcop.dvd_mul_left).mp h2dvd
  exact even_iff_two_dvd.mpr hk2

-- N9
private theorem lucasNumber_dvd_fib_add_two_of_mod_four_eq_three
    (n : ℕ) (hn : n % 4 = 3) (hn3 : n ≠ 3) :
    ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧
      ((lucasNumber k : ℕ) : ℤ) ∣ (Nat.fib n : ℤ) + 2 := by
  have hn43 : n = 4 * (n / 4) + 3 := by omega
  set q := n / 4 with hqdef
  have hnq : n = 4 * q + 3 := hn43
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0] at hnq
    simp only [mul_zero, zero_add] at hnq
    exact hn3 hnq
  set s := 2 * q with hsdef
  have hs_eq : n = 3 + 2 * s := by omega
  have hs0 : s ≠ 0 := by omega
  have hsev : Even s := ⟨q, by omega⟩
  obtain ⟨r, k, hsk, hkev, hk3⟩ := exists_eq_three_pow_mul_even_not_dvd s hs0 hsev
  refine ⟨k, hkev, hk3, ?_⟩
  have h3odd : Odd (3 ^ r : ℕ) := (by decide : Odd (3 : ℕ)).pow
  have hjneg : ((-1 : ℤ)) ^ (3 ^ r) = -1 := h3odd.neg_one_pow
  have hN5 := lucasNumber_dvd_fib_add_two_mul_mul_sub k hkev 3 (3 ^ r)
  have hF3 : Nat.fib 3 = 2 := by decide
  have hcastF3 : ((Nat.fib 3 : ℕ) : ℤ) = 2 := by exact_mod_cast hF3
  have h2s : 2 * k * (3 ^ r) = 2 * s := by rw [hsk]; ring
  have hidx : 3 + 2 * k * (3 ^ r) = n := by rw [h2s]; omega
  rw [hjneg, hcastF3] at hN5
  have hcast : ((Nat.fib (3 + 2 * k * (3 ^ r)) : ℕ) : ℤ) = ((Nat.fib n : ℕ) : ℤ) := by rw [hidx]
  rw [hcast] at hN5
  have heq : (Nat.fib n : ℤ) - -1 * 2 = (Nat.fib n : ℤ) + 2 := by ring
  rw [heq] at hN5
  exact hN5

-- N10
private theorem lucasNumber_dvd_fib_add_two_of_mod_four_eq_one (n : ℕ) (hn : n % 4 = 1) :
    ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧ ((lucasNumber k : ℕ) : ℤ) ∣ (Nat.fib n : ℤ) + 2 := by
  have hn41 : n = 4 * (n / 4) + 1 := by omega
  set q := n / 4 with hqdef
  have hnq : n = 4 * q + 1 := hn41
  set s := 2 * q + 2 with hsdef
  have hs_eq : n + 3 = 2 * s := by omega
  have hs0 : s ≠ 0 := by omega
  have hsev : Even s := ⟨q + 1, by omega⟩
  obtain ⟨r, k, hsk, hkev, hk3⟩ := exists_eq_three_pow_mul_even_not_dvd s hs0 hsev
  refine ⟨k, hkev, hk3, ?_⟩
  have h3odd : Odd (3 ^ r : ℕ) := (by decide : Odd (3 : ℕ)).pow
  have hjneg : ((-1 : ℤ)) ^ (3 ^ r) = -1 := h3odd.neg_one_pow
  have hN5a := lucasNumber_dvd_fib_add_two_mul_mul_sub k hkev 0 (3 ^ r)
  have hN5b := lucasNumber_dvd_fib_add_two_mul_mul_sub k hkev 1 (3 ^ r)
  have hF0 : ((Nat.fib 0 : ℕ) : ℤ) = 0 := by decide
  have hF1 : ((Nat.fib 1 : ℕ) : ℤ) = 1 := by decide
  have h2s : 2 * k * (3 ^ r) = 2 * s := by rw [hsk]; ring
  have hidx3 : 0 + 2 * k * (3 ^ r) = n + 3 := by rw [h2s]; omega
  have hidx4 : 1 + 2 * k * (3 ^ r) = n + 4 := by rw [h2s]; omega
  rw [hjneg, hF0, mul_zero, sub_zero] at hN5a
  rw [hjneg, hF1, mul_one] at hN5b
  have hcast3 :
      ((Nat.fib (0 + 2 * k * (3 ^ r)) : ℕ) : ℤ)
        = ((Nat.fib (n + 3) : ℕ) : ℤ) := by
    rw [hidx3]
  have hcast4 :
      ((Nat.fib (1 + 2 * k * (3 ^ r)) : ℕ) : ℤ)
        = ((Nat.fib (n + 4) : ℕ) : ℤ) := by
    rw [hidx4]
  rw [hcast3] at hN5a
  rw [hcast4] at hN5b
  have e1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
    have : n + 2 = n + 2 := rfl
    exact Nat.fib_add_two
  have e2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    have h : n + 3 = (n + 1) + 2 := by omega
    rw [h]; exact Nat.fib_add_two
  have e3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
    have h : n + 4 = (n + 2) + 2 := by omega
    rw [h]; exact Nat.fib_add_two
  have g1 : ((Nat.fib (n + 2) : ℕ) : ℤ) =
      (Nat.fib n : ℤ) + (Nat.fib (n + 1) : ℤ) := by
    exact_mod_cast e1
  have g2 : ((Nat.fib (n + 3) : ℕ) : ℤ) =
      (Nat.fib (n + 1) : ℤ) + (Nat.fib (n + 2) : ℤ) := by
    exact_mod_cast e2
  have g3 : ((Nat.fib (n + 4) : ℕ) : ℤ) =
      (Nat.fib (n + 2) : ℤ) + (Nat.fib (n + 3) : ℤ) := by
    exact_mod_cast e3
  have key : (Nat.fib n : ℤ) + 2 = 2 * ((Nat.fib (n + 4) : ℤ) + 1) - 3 * (Nat.fib (n + 3) : ℤ) := by
    linear_combination -g1 + g2 - 2 * g3
  have hN5b' : ((lucasNumber k : ℕ) : ℤ) ∣ (Nat.fib (n + 4) : ℤ) + 1 := by
    have : (Nat.fib (n + 4) : ℤ) - -1 = (Nat.fib (n + 4) : ℤ) + 1 := by ring
    rwa [this] at hN5b
  rw [key]
  exact dvd_sub (hN5b'.mul_left 2) (hN5a.mul_left 3)

-- N11
private theorem fib_odd_ne_two_mul_sq (n x : ℕ) (hodd : Odd n) (hn3 : n ≠ 3)
    (h : Nat.fib n = 2 * x ^ 2) : False := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hmod : n % 4 = 1 ∨ n % 4 = 3 := by
    revert h2
    clear h
    intro h2
    omega
  have hex : ∃ k : ℕ, Even k ∧ ¬ 3 ∣ k ∧ ((lucasNumber k : ℕ) : ℤ) ∣ (Nat.fib n : ℤ) + 2 := by
    rcases hmod with hm | hm
    · exact lucasNumber_dvd_fib_add_two_of_mod_four_eq_one n hm
    · exact lucasNumber_dvd_fib_add_two_of_mod_four_eq_three n hm hn3
  obtain ⟨k, hkev, hk3, hdvd⟩ := hex
  have hbmod : lucasNumber k % 4 = 3 :=
    lucasNumber_mod_four_of_even_of_not_three_dvd k hkev hk3
  have hbodd : Odd (lucasNumber k) := Nat.odd_iff.mpr (by omega)
  have hcast : ((Nat.fib n : ℕ) : ℤ) = 2 * ((x : ℤ) ^ 2) := by exact_mod_cast h
  have h2dvd : ((lucasNumber k : ℕ) : ℤ) ∣ 2 * ((x : ℤ) ^ 2 + 1) := by
    have heq : ((Nat.fib n : ℕ) : ℤ) + 2 = 2 * ((x : ℤ) ^ 2 + 1) := by rw [hcast]; ring
    rwa [heq] at hdvd
  have hcop : Nat.Coprime (lucasNumber k) 2 := hbodd.coprime_two_right
  have hisocop : IsCoprime ((lucasNumber k : ℕ) : ℤ) (2 : ℤ) := hcop.isCoprime
  have h1dvd : ((lucasNumber k : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 + 1 :=
    hisocop.dvd_of_dvd_mul_left h2dvd
  exact not_dvd_sq_add_one_of_mod_four_eq_three (lucasNumber k) hbmod _ h1dvd

-- N12
private theorem nat_gcd_fib_lucasNumber_dvd_two (m : ℕ) :
    Nat.gcd (Nat.fib m) (lucasNumber m) ∣ 2 := by
  have hN1 := lucasNumber_add_fib m
  have hgl : Nat.gcd (Nat.fib m) (lucasNumber m) ∣ Nat.fib m := Nat.gcd_dvd_left _ _
  have hgr : Nat.gcd (Nat.fib m) (lucasNumber m) ∣ lucasNumber m := Nat.gcd_dvd_right _ _
  have hsum : Nat.gcd (Nat.fib m) (lucasNumber m) ∣ 2 * Nat.fib (m + 1) := by
    have : Nat.gcd (Nat.fib m) (lucasNumber m) ∣ lucasNumber m + Nat.fib m := dvd_add hgr hgl
    rwa [hN1] at this
  have hcop : Nat.Coprime (Nat.fib m) (Nat.fib (m + 1)) := Nat.fib_coprime_fib_succ m
  have hcopg : Nat.Coprime (Nat.gcd (Nat.fib m) (lucasNumber m)) (Nat.fib (m + 1)) :=
    hcop.coprime_dvd_left hgl
  exact hcopg.dvd_of_dvd_mul_right hsum

-- N13
private theorem eq_gcd_mul_sq_of_mul_eq_sq (a b y : ℕ) (h : a * b = y ^ 2) :
    ∃ c : ℕ, b = Nat.gcd a b * c ^ 2 := by
  obtain ⟨a', b', hcop, ha, hb⟩ := Nat.exists_coprime a b
  set g := Nat.gcd a b with hgdef
  by_cases hg : g = 0
  · have hb0 : b = 0 := by
      have hd : g ∣ b := by rw [hgdef]; exact Nat.gcd_dvd_right a b
      rw [hg] at hd
      exact zero_dvd_iff.mp hd
    refine ⟨0, by rw [hb0]; simp⟩
  · have hgpos : 0 < g := Nat.pos_of_ne_zero hg
    have h' : (a' * g) * (b' * g) = y ^ 2 := by
      have ha' : a = a' * g := ha
      have hb' : b = b' * g := hb
      rw [← ha', ← hb']
      exact h
    have hgab : a' * b' * (g ^ 2) = y ^ 2 := by linear_combination h'
    have hgdvd : g ^ 2 ∣ y ^ 2 :=
      ⟨a' * b', by rw [← hgab]; ring⟩
    have hgy : g ∣ y :=
      (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hgdvd
    obtain ⟨z, hz⟩ := hgy
    have e : (g ^ 2) * (a' * b') = (g ^ 2) * (z ^ 2) := by
      have hgab2 : a' * b' * (g ^ 2) = (g * z) ^ 2 := by rw [← hz]; exact hgab
      linear_combination hgab2
    have hz2 : a' * b' = z ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hgpos 2) e
    have hU : IsUnit (gcd b' a') := by
      rw [Nat.isUnit_iff]
      exact hcop.symm
    obtain ⟨c, hc⟩ :=
      exists_eq_pow_of_mul_eq_pow hU
        (show b' * a' = z ^ 2 by rw [mul_comm]; exact hz2)
    refine ⟨c, ?_⟩
    have hb' : b = b' * g := hb
    rw [hb', hc]
    ring

-- The two Lucas classifications are proved in sibling modules and used here.
-- See `cohn_square_lucas` and `cohn_twice_square_lucas`.

-- N14
private theorem fib_two_mul_eq_two_mul_sq (m x : ℕ) (hm : 0 < m)
    (h : Nat.fib (2 * m) = 2 * x ^ 2) : m = 3 := by
  have hN2 := fib_two_mul_eq_fib_mul_lucasNumber m
  have hmul : (2 * Nat.fib m) * lucasNumber m = (2 * x) ^ 2 := by
    have : Nat.fib m * lucasNumber m = 2 * x ^ 2 := by rw [← hN2]; exact h
    ring_nf
    ring_nf at this
    omega
  obtain ⟨c, hc⟩ := eq_gcd_mul_sq_of_mul_eq_sq (2 * Nat.fib m) (lucasNumber m) (2 * x) hmul
  set g := Nat.gcd (2 * Nat.fib m) (lucasNumber m) with hgdef
  have hg4 : g ∣ 4 := by
    have h1 : g ∣ 2 * Nat.fib m := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
    have h2 : g ∣ lucasNumber m := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
    have h2' : g ∣ 2 * lucasNumber m := h2.mul_left 2
    have hgcd : g ∣ Nat.gcd (2 * Nat.fib m) (2 * lucasNumber m) := Nat.dvd_gcd h1 h2'
    have hmul2 :
        Nat.gcd (2 * Nat.fib m) (2 * lucasNumber m)
          = 2 * Nat.gcd (Nat.fib m) (lucasNumber m) :=
      Nat.gcd_mul_left 2 (Nat.fib m) (lucasNumber m)
    rw [hmul2] at hgcd
    have h12 := nat_gcd_fib_lucasNumber_dvd_two m
    have h24 : 2 * Nat.gcd (Nat.fib m) (lucasNumber m) ∣ 2 * 2 :=
      Nat.mul_dvd_mul_left 2 h12
    have h42 : (2 * 2) = 4 := by ring
    rw [h42] at h24
    exact dvd_trans hgcd h24
  have hgmem : g = 1 ∨ g = 2 ∨ g = 4 := by
    have h42 : (4 : ℕ) = 2 ^ 2 := by ring
    rw [h42] at hg4
    obtain ⟨k, hk2, hkk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hg4
    interval_cases k
    · norm_num at hkk
      exact Or.inl hkk
    · norm_num at hkk
      exact Or.inr (Or.inl hkk)
    · norm_num at hkk
      exact Or.inr (Or.inr hkk)
  have hm136 : m = 1 ∨ m = 3 ∨ m = 6 := by
    rcases hgmem with hg1 | hg2 | hg4v
    · have hsq : lucasNumber m = c ^ 2 := by
        have : lucasNumber m = g * c ^ 2 := hc
        rw [hg1, one_mul] at this
        exact this
      rcases cohn_square_lucas m c hm hsq with h1 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h3)
    · have hsq : lucasNumber m = 2 * c ^ 2 := by
        have : lucasNumber m = g * c ^ 2 := hc
        rw [hg2] at this
        exact this
      exact Or.inr (Or.inr (cohn_twice_square_lucas m c hm hsq))
    · have hsq : lucasNumber m = (2 * c) ^ 2 := by
        have : lucasNumber m = g * c ^ 2 := hc
        rw [hg4v] at this
        rw [this]; ring
      rcases cohn_square_lucas m (2 * c) hm hsq with h1 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h3)
  rcases hm136 with h1 | h3 | h6
  · have hF2 : Nat.fib 2 = 1 := by decide
    have h12 : (2 : ℕ) * m = 2 := by omega
    rw [h12, hF2] at h
    omega
  · exact h3
  · have hF12 : Nat.fib 12 = 144 := by decide
    have h12 : (2 : ℕ) * m = 12 := by omega
    rw [h12, hF12] at h
    have hx9 : x < 9 := by
      by_contra hc9
      push Not at hc9
      have h81 : 81 ≤ x ^ 2 := by
        have hle : (9 : ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc9 2
        simpa using hle
      omega
    have hxb : x ≤ 8 := by omega
    interval_cases x <;> omega

/-- **Cohn's theorem on Fibonacci numbers of the form $2x^2$.** Let $F_n$ denote the Fibonacci
numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. If $n$ and $x$ are natural
numbers with $n \ge 1$ and $F_n = 2x^2$, then $n \in \{3, 6\}$.

This is the second claim of Theorem 2.1 of Keskin and Yosma.

Proves `Wanted` entry `cohn_twice_square_fibonacci`.
-/
theorem cohn_twice_square_fibonacci (n x : ℕ) (hn : 0 < n)
    (h : Nat.fib n = 2 * x ^ 2) : n = 3 ∨ n = 6 := by
  have hcopy := h
  clear h
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hmpos : 0 < m := by omega
    have h2m : 2 * m = n := by omega
    have h' : Nat.fib (2 * m) = 2 * x ^ 2 := by rw [h2m]; exact hcopy
    have hm3 : m = 3 := fib_two_mul_eq_two_mul_sq m x hmpos h'
    exact Or.inr (by omega)
  · by_cases hn3 : n = 3
    · exact Or.inl hn3
    · exact (fib_odd_ne_two_mul_sq n x hodd hn3 hcopy).elim

end
end MetaMathlibExt
