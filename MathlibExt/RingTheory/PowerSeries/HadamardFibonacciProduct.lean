/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Order.Ring.Star

private theorem coeff_C_Xpow_mul (R : Type _) [CommRing R] (c : R) (nn k : ℕ) (p : PowerSeries R) :
    PowerSeries.coeff k (PowerSeries.C c * PowerSeries.X ^ nn * p) =
      if k < nn then 0 else c * PowerSeries.coeff (k - nn) p := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases h : k < nn
  · simp only [h, ite_true, Nat.not_le.mpr h, ite_false, mul_zero]
  · simp only [h, ite_false, Nat.le_of_not_lt h, ite_true]

private theorem coeff_Xpow_mul_aux (R : Type _) [CommRing R] (nn k : ℕ) (p : PowerSeries R) :
    PowerSeries.coeff k (PowerSeries.X ^ nn * p) =
      if k < nn then 0 else PowerSeries.coeff (k - nn) p := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : k < nn
  · simp only [h, ite_true, Nat.not_le.mpr h, ite_false]
  · simp only [h, ite_false, Nat.le_of_not_lt h, ite_true]

private theorem F_mul_eq (R : Type _) [CommRing R] (a : R) :
    (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) *
      PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ)
      = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

private theorem F_coeff_eq (R : Type _) [CommRing R] (a : R) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ))
    - (if k < 1 then 0 else a * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)))
    - (if k < 2 then 0 else PowerSeries.coeff (k - 2) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)))
    = if k = 0 then 1 else 0 := by
  have hmul := F_mul_eq R a
  have h0 := congrArg (PowerSeries.coeff k) hmul
  rw [PowerSeries.coeff_one] at h0
  have h1 : (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) *
        PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ)
        = PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ)
        - (PowerSeries.C a * PowerSeries.X ^ 1 * PowerSeries.invOfUnit
            (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ))
        - (PowerSeries.X ^ 2 * PowerSeries.invOfUnit
            (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ)) := by
    ring
  have hexpand : PowerSeries.coeff k
      ((1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) *
        PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ))
      = PowerSeries.coeff k (PowerSeries.invOfUnit
        (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ))
      - (if k < 1 then 0 else a * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
        (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)))
      - (if k < 2 then 0 else PowerSeries.coeff (k - 2) (PowerSeries.invOfUnit
        (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ))) := by
    rw [h1]
    simp only [map_sub, coeff_C_Xpow_mul, coeff_Xpow_mul_aux]
  rw [hexpand] at h0
  exact h0

private theorem f0' (R : Type _) [CommRing R] (a : R) :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) = 1 := by
  simp

private theorem f1' (R : Type _) [CommRing R] (a : R) :
    PowerSeries.coeff 1 (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) = a := by
  have h := F_coeff_eq R a 1
  norm_num at h
  exact sub_eq_zero.mp h

private theorem frec' (R : Type _) [CommRing R] (a : R) (k : ℕ) (hk : 2 ≤ k) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ))
    = a * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ))
    + PowerSeries.coeff (k - 2) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) := by
  have h := F_coeff_eq R a k
  have hk0 : k ≠ 0 := by omega
  have hk1 : ¬ k < 1 := by omega
  have hk2 : ¬ k < 2 := by omega
  simp only [hk0, ite_false, hk1, hk2] at h
  linear_combination h

private theorem G_mul_eq (R : Type _) [CommRing R] (b : R) (n : ℕ) (hn : n ≠ 0) :
    (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) *
      PowerSeries.invOfUnit (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ)
      = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp only [map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, mul_zero, sub_zero, zero_pow hn, sub_zero, Units.val_one]

private theorem G_coeff_eq (R : Type _) [CommRing R] (b : R) (n k : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))
    - (if k < 1 then 0 else b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)))
    - (if k < n then 0 else PowerSeries.coeff (k - n) (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)))
    = if k = 0 then 1 else 0 := by
  have hmul := G_mul_eq R b n hn
  have h0 := congrArg (PowerSeries.coeff k) hmul
  rw [PowerSeries.coeff_one] at h0
  have h1 : (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) *
        PowerSeries.invOfUnit (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ)
        = PowerSeries.invOfUnit (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ)
        - (PowerSeries.C b * PowerSeries.X ^ 1 * PowerSeries.invOfUnit
            (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ))
        - (PowerSeries.X ^ n * PowerSeries.invOfUnit
            (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ)) := by
    ring
  have hexpand : PowerSeries.coeff k
      ((1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) *
        PowerSeries.invOfUnit (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ))
      = PowerSeries.coeff k (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))
      - (if k < 1 then 0 else b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)))
      - (if k < n then 0 else PowerSeries.coeff (k - n) (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))) := by
    rw [h1]
    simp only [map_sub, coeff_C_Xpow_mul, coeff_Xpow_mul_aux]
  rw [hexpand] at h0
  exact h0

private theorem g0' (R : Type _) [CommRing R] (b : R) (n : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) = 1 := by
  simp

private theorem grec_low (R : Type _) [CommRing R] (b : R) (n k : ℕ) (hn : n ≠ 0)
    (hk1 : 1 ≤ k) (hkn : k < n) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))
    = b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) := by
  have h := G_coeff_eq R b n k hn
  have hk0 : k ≠ 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  simp only [hk0, ite_false, hk1', hkn, ite_true, sub_zero] at h
  linear_combination h

private theorem grec_high (R : Type _) [CommRing R] (b : R) (n k : ℕ) (hn : 1 ≤ n) (hkn : n ≤ k) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))
    = b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ))
    + PowerSeries.coeff (k - n) (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) := by
  have hn0 : n ≠ 0 := by omega
  have h := G_coeff_eq R b n k hn0
  have hk0 : k ≠ 0 := by omega
  have hk1' : ¬ k < 1 := by omega
  have hkn' : ¬ k < n := by omega
  simp only [hk0, ite_false, hk1', hkn'] at h
  linear_combination h

private theorem fib_add_aux (R : Type _) [CommRing R] (F : ℕ → R) (a : R)
    (h0 : F 0 = 1) (h1 : F 1 = a) (hrec : ∀ k : ℕ, 2 ≤ k → F k = a * F (k - 1) + F (k - 2))
    (s d : ℕ) : F ((s + 1) + 1 + d) = F (s + 1) * F (1 + d) + F s * F d := by
  induction s generalizing d with
  | zero =>
    have hr := hrec (2 + d) (by omega)
    have e1 : (2 + d) - 1 = 1 + d := by omega
    have e2 : (2 + d) - 2 = d := by omega
    rw [e1, e2] at hr
    have e3 : (0 + 1 : ℕ) + 1 + d = 2 + d := by omega
    rw [e3]
    simp only [h0, h1, one_mul] at hr ⊢
    exact hr
  | succ s ih =>
    have ih' := ih (d + 1)
    have eL : ((s + 1 + 1) + 1 + d) = ((s + 1) + 1 + (d + 1)) := by omega
    have hr2 : F (1 + (d + 1)) = a * F (1 + d) + F d := by
      have hr := hrec (2 + d) (by omega)
      have e1 : (2 + d) - 1 = 1 + d := by omega
      have e2 : (2 + d) - 2 = d := by omega
      rw [e1, e2] at hr
      have e3 : 1 + (d + 1) = 2 + d := by omega
      rw [e3]
      exact hr
    have hrS : F (s + 1 + 1) = a * F (s + 1) + F s := by
      have hr := hrec (s + 1 + 1) (by omega)
      have e1 : (s + 1 + 1) - 1 = s + 1 := by omega
      have e2 : (s + 1 + 1) - 2 = s := by omega
      rw [e1, e2] at hr
      exact hr
    have ed : d + 1 = 1 + d := by omega
    rw [eL]
    rw [ih']
    rw [hr2]
    rw [ed]
    rw [hrS]
    ring

private theorem fib_shift1 (R : Type _) [CommRing R] (F : ℕ → R) (a : R)
    (h0 : F 0 = 1) (h1 : F 1 = a) (hrec : ∀ k : ℕ, 2 ≤ k → F k = a * F (k - 1) + F (k - 2))
    (n d : ℕ) (hn : 1 ≤ n) : F (n + 1 + d) = F n * F (1 + d) + F (n - 1) * F d := by
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 1 := ⟨n - 1, by omega⟩
  have h := fib_add_aux R F a h0 h1 hrec s d
  have e1 : (s + 1 - 1) = s := by omega
  simpa only [e1] using h

private theorem cassini_aux (R : Type _) [CommRing R] (F : ℕ → R) (a : R)
    (h0 : F 0 = 1) (h1 : F 1 = a) (hrec : ∀ k : ℕ, 2 ≤ k → F k = a * F (k - 1) + F (k - 2))
    (m : ℕ) : F (m + 2) * F m - F (m + 1) ^ 2 = (-1 : R) ^ (m + 2) := by
  induction m with
  | zero =>
    have hr := hrec 2 (by omega)
    norm_num at hr ⊢
    rw [h0, h1] at hr ⊢
    linear_combination hr
  | succ m ih =>
    have eG1 : m + 1 + 2 = m + 3 := by omega
    have eG2 : m + 1 + 1 = m + 2 := by omega
    have hr1 : F (m + 3) = a * F (m + 2) + F (m + 1) := by
      have hr := hrec (m + 3) (by omega)
      have e1 : (m + 3) - 1 = m + 2 := by omega
      have e2 : (m + 3) - 2 = m + 1 := by omega
      rw [e1, e2] at hr
      exact hr
    have hr2 : F (m + 2) = a * F (m + 1) + F m := by
      have hr := hrec (m + 2) (by omega)
      have e1 : (m + 2) - 1 = m + 1 := by omega
      have e2 : (m + 2) - 2 = m := by omega
      rw [e1, e2] at hr
      exact hr
    have ep : (-1 : R) ^ (m + 1 + 2) = -(-1 : R) ^ (m + 2) := by
      have e : m + 1 + 2 = (m + 2) + 1 := by omega
      rw [e, pow_succ]
      ring
    rw [eG1, eG2, ep]
    linear_combination F (m + 1) * hr1 - F (m + 2) * hr2 - ih

private theorem cassini (R : Type _) [CommRing R] (F : ℕ → R) (a : R)
    (h0 : F 0 = 1) (h1 : F 1 = a) (hrec : ∀ k : ℕ, 2 ≤ k → F k = a * F (k - 1) + F (k - 2))
    (n : ℕ) (hn : 2 ≤ n) : F n * F (n - 2) - F (n - 1) ^ 2 = (-1 : R) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := cassini_aux R F a h0 h1 hrec m
  have e1 : m + 2 - 2 = m := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2]
  exact h

private theorem coeff_C_Xpow_thm (R : Type _) [CommRing R] (c : R) (nn k : ℕ) :
    PowerSeries.coeff k (PowerSeries.C c * PowerSeries.X ^ nn : PowerSeries R) =
      if k = nn then c else 0 := by
  have h1 : (PowerSeries.C c * PowerSeries.X ^ nn : PowerSeries R)
      = PowerSeries.C c * PowerSeries.X ^ nn * 1 := by ring
  rw [h1, coeff_C_Xpow_mul]
  by_cases h : k < nn
  · simp only [h, ite_true]
    have hkn : ¬ k = nn := by omega
    simp [hkn]
  · simp only [h, ite_false]
    by_cases h2 : k = nn
    · subst h2
      simp [PowerSeries.coeff_one]
    · have h3 : k - nn ≠ 0 := by omega
      simp [PowerSeries.coeff_one, h3, h2]

@[expose] public section

namespace MetaMathlibExt

/-! # Hadamard products and tilings -/

/--
**Hadamard product of two Fibonacci-type series.** Let $R$ be a commutative ring, let
$a, b \in R$, and let $n \ge 2$ be a natural number. For each $k$, let $f_k$ be the coefficient of
$x^k$ in $1/(1 - ax - x^2)$ and $g_k$ the coefficient of $x^k$ in $1/(1 - bx - x^n)$, the
inverses taken in $R[[x]]$. Then the Hadamard product $\sum_{k \ge 0} f_k g_k x^k$ equals
$$
\frac{1 - f_{n-2}\, x^n}{1 - ab\, x - b^2 x^2 - (f_n + f_{n-2})\, x^n -
(2b f_{n-1} - ab f_{n-2})\, x^{n+1} + (-1)^n x^{2n}}
$$
in $R[[x]]$, where the denominator has constant coefficient $1$ and so is invertible.

Source: Jong Hyun Kim, "Hadamard Products and Tilings", Journal of Integer Sequences 12 (2009),
Article 09.7.4, Theorem `eq:61`, lines 430-437,
<https://cs.uwaterloo.ca/journals/JIS/VOL12/Kim/kim18.tex>.
Proves `Wanted` entry `hadamard_fibonacci_product`.
-/
theorem hadamard_fibonacci_product (R : Type _) [CommRing R] (a b : R)
    (n : ℕ) (hn : 2 ≤ n) :
  let f := fun k =>
    PowerSeries.coeff k
      (PowerSeries.invOfUnit
        (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2) (1 : Rˣ))
  PowerSeries.mk (fun k =>
      f k * PowerSeries.coeff k
        (PowerSeries.invOfUnit
          (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n) (1 : Rˣ))) =
    (1 - PowerSeries.C (f (n - 2)) * PowerSeries.X ^ n) *
      PowerSeries.invOfUnit
        (1 - PowerSeries.C (a * b) * PowerSeries.X - PowerSeries.C (b ^ 2) * PowerSeries.X ^ 2 -
          PowerSeries.C (f n + f (n - 2)) * PowerSeries.X ^ n -
          PowerSeries.C (2 * b * f (n - 1) - a * b * f (n - 2)) * PowerSeries.X ^ (n + 1) +
          PowerSeries.C ((-1 : R) ^ n) * PowerSeries.X ^ (2 * n))
        (1 : Rˣ) := by
  intro f
  have hf0 : f 0 = 1 := by
    have h : f 0 = PowerSeries.coeff 0 (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) := rfl
    rw [h]
    exact f0' R a
  have hf1 : f 1 = a := by
    have h : f 1 = PowerSeries.coeff 1 (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) := rfl
    rw [h]
    exact f1' R a
  have hfrec : ∀ k : ℕ, 2 ≤ k → f k = a * f (k - 1) + f (k - 2) := by
    intro k hk
    have h : f k = PowerSeries.coeff k (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) := rfl
    have h2 : a * f (k - 1) + f (k - 2) = a * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) +
      PowerSeries.coeff (k - 2) (PowerSeries.invOfUnit
      (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries R) (1 : Rˣ)) := rfl
    rw [h, h2]
    exact frec' R a k hk
  have hn0 : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hg0 : PowerSeries.coeff 0 (PowerSeries.invOfUnit
      (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) = 1 :=
    g0' R b n
  have hglow : ∀ k : ℕ, 1 ≤ k → k < n →
      PowerSeries.coeff k (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) =
      b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) := by
    intro k h1 h2
    exact grec_low R b n k hn0 h1 h2
  have hghigh : ∀ k : ℕ, n ≤ k →
      PowerSeries.coeff k (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) =
      b * PowerSeries.coeff (k - 1) (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) +
      PowerSeries.coeff (k - n) (PowerSeries.invOfUnit
        (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ)) := by
    intro k h
    exact grec_high R b n k hn1 h
  have hshift : ∀ s d : ℕ, 1 ≤ s →
      f (s + 1 + d) = f s * f (1 + d) + f (s - 1) * f d :=
    fun s d hs => fib_shift1 R f a hf0 hf1 hfrec s d hs
  have hcass : f n * f (n - 2) - f (n - 1) ^ 2 = (-1 : R) ^ n :=
    cassini R f a hf0 hf1 hfrec n hn
  set G := PowerSeries.invOfUnit
    (1 - PowerSeries.C b * PowerSeries.X - PowerSeries.X ^ n : PowerSeries R) (1 : Rˣ) with hGdef
  set H := PowerSeries.mk (fun k => f k * PowerSeries.coeff k G) with hHdef
  set C1 : R := f n + f (n - 2) with hC1def
  set C2 : R := 2 * b * f (n - 1) - a * b * f (n - 2) with hC2def
  set E : R := ((-1 : R) ^ n) with hEdef
  set D := (1 - PowerSeries.C (a * b) * PowerSeries.X - PowerSeries.C (b ^ 2) * PowerSeries.X ^ 2 -
    PowerSeries.C C1 * PowerSeries.X ^ n - PowerSeries.C C2 * PowerSeries.X ^ (n + 1) +
    PowerSeries.C E * PowerSeries.X ^ (2 * n) : PowerSeries R) with hDdef
  set C0 := (1 - PowerSeries.C (f (n - 2)) * PowerSeries.X ^ n : PowerSeries R) with hC0def
  set I := PowerSeries.invOfUnit D (1 : Rˣ) with hIdef
  have hHk : ∀ j : ℕ, PowerSeries.coeff j H = f j * PowerSeries.coeff j G := by
    intro j
    rw [hHdef]
    simp [PowerSeries.coeff_mk]
  have hDconst : PowerSeries.constantCoeff D = 1 := by
    rw [hDdef]
    simp only [map_sub, map_add, map_one, map_mul, map_pow, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X]
    rw [zero_pow hn0, zero_pow (show n + 1 ≠ 0 by omega), zero_pow (show 2 * n ≠ 0 by omega)]
    simp
  have hDI : D * I = 1 := by
    apply PowerSeries.mul_invOfUnit
    rw [hDconst, Units.val_one]
  have hD : D * H = H - (PowerSeries.C (a * b) * PowerSeries.X ^ 1 * H) -
      (PowerSeries.C (b ^ 2) * PowerSeries.X ^ 2 * H) - (PowerSeries.C C1 * PowerSeries.X ^ n * H) -
      (PowerSeries.C C2 * PowerSeries.X ^ (n + 1) * H) +
      (PowerSeries.C E * PowerSeries.X ^ (2 * n) * H) := by
    rw [hDdef]
    ring
  have expandDH : ∀ k : ℕ, PowerSeries.coeff k (D * H) =
      (f k * PowerSeries.coeff k G)
      - (if k < 1 then 0 else (a * b) * (f (k - 1) * PowerSeries.coeff (k - 1) G))
      - (if k < 2 then 0 else (b ^ 2) * (f (k - 2) * PowerSeries.coeff (k - 2) G))
      - (if k < n then 0 else C1 * (f (k - n) * PowerSeries.coeff (k - n) G))
      - (if k < n + 1 then 0 else C2 * (f (k - n - 1) * PowerSeries.coeff (k - n - 1) G))
      + (if k < 2 * n then 0 else E * (f (k - 2 * n) * PowerSeries.coeff (k - 2 * n) G)) := by
    intro k
    rw [hD]
    simp only [map_sub, map_add, coeff_C_Xpow_mul, hHk]
    have e : k - (n + 1) = k - n - 1 := by omega
    rw [e]
  have expandC : ∀ k : ℕ, PowerSeries.coeff k C0 =
      (if k = 0 then 1 else 0) - (if k = n then f (n - 2) else 0) := by
    intro k
    rw [hC0def]
    simp only [map_sub, PowerSeries.coeff_one, coeff_C_Xpow_thm]
  have key : ∀ k : ℕ, PowerSeries.coeff k (D * H) = PowerSeries.coeff k C0 := by
    intro k
    rw [expandDH k, expandC k]
    by_cases hk0 : k = 0
    · subst hk0
      have h0n : (0 : ℕ) < n := by omega
      have h0n1 : (0 : ℕ) < n + 1 := by omega
      have h02n : (0 : ℕ) < 2 * n := by omega
      have h0ne : (0 : ℕ) ≠ n := by omega
      simp only [(show (0 : ℕ) < 1 by omega), (show (0 : ℕ) < 2 by omega), h0n, h0n1, h02n,
        ite_true, h0ne, ite_false, sub_zero, add_zero]
      rw [hf0, hg0]
      ring
    · by_cases hkn : k < n
      · by_cases hk1 : k = 1
        · subst hk1
          have hk1n : (1 : ℕ) < n := hkn
          have e1 : ¬ (1 : ℕ) < 1 := by omega
          have e2 : (1 : ℕ) < 2 := by omega
          have e3 : (1 : ℕ) < n + 1 := by omega
          have e4 : (1 : ℕ) < 2 * n := by omega
          have e5 : (1 : ℕ) ≠ 0 := by omega
          have e6 : (1 : ℕ) ≠ n := by omega
          simp only [e1, e2, hk1n, e3, e4, ite_true, ite_false, e5, e6, sub_zero, add_zero]
          have hg1 := hglow 1 (by omega) hk1n
          rw [hf1, hg1, hf0, hg0]
          ring
        · have hk2 : 2 ≤ k := by omega
          have e1 : ¬ k < 1 := by omega
          have e2 : ¬ k < 2 := by omega
          have e3 : k < n + 1 := by omega
          have e4 : k < 2 * n := by omega
          simp only [e1, e2, hkn, e3, e4, ite_true, ite_false, hk0, sub_zero, add_zero,
            (show k ≠ n by omega)]
          have hfk := hfrec k hk2
          have hgk := hglow k (by omega) hkn
          have hgk1 := hglow (k - 1) (by omega) (by omega)
          have e5 : k - 1 - 1 = k - 2 := by omega
          rw [hfk, hgk, hgk1, e5]
          ring
      · by_cases hkeq : k = n
        · rw [hkeq]
          have e1 : ¬ n < 1 := by omega
          have e2 : ¬ n < 2 := by omega
          have e3 : ¬ n < n := by omega
          have e4 : n < n + 1 := by omega
          have e5 : n < 2 * n := by omega
          have e6 : n ≠ 0 := by omega
          simp only [e1, e2, e3, e4, e5, ite_true, ite_false, e6, sub_zero,
            add_zero]
          have enn : n - n = 0 := Nat.sub_self n
          have hfn := hfrec n hn
          have hgn := hghigh n (le_refl n)
          have hgn1 := hglow (n - 1) (by omega) (by omega)
          have en1 : n - 1 - 1 = n - 2 := by omega
          rw [hC1def, hfn, hgn, hgn1, en1, enn, hf0, hg0]
          ring
        · have hnk : n < k := by omega
          by_cases hk2n : k < 2 * n
          · have eA1 : ¬ k < 1 := by omega
            have eA2 : ¬ k < 2 := by omega
            have eA4 : ¬ k < n + 1 := by omega
            have eA5 : k ≠ 0 := by omega
            have eA6 : k ≠ n := by omega
            simp only [eA1, eA2, hkn, eA4, hk2n, ite_true, ite_false, eA5, eA6, sub_zero,
              add_zero]
            have hk2 : 2 ≤ k := by omega
            have hfk := hfrec k hk2
            have hgk := hghigh k (by omega : n ≤ k)
            have hgk1 := hghigh (k - 1) (by omega : n ≤ k - 1)
            have hgkn := hglow (k - n) (by omega : 1 ≤ k - n) (by omega : k - n < n)
            have e1 : k - 1 - 1 = k - 2 := by omega
            have e2 : k - 1 - n = k - n - 1 := by omega
            have hF : a * f (k - 1) + 2 * f (k - 2)
                = (f n + f (n - 2)) * f (k - n)
                + (2 * f (n - 1) - a * f (n - 2)) * f (k - n - 1) := by
              by_cases hn2 : n = 2
              · subst hn2
                have hk3 : k = 3 := by omega
                subst hk3
                change a * f 2 + 2 * f 1 = (f 2 + f 0) * f 1 + (2 * f 1 - a * f 0) * f 0
                rw [hf1, hf0]
                ring
              · have hn3 : 3 ≤ n := by omega
                have s1 := hshift (n - 1) (k - n - 1) (by omega : 1 ≤ n - 1)
                have eS1 : (n - 1) + 1 + (k - n - 1) = k - 1 := by omega
                have eS1b : 1 + (k - n - 1) = k - n := by omega
                have eS1c : (n - 1) - 1 = n - 2 := by omega
                rw [eS1, eS1b, eS1c] at s1
                have s2 := hshift (n - 2) (k - n - 1) (by omega : 1 ≤ n - 2)
                have eT1 : (n - 2) + 1 + (k - n - 1) = k - 2 := by omega
                have eT3 : (n - 2) - 1 = n - 3 := by omega
                rw [eT1, eS1b, eT3] at s2
                have hnrec := hfrec n hn
                have hn1rec0 := hfrec (n - 1) (by omega : 2 ≤ n - 1)
                have eN2 : (n - 1) - 2 = n - 3 := by omega
                rw [eS1c, eN2] at hn1rec0
                linear_combination a * s1 + 2 * s2 - f (k - n) * hnrec -
                  (2 * f (k - n - 1)) * hn1rec0
            rw [hC1def, hC2def, hfk, hgk, hgk1, hgkn, e1, e2]
            linear_combination (b * PowerSeries.coeff (k - n - 1) G) * hF
          · have hk2n' : 2 * n ≤ k := by omega
            have eB1 : ¬ k < 1 := by omega
            have eB2 : ¬ k < 2 := by omega
            have eB3 : ¬ k < n := by omega
            have eB4 : ¬ k < n + 1 := by omega
            have eB5 : ¬ k < 2 * n := by omega
            have eB6 : k ≠ 0 := by omega
            have eB7 : k ≠ n := by omega
            simp only [eB1, eB2, eB3, eB4, eB5, ite_false, eB6, eB7, sub_zero]
            have hk2 : 2 ≤ k := by omega
            have hfk := hfrec k hk2
            have hgk := hghigh k (by omega : n ≤ k)
            have hgk1 := hghigh (k - 1) (by omega : n ≤ k - 1)
            have hgkn := hghigh (k - n) (by omega : n ≤ k - n)
            have e1 : k - 1 - 1 = k - 2 := by omega
            have e2 : k - 1 - n = k - n - 1 := by omega
            have e3 : (k - n) - n = k - 2 * n := by omega
            have hF : a * f (k - 1) + 2 * f (k - 2)
                = (f n + f (n - 2)) * f (k - n)
                + (2 * f (n - 1) - a * f (n - 2)) * f (k - n - 1) := by
              by_cases hn2 : n = 2
              · subst hn2
                have s1 := hshift 1 (k - 2 - 1) (by omega : 1 ≤ 1)
                have es1 : 1 + 1 + (k - 2 - 1) = k - 1 := by omega
                have es2 : 1 + (k - 2 - 1) = k - 2 := by omega
                have es3 : (1 : ℕ) - 1 = 0 := by omega
                rw [es1, es2, es3, hf1, hf0] at s1
                have h2 := hfrec 2 (by omega)
                have en0 : (2 : ℕ) - 2 = 0 := by omega
                have en1 : (2 : ℕ) - 1 = 1 := by omega
                rw [en0, en1, hf1, hf0] at h2
                rw [en0, en1, hf1, hf0]
                linear_combination a * s1 - f (k - 2) * h2
              · have hn3 : 3 ≤ n := by omega
                have s1 := hshift (n - 1) (k - n - 1) (by omega : 1 ≤ n - 1)
                have eS1 : (n - 1) + 1 + (k - n - 1) = k - 1 := by omega
                have eS1b : 1 + (k - n - 1) = k - n := by omega
                have eS1c : (n - 1) - 1 = n - 2 := by omega
                rw [eS1, eS1b, eS1c] at s1
                have s2 := hshift (n - 2) (k - n - 1) (by omega : 1 ≤ n - 2)
                have eT1 : (n - 2) + 1 + (k - n - 1) = k - 2 := by omega
                have eT3 : (n - 2) - 1 = n - 3 := by omega
                rw [eT1, eS1b, eT3] at s2
                have hnrec := hfrec n hn
                have hn1rec0 := hfrec (n - 1) (by omega : 2 ≤ n - 1)
                have eN2 : (n - 1) - 2 = n - 3 := by omega
                rw [eS1c, eN2] at hn1rec0
                linear_combination a * s1 + 2 * s2 - f (k - n) * hnrec -
                  (2 * f (k - n - 1)) * hn1rec0
            have hG2 : f k = (f n + f (n - 2)) * f (k - n) - (-1 : R) ^ n * f (k - 2 * n) := by
              by_cases heq : k = 2 * n
              · subst heq
                have s := hshift n (n - 1) hn1
                have es1 : n + 1 + (n - 1) = 2 * n := by omega
                have es2 : 1 + (n - 1) = n := by omega
                rw [es1, es2] at s
                have ekn : 2 * n - n = n := by omega
                have ek2n : 2 * n - 2 * n = 0 := Nat.sub_self _
                rw [ekn, ek2n, hf0]
                linear_combination s - hcass
              · have hgt : 2 * n < k := by omega
                have sA := hshift n (k - n - 1) hn1
                have eA1 : n + 1 + (k - n - 1) = k := by omega
                have eA2 : 1 + (k - n - 1) = k - n := by omega
                rw [eA1, eA2] at sA
                have sB := hshift n (k - 2 * n - 1) hn1
                have eB1 : n + 1 + (k - 2 * n - 1) = k - n := by omega
                have eB2 : 1 + (k - 2 * n - 1) = k - 2 * n := by omega
                rw [eB1, eB2] at sB
                have sC := hshift (n - 1) (k - 2 * n - 1) (by omega : 1 ≤ n - 1)
                have eC1 : (n - 1) + 1 + (k - 2 * n - 1) = k - n - 1 := by omega
                have eC2 : (n - 1) - 1 = n - 2 := by omega
                rw [eC1, eB2, eC2] at sC
                linear_combination sA - f (n - 2) * sB + f (n - 1) * sC -
                  f (k - 2 * n) * hcass
            rw [hC1def, hC2def, hEdef, hfk, hgk, hgk1, hgkn, e1, e2, e3]
            linear_combination (b * PowerSeries.coeff (k - n - 1) G) * hF +
              PowerSeries.coeff (k - 2 * n) G * hG2 -
              PowerSeries.coeff (k - 2 * n) G * hfk
  have hDH : D * H = C0 := by
    ext k
    exact key k
  calc H = 1 * H := (one_mul H).symm
    _ = (I * D) * H := by rw [mul_comm I D, hDI]
    _ = I * (D * H) := by ring
    _ = I * C0 := by rw [hDH]
    _ = C0 * I := by ring

end MetaMathlibExt
