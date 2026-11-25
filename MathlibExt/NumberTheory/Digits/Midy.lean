/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

namespace MetaMathlibExt

/-- **Midy's theorem, general form.** Let $p$ be a prime and $n$ a natural number such that $p$
divides $10^{2n} - 1$ but does not divide $10^n - 1$. Let $Q = (10^{2n} - 1)/p$ and write
$Q = 10^n H + L$ with $0 \le L < 10^n$, so that $L$ is the number formed by the last $n$ decimal
digits of $Q$ and $H$ the number formed by the remaining digits. Then $H + L = 10^n - 1$.

Midy's theorem in its usual form, where the decimal period of $1/p$ is exactly $2n$, is the
special case in which $p$ does not divide $10^m - 1$ for any $0 < m < 2n$. -/
theorem midy_theorem_general {p n : ℕ} (hp : Nat.Prime p)
    (hdiv : p ∣ 10 ^ (2 * n) - 1) (hnot : ¬p ∣ 10 ^ n - 1) :
    Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
      Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
      10 ^ n - 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => hnot (by simp [h])
  have hp_pos : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hA1 : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
  have hA10 : 10 ≤ 10 ^ n := by
    calc 10 = 10 ^ 1 := by simp
    _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : 10 ^ (2 * n) = (10 ^ n) ^ 2 := by ring
  have hfac : 10 ^ (2 * n) - 1 = (10 ^ n - 1) * (10 ^ n + 1) := by
    obtain ⟨c, hc⟩ : ∃ c, 10 ^ n = 1 + c := ⟨10 ^ n - 1, by omega⟩
    rw [hsq, hc]
    have hsq1 : (1 + c) ^ 2 = 1 + (c * c + 2 * c) := by ring
    have hmul : ((1 + c) - 1) * ((1 + c) + 1) = c * c + 2 * c := by
      have e1 : (1 + c) - 1 = c := by omega
      have e2 : (1 + c) + 1 = c + 2 := by omega
      rw [e1, e2]; ring
    omega
  have hdvd : p ∣ (10 ^ n - 1) * (10 ^ n + 1) := hfac ▸ hdiv
  have hplus : p ∣ 10 ^ n + 1 := by
    rcases (hp.dvd_mul.mp hdvd) with h | h
    · exact absurd h hnot
    · exact h
  obtain ⟨t, ht⟩ := hplus
  have hpk : p * ((10 ^ (2 * n) - 1) / p) = 10 ^ (2 * n) - 1 :=
    Nat.mul_div_cancel' hdiv
  have hkey : p * ((10 ^ n - 1) * t) = 10 ^ (2 * n) - 1 := by
    calc p * ((10 ^ n - 1) * t) = (10 ^ n - 1) * (p * t) := by ring
    _ = (10 ^ n - 1) * (10 ^ n + 1) := by rw [← ht]
    _ = 10 ^ (2 * n) - 1 := hfac.symm
  have hk : (10 ^ (2 * n) - 1) / p = (10 ^ n - 1) * t :=
    Nat.mul_left_cancel hp_pos (hkey.trans hpk.symm) |>.symm
  have ht_ne : t ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at ht
    omega
  have ht_pos : 0 < t := Nat.pos_of_ne_zero ht_ne
  have h2t : 2 * t ≤ 10 ^ n + 1 := by
    calc 2 * t ≤ p * t := by gcongr
    _ = 10 ^ n + 1 := ht.symm
  have htle : t ≤ 10 ^ n := by omega
  have ht_lt : t < 10 ^ n := by omega
  obtain ⟨s, hs⟩ : ∃ s, 10 ^ n = t + s := Nat.exists_eq_add_of_le htle
  obtain ⟨r, hr⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  subst hr
  have hs_eq : 10 ^ n - (r + 1) = s := by omega
  have hr_eq : (r + 1) - 1 = r := by omega
  have hA : 10 ^ n - 1 = s + r := by omega
  have hk_eq : (10 ^ (2 * n) - 1) / p = s + 10 ^ n * r := by
    rw [hk, hA, hs]
    ring
  have hApos : 0 < 10 ^ n := by omega
  have hs_lt : s < 10 ^ n := by omega
  have hmod : ((10 ^ (2 * n) - 1) / p) % 10 ^ n = s := by
    rw [hk_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs_lt]
  have hdiv2 : ((10 ^ (2 * n) - 1) / p) / 10 ^ n = r := by
    rw [hk_eq, Nat.add_mul_div_left _ _ hApos, Nat.div_eq_of_lt hs_lt,
      Nat.zero_add]
  have e1 : Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
      ((10 ^ (2 * n) - 1) / p) % 10 ^ n :=
    (Nat.self_mod_pow_eq_ofDigits_take n _ (by norm_num)).symm
  have e2 : Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
      ((10 ^ (2 * n) - 1) / p) / 10 ^ n :=
    (Nat.self_div_pow_eq_ofDigits_drop n _ (by norm_num)).symm
  rw [e1, e2, hmod, hdiv2]
  omega

set_option linter.unusedVariables false in
/-- **Midy's theorem.** Let $p \ne 2, 5$ be a prime and $n \ge 1$ an integer such that $p$ divides
$10^{2n} - 1$ and does not divide $10^m - 1$ for any $0 < m < 2n$, that is, the decimal period of
$1/p$ is $2n$. Let $Q = (10^{2n} - 1)/p$, whose decimal expansion padded with leading zeros to
$2n$ digits is the repetend of $1/p$, and write $Q = 10^n H + L$ with $0 \le L < 10^n$, so that
$H$ and $L$ are the two $n$-digit halves of the repetend. Then $H + L = 10^n - 1$.

The proof uses neither $p \ne 2, 5$ nor the minimality of the period beyond $p \nmid 10^n - 1$;
see Midy's theorem, general form.

Proves `Wanted` entry `midy_theorem`.

Source: https://en.wikipedia.org/wiki/Midy%27s_theorem, statement `midy-s1`.
-/
theorem midy_theorem {p n : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2)
    (h5 : p ≠ 5) (hn : 0 < n) (hdiv : p ∣ 10 ^ (2 * n) - 1)
    (hmin : ∀ m : ℕ, 0 < m → m < 2 * n → ¬p ∣ 10 ^ m - 1) :
    Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
      Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
      10 ^ n - 1 := by
  exact midy_theorem_general hp hdiv (hmin n hn (by omega))

end MetaMathlibExt
