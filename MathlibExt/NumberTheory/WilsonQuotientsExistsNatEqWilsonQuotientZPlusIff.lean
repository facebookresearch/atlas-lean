/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.ModEq
import MathlibExt.NumberTheory.WilsonQuotients

/-!
# When the sign-adjusted Wilson quotient sum is a natural number

Morozov's sign-adjusted Wilson quotients `wilsonQuotientMPlus` and their sum
`wilsonQuotientZPlus`, with the characterization of when the sum is a natural number.

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93
(<https://math.colgate.edu/~integers/z93/z93.pdf>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- **Morozov's sign-adjusted Wilson quotients.** For natural numbers $k$ and $n$, $M_k^+(n)$ is
the rational number

$$M_k^+(n) = \frac{(-1)^k + k! \, (n - k - 1)!}{n},$$

where $n - k - 1$ is truncated subtraction of natural numbers and division by $0$ gives $0$. -/
def wilsonQuotientMPlus (k n : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k + (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- **Morozov's sign-adjusted Wilson quotient sum.** For a natural number $n$, $Z^+(n)$ is the
rational number $\sum_{k=0}^{n-1} M_k^+(n)$, where $M_k^+(n) = ((-1)^k + k!\,(n-k-1)!)/n$ is
Morozov's sign-adjusted quotient. -/
def wilsonQuotientZPlus (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientMPlus k n

private def factSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, Nat.factorial k * Nat.factorial (n - k - 1)

private def wilsonNum (n : ℕ) : ℕ := n % 2 + factSum n

private theorem sum_neg_one_pow_eq_mod_two {R : Type*} [Ring R] (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1 : R) ^ k = ((n % 2 : ℕ) : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n % 2 = 0
    · have hn2 : n = 2 * (n / 2) := by omega
      have hsq : (-1 : R) ^ 2 = 1 := neg_one_sq
      have hpow : (-1 : R) ^ n = 1 := by rw [hn2, pow_mul, hsq, one_pow]
      have hmod : (n + 1) % 2 = 1 := by omega
      rw [hpow, h, hmod]
      simp
    · have h1 : n % 2 = 1 := by omega
      have hn2 : n = 2 * (n / 2) + 1 := by omega
      have hsq : (-1 : R) ^ 2 = 1 := neg_one_sq
      have hpow : (-1 : R) ^ n = -1 := by
        rw [hn2, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
      have hmod : (n + 1) % 2 = 0 := by omega
      rw [hpow, h1, hmod]
      simp

private theorem sum_neg_one_pow_int_eq_mod_two (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k = ((n % 2 : ℕ) : ℤ) :=
  sum_neg_one_pow_eq_mod_two n

private theorem sum_neg_one_pow_rat_eq_mod_two (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k = ((n % 2 : ℕ) : ℚ) :=
  sum_neg_one_pow_eq_mod_two n

private theorem wilsonQuotientZPlus_eq_div (n : ℕ) :
    wilsonQuotientZPlus n = ((wilsonNum n : ℕ) : ℚ) / (n : ℚ) := by
  dsimp [wilsonQuotientZPlus, wilsonQuotientMPlus, wilsonNum, factSum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  rw [sum_neg_one_pow_rat_eq_mod_two]
  simp only [← Nat.cast_mul]
  rw [← Nat.cast_sum, Nat.cast_add]

private theorem exists_nat_iff_dvd (n : ℕ) (hn : 1 ≤ n) :
    (∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus n) ↔ n ∣ wilsonNum n := by
  rw [wilsonQuotientZPlus_eq_div]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  constructor
  · rintro ⟨m, hm⟩
    have hmul : (m : ℚ) * (n : ℚ) = ((wilsonNum n : ℕ) : ℚ) := by
      rw [eq_div_iff hn0] at hm
      exact hm
    have hnat : m * n = wilsonNum n := by exact_mod_cast hmul
    exact ⟨m, by rw [← hnat, mul_comm]⟩
  · rintro ⟨c, hc⟩
    use c
    rw [eq_div_iff hn0, hc, Nat.cast_mul, mul_comm]

private theorem prime_dvd_wilsonNum (n : ℕ) (hp : n.Prime) : n ∣ wilsonNum n := by
  have hn1 : 1 ≤ n := hp.pos
  have h_each : ∀ k ∈ Finset.range n,
      (n : ℤ) ∣ (-1 : ℤ) ^ k + ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ) := by
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have hmod := (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff n k hn1 hk_lt).mpr
      (Or.inr hp)
    have h_dvd : (n : ℤ) ∣ 1 + (-1 : ℤ) ^ k *
        ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ) := by
      have h0 : (-1 : ℤ) ^ k * ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ) + 1 ≡
          0 [ZMOD (n : ℤ)] := by
        have h1 := hmod.add_right (1 : ℤ)
        simpa using h1
      have h2 := Int.modEq_zero_iff_dvd.mp h0
      simpa [add_comm] using h2
    have hs_sq : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
      have h1 : (-1 : ℤ) * (-1 : ℤ) = 1 := by decide
      rw [← mul_pow, h1, one_pow]
    have h_eq : (-1 : ℤ) ^ k + ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ) =
        (-1 : ℤ) ^ k * (1 + (-1 : ℤ) ^ k *
          ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ)) := by
      rw [mul_add, mul_one, ← mul_assoc, hs_sq, one_mul]
    rw [h_eq]
    exact dvd_mul_of_dvd_right h_dvd _
  have h_sum : (n : ℤ) ∣ ∑ k ∈ Finset.range n,
      ((-1 : ℤ) ^ k + ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ)) :=
    Finset.dvd_sum h_each
  have h_sum_eq : ∑ k ∈ Finset.range n,
      ((-1 : ℤ) ^ k + ((Nat.factorial k * Nat.factorial (n - k - 1) : ℕ) : ℤ)) =
      ((wilsonNum n : ℕ) : ℤ) := by
    simp only [wilsonNum, factSum, Finset.sum_add_distrib, sum_neg_one_pow_int_eq_mod_two,
      ← Nat.cast_sum, Nat.cast_add]
  rw [h_sum_eq] at h_sum
  exact Int.natCast_dvd_natCast.mp h_sum

private theorem even_dvd_wilsonNum (n : ℕ) (h_even : n % 2 = 0) : n ∣ wilsonNum n := by
  have hm : n = 2 * (n / 2) := by omega
  have hT : wilsonNum n = factSum n := by
    dsimp [wilsonNum]
    rw [h_even, Nat.zero_add]
  rw [hT, hm]
  dsimp [factSum]
  have h_split : ∑ k ∈ Finset.range (2 * (n / 2)),
        Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) =
      ∑ k ∈ Finset.range (n / 2), Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) +
      ∑ k ∈ Finset.range (n / 2),
        Nat.factorial (n / 2 + k) * Nat.factorial (2 * (n / 2) - (n / 2 + k) - 1) := by
    rw [show 2 * (n / 2) = n / 2 + n / 2 from two_mul _]
    exact Finset.sum_range_add
      (fun k => Nat.factorial k * Nat.factorial (n / 2 + n / 2 - k - 1)) _ _
  rw [h_split]
  have h_refl : ∑ k ∈ Finset.range (n / 2),
        Nat.factorial (n / 2 + k) * Nat.factorial (2 * (n / 2) - (n / 2 + k) - 1) =
      ∑ k ∈ Finset.range (n / 2),
        Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) := by
    have h_term : ∀ k ∈ Finset.range (n / 2),
        Nat.factorial (n / 2 + k) * Nat.factorial (2 * (n / 2) - (n / 2 + k) - 1) =
        Nat.factorial (n / 2 - 1 - k) * Nat.factorial (2 * (n / 2) - (n / 2 - 1 - k) - 1) := by
      intro k hk
      have hk_lt : k < n / 2 := Finset.mem_range.mp hk
      have h1 : 2 * (n / 2) - (n / 2 + k) - 1 = n / 2 - 1 - k := by omega
      have h2 : 2 * (n / 2) - (n / 2 - 1 - k) - 1 = n / 2 + k := by omega
      rw [h1, h2, mul_comm]
    have h_sum : ∑ k ∈ Finset.range (n / 2),
          Nat.factorial (n / 2 + k) * Nat.factorial (2 * (n / 2) - (n / 2 + k) - 1) =
        ∑ k ∈ Finset.range (n / 2),
          Nat.factorial (n / 2 - 1 - k) * Nat.factorial (2 * (n / 2) - (n / 2 - 1 - k) - 1) :=
      Finset.sum_congr rfl h_term
    rw [h_sum]
    exact Finset.sum_range_reflect
      (fun k => Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1)) _
  rw [h_refl]
  have h_two : ∑ k ∈ Finset.range (n / 2), Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) +
      ∑ k ∈ Finset.range (n / 2), Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) =
      2 * ∑ k ∈ Finset.range (n / 2), Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) :=
    (two_mul _).symm
  rw [h_two]
  obtain ⟨t, ht⟩ : n / 2 ∣ ∑ k ∈ Finset.range (n / 2),
      Nat.factorial k * Nat.factorial (2 * (n / 2) - k - 1) := by
    apply Finset.dvd_sum
    intro k hk
    have hk_lt : k < n / 2 := Finset.mem_range.mp hk
    by_cases hm0 : n / 2 = 0
    · have hfalse : False := by omega
      exact False.elim hfalse
    · have hle : n / 2 ≤ 2 * (n / 2) - k - 1 := by omega
      have hpos : 0 < n / 2 := by omega
      have hdvd : n / 2 ∣ Nat.factorial (2 * (n / 2) - k - 1) := Nat.dvd_factorial hpos hle
      exact dvd_mul_of_dvd_right hdvd _
  exact ⟨t, by rw [ht, mul_assoc]⟩

private theorem odd_composite_not_dvd_wilsonNum (n : ℕ) (hn : 1 ≤ n) (hn1 : n ≠ 1)
    (hp : ¬n.Prime) (h_odd : n % 2 ≠ 0) : ¬n ∣ wilsonNum n := by
  have hmod1 : n % 2 = 1 := by omega
  have hT : wilsonNum n = 1 + factSum n := by
    dsimp [wilsonNum]
    rw [hmod1]
  rw [hT]
  intro hdvd
  set p := n.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hn1
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_lt : p < n := by
    have hle : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hp_dvd
    have hne : p ≠ n := by
      intro heq
      apply hp
      rw [← heq]
      exact hp_prime
    omega
  have hp_pos : 0 < p := hp_prime.pos
  obtain ⟨q, hq⟩ := hp_dvd
  have hq_ge2 : 2 ≤ q := by
    by_contra hlt
    have hq_pos : 0 < q := by
      by_contra hz
      have hq0 : q = 0 := by omega
      rw [hq0, mul_zero] at hq
      omega
    have hq1 : q = 1 := by omega
    rw [hq1, mul_one] at hq
    omega
  have hn_ge : 2 * p ≤ n := by
    have hex : ∃ r, q = 2 + r := ⟨q - 2, by omega⟩
    obtain ⟨r, hr⟩ := hex
    rw [hq, hr, mul_add, mul_comm 2 p]
    exact Nat.le_add_right _ _
  have hp_dvd_sum : p ∣ factSum n := by
    dsimp [factSum]
    apply Finset.dvd_sum
    intro k hk
    have hk_lt : k < n := Finset.mem_range.mp hk
    have h_or : p ≤ k ∨ p ≤ n - k - 1 := by omega
    cases h_or with
    | inl hle =>
      have hdvd : p ∣ Nat.factorial k := Nat.dvd_factorial hp_pos hle
      exact dvd_mul_of_dvd_left hdvd _
    | inr hle =>
      have hdvd : p ∣ Nat.factorial (n - k - 1) := Nat.dvd_factorial hp_pos hle
      exact dvd_mul_of_dvd_right hdvd _
  have hp_dvd2 : p ∣ n := Nat.minFac_dvd n
  have hp_dvd_succ : p ∣ 1 + factSum n := dvd_trans hp_dvd2 hdvd
  have hsub := Nat.dvd_sub hp_dvd_succ hp_dvd_sum
  have hp_dvd_one : p ∣ 1 := by simpa using hsub
  have hp_eq1 : p = 1 := Nat.dvd_one.mp hp_dvd_one
  have hp_ge2 : 2 ≤ p := hp_prime.two_le
  omega

/-- **When the sign-adjusted Wilson quotient sum is a natural number.** For every natural number
$n \ge 1$, Morozov's sign-adjusted Wilson quotient sum $Z^+(n)$ is a natural number if and only
if $n$ is even, $n = 1$, or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 2. -/
theorem exists_nat_eq_wilsonQuotientZPlus_iff
    (n : ℕ) (hn : 1 ≤ n) :
    (∃ m : ℕ, (m : ℚ) = wilsonQuotientZPlus n) ↔
      n % 2 = 0 ∨ n = 1 ∨ n.Prime := by
  rw [exists_nat_iff_dvd n hn]
  by_cases hn1 : n = 1
  · subst hn1
    exact iff_of_true (one_dvd _) (Or.inr (Or.inl rfl))
  · have h_rhs : (n % 2 = 0 ∨ n = 1 ∨ n.Prime) ↔ (n % 2 = 0 ∨ n.Prime) := by simp [hn1]
    rw [h_rhs]
    constructor
    · intro hdvd
      by_cases h_even : n % 2 = 0
      · exact Or.inl h_even
      · by_cases hp : n.Prime
        · exact Or.inr hp
        · exact absurd hdvd (odd_composite_not_dvd_wilsonNum n hn hn1 hp h_even)
    · rintro (h_even | hp)
      · exact even_dvd_wilsonNum n h_even
      · exact prime_dvd_wilsonNum n hp

end MathlibExt.NumberTheory.WilsonQuotientsWanted
