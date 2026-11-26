/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.WilsonQuotientPrimality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.WilsonQuotients

/-!
# The Wilson quotient sum Z(n) modulo n

Morozov's Wilson quotient sum `Z(n)` is an integer for every natural number `n ≥ 1`;
it satisfies `Z(n) ≡ 1 [ZMOD n]` when `n` is composite and `Z(n) ≡ -1 [ZMOD n]`
when `n` is `1` or prime. The proof evaluates the alternating factorial sum in
closed form by telescoping the reciprocal binomial coefficient identity of
B. Sury, T. Wang and F. Zhao, "Identities involving reciprocals of binomial
coefficients", then separates even, composite and prime moduli.

Statements from Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", *INTEGERS* 25 (2025), Article A93
(<https://math.colgate.edu/~integers/z93/z93.pdf>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- Alternating factorial summand `(-1)^k * k! * (N - k)!` as an integer. -/
private def altFactorialSummand (N k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * ((Nat.factorial k * Nat.factorial (N - k) : ℕ) : ℤ)

/-- Shifted summand `(-1)^k * k! * (N + 1 - k)!` whose consecutive differences telescope. -/
private def telescopeFun (N k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * ((Nat.factorial k * Nat.factorial (N + 1 - k) : ℕ) : ℤ)

/-- Alternating factorial sum `∑ k = 0..N, (-1)^k * k! * (N - k)!` as an integer. -/
private def altFactorialSum (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), altFactorialSummand N k

/-- Each summand, scaled by `N + 2`, is a consecutive difference of the shifted sum. -/
private theorem telescope_step (N k : ℕ) (hk : k ≤ N) :
    telescopeFun N k - telescopeFun N (k + 1)
      = ((N + 2 : ℕ) : ℤ) * altFactorialSummand N k := by
  have h1 : N + 1 - k = (N - k) + 1 := by omega
  have h2 : N + 1 - (k + 1) = N - k := by omega
  have hcast : (N : ℤ) = ((N - k : ℕ) : ℤ) + (k : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel hk).symm
  simp only [telescopeFun, altFactorialSummand]
  rw [h1, h2, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  push_cast
  rw [hcast]
  ring

/-- Closed form `(N + 2) * ∑ k, (-1)^k * k! * (N - k)! = (1 + (-1)^N) * (N + 1)!`. -/
private theorem altFactorialSum_mul (N : ℕ) :
    ((N + 2 : ℕ) : ℤ) * altFactorialSum N
      = (1 + (-1 : ℤ) ^ N) * ((Nat.factorial (N + 1) : ℕ) : ℤ) := by
  have hterm : ∀ k ∈ Finset.range (N + 1),
      telescopeFun N k - telescopeFun N (k + 1)
        = ((N + 2 : ℕ) : ℤ) * altFactorialSummand N k := by
    intro k hk
    exact telescope_step N k (by have := Finset.mem_range.mp hk; omega)
  calc ((N + 2 : ℕ) : ℤ) * altFactorialSum N
      = ∑ k ∈ Finset.range (N + 1), (telescopeFun N k - telescopeFun N (k + 1)) := by
        simp only [altFactorialSum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k hk => (hterm k hk).symm)
    _ = telescopeFun N 0 - telescopeFun N (N + 1) := Finset.sum_range_sub' _ _
    _ = (1 + (-1 : ℤ) ^ N) * ((Nat.factorial (N + 1) : ℕ) : ℤ) := by
        simp only [telescopeFun, show N + 1 - 0 = N + 1 by omega,
          show N + 1 - (N + 1) = 0 by omega, pow_zero, Nat.factorial_zero,
          one_mul, mul_one, pow_succ]
        ring

/-- Morozov's sum splits as `Z(n) = 1 + (alternating factorial sum) / n`. -/
private theorem wilsonQuotientZ_eq (n : ℕ) (hn : 1 ≤ n) :
    wilsonQuotientZ n = 1 + ((altFactorialSum (n - 1) : ℤ) : ℚ) / (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hterm : ∀ k ∈ Finset.range n,
      wilsonQuotientM k n
        = 1 / (n : ℚ) + ((altFactorialSummand (n - 1) k : ℤ) : ℚ) / (n : ℚ) := by
    intro k hk
    have hsub : n - k - 1 = (n - 1) - k := by
      have := Finset.mem_range.mp hk; omega
    simp only [wilsonQuotientM, altFactorialSummand]
    rw [hsub]
    push_cast
    rw [add_div]
  have hcast : ((altFactorialSum (n - 1) : ℤ) : ℚ)
      = ∑ k ∈ Finset.range n, ((altFactorialSummand (n - 1) k : ℤ) : ℚ) := by
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp only [altFactorialSum, hn1, Int.cast_sum]
  calc wilsonQuotientZ n
      = ∑ k ∈ Finset.range n,
          (1 / (n : ℚ) + ((altFactorialSummand (n - 1) k : ℤ) : ℚ) / (n : ℚ)) := by
        simp only [wilsonQuotientZ]
        exact Finset.sum_congr rfl hterm
    _ = 1 + ((altFactorialSum (n - 1) : ℤ) : ℚ) / (n : ℚ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one_div_cancel hn0, ← Finset.sum_div, ← hcast]

/-- A product of two distinct positive factors below `m` divides `m!`. -/
private theorem mul_dvd_factorial_of_lt (x y m : ℕ) (hx : 0 < x) (hxy : x < y)
    (hym : y ≤ m) : x * y ∣ m.factorial := by
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  have h1 : x ∣ z.factorial := Nat.dvd_factorial hx (by omega)
  have h2 : (z + 1) * x ∣ (z + 1) * z.factorial := mul_dvd_mul dvd_rfl h1
  rw [← Nat.factorial_succ, mul_comm (z + 1) x] at h2
  exact dvd_trans h2 (Nat.factorial_dvd_factorial hym)

/-- A composite number other than `4` divides `(n - 1)!`. -/
private theorem dvd_factorial_sub_one_of_composite (n : ℕ) (hn : 2 ≤ n)
    (hp : ¬n.Prime) (hn4 : n ≠ 4) : n ∣ (n - 1).factorial := by
  obtain ⟨m, hmn, hm1, hmn'⟩ := Nat.exists_dvd_of_not_prime hn hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hmn
    omega
  have hm2 : 2 ≤ m := by omega
  obtain ⟨k, hnk⟩ := hmn
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hnk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hnk
    exact hmn' hnk.symm
  have hk2 : 2 ≤ k := by omega
  have hmn1 : m ≤ n - 1 := by
    have hk2' : 2 + (k - 2) = k := by omega
    have hdecomp : m * k = 2 * m + m * (k - 2) := by
      calc m * k = m * (2 + (k - 2)) := by rw [hk2']
        _ = 2 * m + m * (k - 2) := by ring
    omega
  have hkn1 : k ≤ n - 1 := by
    have hm2' : 2 + (m - 2) = m := by omega
    have hdecomp : m * k = 2 * k + (m - 2) * k := by
      calc m * k = (2 + (m - 2)) * k := by rw [hm2']
        _ = 2 * k + (m - 2) * k := by ring
    omega
  rcases eq_or_ne m k with heq | hne
  · subst heq
    have hm2' : m ≠ 2 := by
      rintro rfl
      exact hn4 (by rw [hnk])
    have hm3 : 3 ≤ m := by omega
    have h2m : 2 * m ≤ n - 1 := by
      have h3 : 3 + (m - 3) = m := by omega
      have hsplit : m * m = 3 * m + m * (m - 3) := by
        calc m * m = m * (3 + (m - 3)) := by rw [h3]
          _ = 3 * m + m * (m - 3) := by ring
      omega
    have hdiv : m * (2 * m) ∣ (n - 1).factorial :=
      mul_dvd_factorial_of_lt m (2 * m) (n - 1) (by omega) (by omega) h2m
    have hle : m * m ∣ m * (2 * m) := mul_dvd_mul_left m (dvd_mul_left m 2)
    conv_lhs => rw [hnk]
    exact dvd_trans hle hdiv
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · conv_lhs => rw [hnk]
      exact mul_dvd_factorial_of_lt m k (n - 1) (by omega) hlt hkn1
    · have hnk' : n = k * m := by rw [hnk, mul_comm]
      conv_lhs => rw [hnk']
      exact mul_dvd_factorial_of_lt k m (n - 1) (by omega) hgt hmn1

/-- **The Wilson quotient sum Z(n) modulo n.** Let $n \ge 1$ be a natural number. Morozov's
Wilson quotient sum $Z(n)$ is an integer; moreover $Z(n) \equiv 1 \pmod{n}$ if $n$ is neither
$1$ nor prime, and $Z(n) \equiv -1 \pmod{n}$ if $n = 1$ or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 3. -/
theorem exists_int_eq_wilsonQuotientZ_and_modEq
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n ∧
      ((¬(n = 1 ∨ n.Prime) → z ≡ 1 [ZMOD (n : ℤ)]) ∧
        ((n = 1 ∨ n.Prime) → z ≡ -1 [ZMOD (n : ℤ)])) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · refine ⟨2, ?_, ?_, ?_⟩
    · norm_num [wilsonQuotientZ, wilsonQuotientM, Finset.sum_range_succ]
    · intro h
      exact (h (Or.inl rfl)).elim
    · intro _
      exact Int.modEq_one
  · rcases Nat.even_or_odd n with heven | hodd
    · have hn2 : 2 ≤ n := by omega
      have hNodd : Odd (n - 1) := by
        obtain ⟨r, hr⟩ := heven
        refine ⟨r - 1, by omega⟩
      have hmaster := altFactorialSum_mul (n - 1)
      have he1 : n - 1 + 2 = n + 1 := by omega
      have he2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [he1, he2, hNodd.neg_one_pow] at hmaster
      have hF0 : altFactorialSum (n - 1) = 0 := by
        have h0 : ((n + 1 : ℕ) : ℤ) * altFactorialSum (n - 1) = 0 := by
          linear_combination hmaster
        have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
        have hcancel : ((n + 1 : ℕ) : ℤ) * altFactorialSum (n - 1)
            = ((n + 1 : ℕ) : ℤ) * 0 := by rw [mul_zero]; exact h0
        exact mul_left_cancel₀ hne hcancel
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [wilsonQuotientZ_eq n hn, hF0]
        norm_num
      · intro _
        rfl
      · intro h
        rcases h with h1 | hp
        · exact absurd h1 hn1
        · rcases hp.eq_two_or_odd with rfl | hodd2
          · refine Int.modEq_iff_dvd.mpr ⟨-1, by norm_num⟩
          · obtain ⟨r, hr⟩ := heven
            omega
    · have hn3 : 3 ≤ n := by
        obtain ⟨r, hr⟩ := hodd
        omega
      have hNeven : Even (n - 1) := by
        obtain ⟨r, hr⟩ := hodd
        refine ⟨r, by omega⟩
      have hmaster := altFactorialSum_mul (n - 1)
      have ho1 : n - 1 + 2 = n + 1 := by omega
      have ho2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [ho1, ho2, hNeven.neg_one_pow] at hmaster
      norm_num at hmaster
      set T := altFactorialSum (n - 1) with hTdef
      have hn0' : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hfac : ((n.factorial : ℕ) : ℤ) = (n : ℤ) * (((n - 1).factorial : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
      have hTeq : T = 2 * ((n.factorial : ℕ) : ℤ) - (n : ℤ) * T := by
        linear_combination hmaster
      have hdvdT : (n : ℤ) ∣ T := by
        have hfn : (n : ℤ) ∣ ((n.factorial : ℕ) : ℤ) := by
          exact_mod_cast Nat.dvd_factorial (by omega : 0 < n) le_rfl
        have h1 : (n : ℤ) ∣ 2 * ((n.factorial : ℕ) : ℤ) := dvd_mul_of_dvd_right hfn 2
        have h2 : (n : ℤ) ∣ (n : ℤ) * T := dvd_mul_right _ _
        rw [hTeq]
        exact dvd_sub h1 h2
      have ⟨q, hq⟩ := hdvdT
      refine ⟨1 + q, ?_, ?_, ?_⟩
      · have hcast : ((T : ℤ) : ℚ) = (n : ℚ) * (q : ℚ) := by exact_mod_cast hq
        have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
        have hdiv : ((T : ℤ) : ℚ) / (n : ℚ) = (q : ℚ) := by
          rw [hcast]
          exact mul_div_cancel_left₀ _ hn0
        rw [wilsonQuotientZ_eq n hn, ← hTdef]
        push_cast
        rw [hdiv]
      · intro hcon
        have hp' : ¬n.Prime := fun hp => hcon (Or.inr hp)
        have hn4 : n ≠ 4 := by
          obtain ⟨r, hr⟩ := hodd
          omega
        have hwcomp : (n : ℤ) ∣ (((n - 1).factorial : ℕ) : ℤ) := by
          exact_mod_cast dvd_factorial_sub_one_of_composite n (by omega) hp' hn4
        have hsq1 : (n : ℤ) ^ 2 ∣ 2 * ((n.factorial : ℕ) : ℤ) := by
          have hmul : (n : ℤ) * (n : ℤ) ∣ (n : ℤ) * (((n - 1).factorial : ℕ) : ℤ) :=
            mul_dvd_mul dvd_rfl hwcomp
          rw [← hfac] at hmul
          rw [pow_two]
          exact dvd_mul_of_dvd_right hmul 2
        have hsq2 : (n : ℤ) ^ 2 ∣ (n : ℤ) * T := by
          rw [pow_two]
          exact mul_dvd_mul dvd_rfl hdvdT
        have hsqT : (n : ℤ) ^ 2 ∣ T := by
          rw [hTeq]
          exact dvd_sub hsq1 hsq2
        have hnq : (n : ℤ) ∣ q := by
          obtain ⟨u, hu⟩ := hsqT
          have e : (n : ℤ) * q = (n : ℤ) * ((n : ℤ) * u) := by
            rw [← hq, hu]
            ring
          have heq : q = (n : ℤ) * u := mul_left_cancel₀ hn0' e
          exact ⟨u, heq⟩
        have h1mz : (1 : ℤ) - (1 + q) = -q := by ring
        rw [Int.modEq_iff_dvd, h1mz]
        exact dvd_neg.mpr hnq
      · intro hprime
        have hp : n.Prime := by
          rcases hprime with h1 | hp
          · exact absurd h1 hn1
          · exact hp
        have hcor := (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff n 0 hn
          (by omega)).mpr (Or.inr hp)
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
          show n - 0 - 1 = n - 1 by omega] at hcor
        have hwil : (n : ℤ) ∣ 1 + (((n - 1).factorial : ℕ) : ℤ) := by
          have hwdvd : (n : ℤ) ∣ -1 - (((n - 1).factorial : ℕ) : ℤ) :=
            Int.modEq_iff_dvd.mp hcor
          have hneg : (1 : ℤ) + (((n - 1).factorial : ℕ) : ℤ)
              = -(-1 - (((n - 1).factorial : ℕ) : ℤ)) := by ring
          rw [hneg]
          exact dvd_neg.mpr hwdvd
        have e2 : ((n : ℤ) + 1) * q = 2 * (((n - 1).factorial : ℕ) : ℤ) := by
          have e1 : ((n : ℤ) + 1) * ((n : ℤ) * q)
              = 2 * ((n : ℤ) * (((n - 1).factorial : ℕ) : ℤ)) := by
            have htmp := hmaster
            rw [hq, hfac] at htmp
            exact htmp
          have e1' : (n : ℤ) * (((n : ℤ) + 1) * q)
              = (n : ℤ) * (2 * (((n - 1).factorial : ℕ) : ℤ)) := by
            linear_combination e1
          exact mul_left_cancel₀ hn0' e1'
        have hdiv : ((n : ℤ) + 1) * ((1 + q) + 1)
            = 2 * (n : ℤ) + 2 * (1 + (((n - 1).factorial : ℕ) : ℤ)) := by
          linear_combination e2
        have hmod0 : (n : ℤ) ∣ ((n : ℤ) + 1) * ((1 + q) + 1) := by
          rw [hdiv]
          exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hwil 2)
        have hmod1 : (n : ℤ) ∣ (1 + q) + 1 := by
          have hsub : (1 + q) + 1
              = ((n : ℤ) + 1) * ((1 + q) + 1) - (n : ℤ) * ((1 + q) + 1) := by ring
          rw [hsub]
          exact dvd_sub hmod0 (dvd_mul_right _ _)
        have hfin : (-1 : ℤ) - (1 + q) = -((1 + q) + 1) := by ring
        rw [Int.modEq_iff_dvd, hfin]
        exact dvd_neg.mpr hmod1

end MathlibExt.NumberTheory.WilsonQuotientsWanted
