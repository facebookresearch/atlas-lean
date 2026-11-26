/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # Deficient `F`-perfect numbers of the form `2 ^ a * p`

The only deficient `F`-perfect number of the form `2 ^ a * p` with `p` prime
is `6 = 2 ^ 1 * 3`. Reducing the deficient-perfect equation modulo `4` rules
out odd `p` with `a ≥ 2` and all powers of two; for `a = 1` the equation forces
`p ≤ 6`, leaving `p = 3`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 7.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem geom_sum_four (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), 2 ^ (i * 2)) % 4 = 1 := by
  rw [Finset.sum_range_succ', zero_mul, pow_zero]
  have htail : 4 ∣ ∑ k ∈ Finset.range e, 2 ^ ((k + 1) * 2) := by
    apply Finset.dvd_sum
    intro i _
    change (2 : ℕ) ^ 2 ∣ 2 ^ ((i + 1) * 2)
    exact Nat.pow_dvd_pow 2 (by omega)
  omega

private theorem sq_mod_four (d : ℕ) : d ^ 2 % 4 = 0 ∨ d ^ 2 % 4 = 1 := by
  have h4 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
  rcases h4 with h | h | h | h <;> rw [pow_two, Nat.mul_mod, h] <;> decide

private theorem odd_sq_mod_four (p : ℕ) (hpo : Odd p) : p ^ 2 % 4 = 1 := by
  have h2 : p % 2 = 1 := Nat.odd_iff.mp hpo
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h | h <;> rw [pow_two, Nat.mul_mod, h]

private theorem not_isDeficientFPerfect_two_pow (b : ℕ) :
    ¬ IsDeficientFPerfect (2 ^ b) := by
  intro h
  obtain ⟨d, hd, hlt, hsum⟩ := h
  rcases lt_or_ge b 2 with hb | hb
  · have hbo : b = 0 ∨ b = 1 := by omega
    rcases hbo with rfl | rfl
    · simp only [pow_zero] at hd hlt
      have hd1 : d = 1 := Nat.dvd_one.mp hd
      omega
    · simp only [pow_one] at hd hlt hsum
      have hσ : (∑ e ∈ (2 : ℕ).divisors, e ^ 2) = 5 := by
        have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
        rw [Nat.prime_two.divisors, Finset.sum_insert h1, Finset.sum_singleton]
        decide
      rw [hσ] at hsum
      have hd1 : d = 1 :=
        (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (ne_of_lt hlt)
      rw [hd1, one_pow] at hsum
      exact absurd hsum (by decide)
  · have hσ : (∑ e ∈ (2 ^ b).divisors, e ^ 2) =
        ∑ i ∈ Finset.range (b + 1), 2 ^ (i * 2) := by
      rw [← ArithmeticFunction.sigma_apply,
        ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two]
    have hS : (∑ e ∈ (2 ^ b).divisors, e ^ 2) % 4 = 1 := by
      rw [hσ]
      exact geom_sum_four b
    have h2b : (2 : ℕ) ^ 2 ∣ 2 ^ b := Nat.pow_dvd_pow 2 hb
    have h4dvd : 4 ∣ 2 ^ b := h2b
    have hn0 : (2 ^ b) % 4 = 0 := by omega
    have hN : ((2 ^ b) ^ 2) % 4 = 0 := by
      have h4dvd2 : 4 ∣ (2 ^ b) ^ 2 := by
        rw [pow_two]
        exact dvd_mul_of_dvd_left h4dvd _
      omega
    have hd01 := sq_mod_four d
    omega

/-- **Deficient $F$-perfect numbers of the form $2^a p$.** Let $p$ be a prime and $a$ a natural
number. If $2^a p$ is deficient $F$-perfect, then $p = 3$ and $a = 1$, so the number is $6$.

The number $6$ is indeed deficient $F$-perfect, with $d = 2$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 7. -/
theorem isDeficientFPerfect_two_pow_mul_prime_imp
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect (2 ^ a * p) → p = 3 ∧ a = 1 := by
  intro h
  by_cases hp2 : p = 2
  · subst hp2
    have hpow : (2 : ℕ) ^ a * 2 = 2 ^ (a + 1) := (pow_succ 2 a).symm
    rw [hpow] at h
    exact absurd h (not_isDeficientFPerfect_two_pow (a + 1))
  · have hpo : Odd p := hp.odd_of_ne_two hp2
    rcases lt_or_ge a 2 with ha2 | ha2
    · have hao : a = 0 ∨ a = 1 := by omega
      rcases hao with rfl | rfl
      · simp only [pow_zero, one_mul] at h
        exact absurd h (not_isKLDeficientPerfect_of_prime_odd 2 3 p hp hpo)
      · rw [pow_one] at h
        obtain ⟨d, hd, hlt, hsum⟩ := h
        have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpo
        have htwo : ArithmeticFunction.sigma 2 2 = 5 := by
          have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
          rw [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors,
            Finset.sum_insert h1, Finset.sum_singleton]
          decide
        have hps : ArithmeticFunction.sigma 2 p = 1 + p ^ 2 := by
          have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
            simpa only [Finset.mem_singleton] using hp.ne_one.symm
          rw [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert h1,
            Finset.sum_singleton, one_pow]
        have hσ : (∑ e ∈ (2 * p).divisors, e ^ 2) = 5 * (1 + p ^ 2) := by
          rw [← ArithmeticFunction.sigma_apply,
            ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
            htwo, hps]
        rw [hσ] at hsum
        have hsq : (2 * p) ^ 2 = 4 * p ^ 2 := by
          rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from rfl]
        have heq : 5 + p ^ 2 + d ^ 2 = 6 * p := by omega
        have hpp : p * p ≤ 6 * p := by
          have hle : p ^ 2 ≤ 6 * p := by omega
          rwa [pow_two] at hle
        have hp6 : p ≤ 6 := le_of_mul_le_mul_right hpp hp.pos
        have hp2le := hp.two_le
        have hpor : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
        rcases hpor with rfl | rfl | rfl | rfl | rfl
        · exact absurd hpo (by decide)
        · exact ⟨rfl, rfl⟩
        · exact absurd hp (by decide)
        · have h52 : (5 : ℕ) ^ 2 = 25 := by decide
          rw [h52] at heq
          have hd2 : d ^ 2 = 0 := by omega
          have hd0 : d = 0 := (pow_eq_zero_iff two_ne_zero).mp hd2
          rw [hd0] at hd
          exact absurd hd (by decide)
        · exact absurd hp (by decide)
    · obtain ⟨d, hd, hlt, hsum⟩ := h
      have hcop : Nat.Coprime (2 ^ a) p :=
        (Nat.coprime_two_left.mpr hpo).pow_left a
      have hps : ArithmeticFunction.sigma 2 p = 1 + p ^ 2 := by
        have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
          simpa only [Finset.mem_singleton] using hp.ne_one.symm
        rw [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert h1,
          Finset.sum_singleton, one_pow]
      have hσ : (∑ e ∈ (2 ^ a * p).divisors, e ^ 2) =
          (∑ i ∈ Finset.range (a + 1), 2 ^ (i * 2)) * (1 + p ^ 2) := by
        rw [← ArithmeticFunction.sigma_apply,
          ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
          ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two, hps]
      have hS : (∑ e ∈ (2 ^ a * p).divisors, e ^ 2) % 4 = 2 := by
        have hT : (1 + p ^ 2) % 4 = 2 := by
          have hp2 := odd_sq_mod_four p hpo
          omega
        rw [hσ, Nat.mul_mod, geom_sum_four a, hT]
      have h2a : (2 : ℕ) ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha2
      have h4dvd : 4 ∣ 2 ^ a * p := dvd_mul_of_dvd_left h2a p
      have hn0 : (2 ^ a * p) % 4 = 0 := by omega
      have hN : ((2 ^ a * p) ^ 2) % 4 = 0 := by
        have h4dvd2 : 4 ∣ (2 ^ a * p) ^ 2 := by
          rw [pow_two]
          exact dvd_mul_of_dvd_left h4dvd _
        omega
      have hd01 := sq_mod_four d
      omega

end MathlibExt.NumberTheory.FkPerfectWanted
