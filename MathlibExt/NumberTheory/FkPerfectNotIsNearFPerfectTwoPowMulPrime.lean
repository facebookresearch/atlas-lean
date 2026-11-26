/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FkPerfect
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # No near `F`-perfect number of the form `2 ^ a * p`

This module proves that no number of the form $2^a p$ with $p$ prime is near $F$-perfect.
Near $F$-perfect numbers are defined in `MathlibExt.NumberTheory.FkPerfect`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 9.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sq_mod_four_ne_two (d : ℕ) : d ^ 2 % 4 ≠ 2 := by
  rcases Nat.even_or_odd d with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hsq : d ^ 2 = 4 * (m ^ 2) := by rw [hm]; ring
    omega
  · have hodd2 : Odd (d ^ 2) := hodd.pow
    obtain ⟨m, hm⟩ := hodd2
    omega

private theorem sq_mod_eight_ne_five (d : ℕ) : d ^ 2 % 8 ≠ 5 := by
  rcases Nat.even_or_odd d with hev | hodd
  · have hev2 : Even (d ^ 2) := hev.pow_of_ne_zero (by decide)
    obtain ⟨r, hr⟩ := hev2
    omega
  · obtain ⟨c, hc⟩ := Nat.eight_dvd_sq_sub_one_of_odd hodd
    have hsq1 : 1 ≤ d ^ 2 := pow_pos hodd.pos 2
    omega

/-- **No near $F$-perfect number of the form $2^a p$.** For every prime $p$ and every natural
number $a$, the number $n = 2^a p$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 9. -/
theorem not_isNearFPerfect_two_pow_mul_prime
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 ^ a * p) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases h2 : p = 2
  · subst h2
    have hn : (2 : ℕ) ^ a * 2 = 2 ^ (a + 1) := (pow_succ 2 a).symm
    rw [hn] at hdvd hlt hsum
    have hsig : (∑ e ∈ (2 ^ (a + 1)).divisors, e ^ 2)
        = ∑ j ∈ Finset.range (a + 1 + 1), 2 ^ (j * 2) := by
      rw [← ArithmeticFunction.sigma_apply,
        ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two]
    rw [hsig] at hsum
    by_cases ha : 2 ≤ a
    · have hS5 : (∑ j ∈ Finset.range (a + 1 + 1), 2 ^ (j * 2)) % 8 = 5 := by
        have hsplit : ∑ j ∈ Finset.range (a + 1 + 1), 2 ^ (j * 2)
            = (∑ j ∈ Finset.range (a + 1 - 1), 2 ^ ((2 + j) * 2)) + 5 := by
          have h2' : (2 : ℕ) + (a + 1 - 1) = a + 1 + 1 := by omega
          rw [← h2', Finset.sum_range_add]
          have hfin : ∑ x ∈ Finset.range 2, (2 : ℕ) ^ (x * 2) = 5 := by decide
          rw [hfin]
          exact add_comm _ _
        have htail : (8 : ℕ) ∣ ∑ j ∈ Finset.range (a + 1 - 1), 2 ^ ((2 + j) * 2) := by
          apply Finset.dvd_sum
          intro j _
          have h8 : (8 : ℕ) = 2 ^ 3 := by decide
          rw [h8]
          exact Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨t, ht⟩ := htail
        omega
      have hn8 : (8 : ℕ) ∣ 2 ^ (a + 1) := by
        have h8 : (8 : ℕ) = 2 ^ 3 := by decide
        rw [h8]
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨k, hk⟩ := hn8
      have hn2 : (2 ^ (a + 1)) ^ 2 = 8 * (8 * (k ^ 2)) := by rw [hk]; ring
      have h3n : 3 * 2 ^ (a + 1) = 8 * (3 * k) := by rw [hk]; ring
      have hcontra : d ^ 2 % 8 = 5 := by omega
      exact sq_mod_eight_ne_five d hcontra
    · have ha01 : a = 0 ∨ a = 1 := by omega
      rcases ha01 with rfl | rfl
      · have h0 : (∑ j ∈ Finset.range (0 + 1 + 1), (2 : ℕ) ^ (j * 2)) = 5 := by decide
        have e1 : ((2 : ℕ) ^ (0 + 1)) ^ 2 = 4 := by decide
        have e2 : 3 * (2 : ℕ) ^ (0 + 1) = 6 := by decide
        rw [h0, e1, e2] at hsum
        omega
      · have h1 : (∑ j ∈ Finset.range (1 + 1 + 1), (2 : ℕ) ^ (j * 2)) = 21 := by decide
        have e1 : ((2 : ℕ) ^ (1 + 1)) ^ 2 = 16 := by decide
        have e2 : 3 * (2 : ℕ) ^ (1 + 1) = 12 := by decide
        rw [h1, e1, e2] at hsum
        omega
  · have hpo : Odd p := hp.odd_of_ne_two h2
    by_cases ha0 : a = 0
    · subst ha0
      have hn : (2 : ℕ) ^ 0 * p = p := by simp
      rw [hn] at hsum
      have hsig : (∑ e ∈ p.divisors, e ^ 2) = 1 + p ^ 2 := by
        have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
          simpa only [Finset.mem_singleton] using hp.ne_one.symm
        simp only [hp.divisors, Finset.sum_insert h1, Finset.sum_singleton, one_pow]
      rw [hsig] at hsum
      have hp2 : 2 ≤ p := hp.two_le
      omega
    · by_cases ha1 : a = 1
      · subst ha1
        have hcop : Nat.Coprime ((2 : ℕ) ^ 1) p :=
          Nat.Coprime.pow_left 1 (Nat.coprime_two_left.mpr hpo)
        have hsigp : ArithmeticFunction.sigma 2 p = 1 + p ^ 2 := by
          have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
            simpa only [Finset.mem_singleton] using hp.ne_one.symm
          simp only [ArithmeticFunction.sigma_apply, hp.divisors,
            Finset.sum_insert h1, Finset.sum_singleton, one_pow]
        have hsig : (∑ e ∈ ((2 : ℕ) ^ 1 * p).divisors, e ^ 2) = 5 * (1 + p ^ 2) := by
          rw [← ArithmeticFunction.sigma_apply,
            ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
            hsigp, ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two]
          have e1 : ∑ j ∈ Finset.range (1 + 1), (2 : ℕ) ^ (j * 2) = 5 := by decide
          rw [e1]
        rw [hsig] at hsum
        have hn2 : ((2 : ℕ) ^ 1 * p) ^ 2 = 4 * (p ^ 2) := by ring
        have h3n : 3 * ((2 : ℕ) ^ 1 * p) = 6 * p := by ring
        have hdeq : d ^ 2 + 6 * p = p ^ 2 + 5 := by omega
        have hp3 : 3 ≤ p := by
          have h2le := hp.two_le
          omega
        by_cases hp7 : 7 ≤ p
        · obtain ⟨q, rfl⟩ : ∃ q, p = q + 7 := ⟨p - 7, by omega⟩
          have hexpand : (q + 7) ^ 2 = q ^ 2 + 14 * q + 49 := by ring
          have hdeq' : d ^ 2 = q ^ 2 + 8 * q + 12 := by omega
          have hlow : (q + 3) ^ 2 < d ^ 2 := by
            have e : (q + 3) ^ 2 = q ^ 2 + 6 * q + 9 := by ring
            omega
          have hhigh : d ^ 2 < (q + 4) ^ 2 := by
            have e : (q + 4) ^ 2 = q ^ 2 + 8 * q + 16 := by ring
            omega
          have h1 : q + 3 < d := (Nat.pow_lt_pow_iff_left (n := 2) (by decide)).mp hlow
          have h2' : d < q + 4 := (Nat.pow_lt_pow_iff_left (n := 2) (by decide)).mp hhigh
          omega
        · have hp6 : p ≤ 6 := by omega
          interval_cases p
          · omega
          · exact absurd hp (by decide)
          · have h0 : d ^ 2 = 0 := by omega
            have hd0 : d = 0 := eq_zero_of_pow_eq_zero h0
            rw [hd0, zero_dvd_iff] at hdvd
            exact absurd hdvd (by decide)
          · exact absurd hp (by decide)
      · have ha2 : 2 ≤ a := by omega
        have h4n : (4 : ℕ) ∣ 2 ^ a * p := by
          have h4 : (4 : ℕ) = 2 ^ 2 := by decide
          rw [h4]
          exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 ha2) p
        have hcop : Nat.Coprime ((2 : ℕ) ^ a) p :=
          Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hpo)
        have hsigp : ArithmeticFunction.sigma 2 p = 1 + p ^ 2 := by
          have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
            simpa only [Finset.mem_singleton] using hp.ne_one.symm
          simp only [ArithmeticFunction.sigma_apply, hp.divisors,
            Finset.sum_insert h1, Finset.sum_singleton, one_pow]
        have hsig2 : ArithmeticFunction.sigma 2 ((2 : ℕ) ^ a)
            = ∑ j ∈ Finset.range (a + 1), 2 ^ (j * 2) :=
          ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two
        have hsig : (∑ e ∈ ((2 : ℕ) ^ a * p).divisors, e ^ 2)
            = (∑ j ∈ Finset.range (a + 1), 2 ^ (j * 2)) * (1 + p ^ 2) := by
          rw [← ArithmeticFunction.sigma_apply,
            ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
            hsig2, hsigp]
        have hS1 : (∑ j ∈ Finset.range (a + 1), (2 : ℕ) ^ (j * 2)) % 4 = 1 := by
          have hsplit : ∑ j ∈ Finset.range (a + 1), (2 : ℕ) ^ (j * 2)
              = (∑ j ∈ Finset.range a, 2 ^ ((j + 1) * 2)) + 1 := by
            rw [Finset.sum_range_succ']
            simp
          have htail4 : (4 : ℕ) ∣ ∑ j ∈ Finset.range a, 2 ^ ((j + 1) * 2) := by
            apply Finset.dvd_sum
            intro j _
            have h4 : (4 : ℕ) = 2 ^ 2 := by decide
            rw [h4]
            exact Nat.pow_dvd_pow 2 (by omega)
          obtain ⟨t, ht⟩ := htail4
          omega
        have hT2 : (1 + p ^ 2) % 4 = 2 := by
          obtain ⟨m, hm⟩ := hpo
          have hsq : p ^ 2 = 4 * (m ^ 2 + m) + 1 := by rw [hm]; ring
          omega
        have hsig4 : (∑ e ∈ ((2 : ℕ) ^ a * p).divisors, e ^ 2) % 4 = 2 := by
          rw [hsig, Nat.mul_mod, hS1, hT2]
        obtain ⟨k, hk⟩ := h4n
        have hn2 : ((2 : ℕ) ^ a * p) ^ 2 = 4 * (4 * (k ^ 2)) := by rw [hk]; ring
        have h3n : 3 * ((2 : ℕ) ^ a * p) = 4 * (3 * k) := by rw [hk]; ring
        have hcontra : d ^ 2 % 4 = 2 := by omega
        exact sq_mod_four_ne_two d hcontra

end MathlibExt.NumberTheory.FkPerfectWanted
