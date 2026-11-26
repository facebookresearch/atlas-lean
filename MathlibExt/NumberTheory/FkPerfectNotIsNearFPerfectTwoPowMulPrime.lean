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
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SquareModEight

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
    have h := not_isNearFPerfect_two_pow_mul_prime_pow 2 (a + 1) 0 Nat.prime_two ⟨0, rfl⟩
    have hn : (2 : ℕ) ^ (a + 1) * 2 ^ 0 = 2 ^ a * 2 := by ring
    rw [hn] at h
    exact h ⟨d, hdvd, hlt, hsum⟩
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
        have hn : (2 : ℕ) ^ 1 * p = 2 * p ^ 1 := by ring
        rw [hn] at hdvd hlt hsum
        obtain ⟨h5, -⟩ := klNearPerfectWith_two_mul_prime_pow_imp p 1 2 3 d hp hpo
          (by decide) (by decide) ⟨hdvd, hlt, hsum⟩
        have hle : p ^ 2 ≤ 5 := Nat.le_of_dvd (by decide) h5
        have hp3 : 3 ≤ p := by
          have h2le := hp.two_le
          omega
        have h9 : 9 ≤ p ^ 2 := by simpa using Nat.pow_le_pow_left hp3 2
        omega
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
        have hr := Nat.sq_mod_eight d
        omega

end MathlibExt.NumberTheory.FkPerfectWanted
