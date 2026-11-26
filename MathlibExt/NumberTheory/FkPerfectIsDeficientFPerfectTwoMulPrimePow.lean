/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.FkPerfect

/-! # The only deficient `F`-perfect number of the form `2 * p ^ a` is `6`

For odd `p`, the divisor sum of `2 * p ^ a` factors as `(1 + 2 ^ 2)` times a
geometric sum; a size comparison then leaves only `2 * 3 = 6` and `2 * 5 = 10`,
and `10` is ruled out by direct computation. Powers of two, including `2`
itself, are ruled out by the prime-power classification
`isKLDeficientPerfect_prime_pow_two_iff`. This module proves that `6` is
deficient `F`-perfect with divisor `2` and is the only such number of the form
`2 * p ^ a`; deficient `F`-perfect numbers are defined in
`MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime`.

Full reference: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P.
Saikia, "On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers",
*INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 12.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem not_isDeficientFPerfect_ten : ¬ IsDeficientFPerfect 10 := by
  rintro ⟨d, hd, _hlt, hsum⟩
  have hs : (∑ e ∈ (10).divisors, e ^ 2) = 130 := by decide
  rw [hs, show (10 : ℕ) ^ 2 = 100 from by decide,
    show (3 : ℕ) * 10 = 30 from by decide] at hsum
  have hd0 : d ^ 2 = 0 := by omega
  have hdz : d = 0 := sq_eq_zero_iff.mp hd0
  rw [hdz, zero_dvd_iff] at hd
  exact absurd hd (by decide)

private theorem deficientFPerfect_two_mul_odd_imp (p a : ℕ) (hp : p.Prime)
    (hpo : Odd p) (ha : 1 ≤ a) :
    IsDeficientFPerfect (2 * p ^ a) → 2 * p ^ a = 6 := by
  intro h
  have hcopy := h
  obtain ⟨d, _hd, _hlt, hsum⟩ := h
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpo
  have htwo : ArithmeticFunction.sigma 2 2 = 1 + 2 ^ 2 := by
    rw [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
    decide
  have hsigma : (∑ e ∈ (2 * p ^ a).divisors, e ^ 2)
      = (1 + 2 ^ 2) * ∑ i ∈ Finset.range (a + 1), p ^ (i * 2) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right a),
      htwo, ArithmeticFunction.sigma_apply_prime_pow hp]
  rw [hsigma] at hsum
  have hmem : a ∈ Finset.range (a + 1) := Finset.mem_range.mpr (Nat.lt_succ_self a)
  have hS2 : (p ^ a) ^ 2 ≤ ∑ i ∈ Finset.range (a + 1), p ^ (i * 2) := by
    have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (p ^ (i * 2))) hmem
    rw [(pow_mul p a 2).symm]
    exact hle
  by_cases h6 : 6 < p ^ a
  · have hpos : 0 < p ^ a := pow_pos hp.pos a
    have hsq : 6 * p ^ a < (p ^ a) ^ 2 := by
      rw [pow_two]
      exact mul_lt_mul_of_pos_right h6 hpos
    rw [show (1 : ℕ) + 2 ^ 2 = 5 from by decide,
      show (2 * p ^ a) ^ 2 = 4 * (p ^ a) ^ 2 from by ring,
      show 3 * (2 * p ^ a) = 6 * p ^ a from by ring] at hsum
    have hF : False := by omega
    exact hF.elim
  · have h6le : p ^ a ≤ 6 := by omega
    have ha1 : a = 1 := by
      by_contra ha1
      have ha2 : 2 ≤ a := by omega
      obtain ⟨m, hm⟩ := hpo
      have hp3 : 3 ≤ p := by
        have h2 := hp.two_le
        omega
      have h1 : (3 : ℕ) ^ a ≤ p ^ a := Nat.pow_le_pow_left hp3 a
      have h2 : (3 : ℕ) ^ 2 ≤ 3 ^ a :=
        pow_le_pow_right₀ (a := 3) (show (1 : ℕ) ≤ 3 by decide) ha2
      have h9 : (3 : ℕ) ^ 2 = 9 := by decide
      omega
    subst ha1
    rw [pow_one] at h6le
    have h2 := hp.two_le
    interval_cases p
    · obtain ⟨m, hm⟩ := hpo
      have hF : False := by omega
      exact hF.elim
    · decide
    · exact absurd hp (by decide)
    · have h10 : (2 : ℕ) * 5 ^ 1 = 10 := by decide
      rw [h10] at hcopy ⊢
      exact absurd hcopy not_isDeficientFPerfect_ten
    · exact absurd hp (by decide)

/-- **The only deficient $F$-perfect number of the form $2p^a$ is $6$.** The number $6$ is deficient
$F$-perfect, and for every prime $p$ and every natural number $a$, if $2p^a$ is deficient
$F$-perfect then $2p^a = 6$.

The divisor for $6$ is $d = 2$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 12. -/
theorem isDeficientFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect 6 ∧
      (IsDeficientFPerfect (2 * p ^ a) → 2 * p ^ a = 6) := by
  constructor
  · refine ⟨2, by decide, by decide, ?_⟩
    have hs : (∑ e ∈ (6).divisors, e ^ 2) = 50 := by decide
    rw [hs]
    decide
  · intro h
    rcases hp.eq_two_or_odd' with rfl | hpo
    · have e : (2 : ℕ) * 2 ^ a = 2 ^ (a + 1) := (pow_succ' 2 a).symm
      rw [e] at h
      exact absurd ((isKLDeficientPerfect_prime_pow_two_iff 2 (a + 1) 3 Nat.prime_two).mp h).2.2
        (by decide)
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · have h2 : (2 : ℕ) * p ^ 0 = 2 ^ 1 := by simp
        rw [h2] at h
        exact absurd ((isKLDeficientPerfect_prime_pow_two_iff 2 1 3 Nat.prime_two).mp h).2.2
          (by decide)
      · exact deficientFPerfect_two_mul_odd_imp p a hp hpo ha h

end MathlibExt.NumberTheory.FkPerfectWanted
