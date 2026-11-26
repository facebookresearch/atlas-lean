/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.FkPerfect
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # No near `F`-perfect number of the form `2 * p ^ a`

For an odd prime `p`, the divisibility `p ^ 2 ∣ 1 + 2 ^ 2` supplied by
`klNearPerfectWith_two_mul_prime_pow_imp` is impossible since `p ^ 2 ≥ 9 > 5`.
For `p = 2`, the number `2 * 2 ^ a = 2 ^ (a + 1)` is a power of two; the
near-`F`-perfect equation then fails modulo `8` once the exponent reaches `3`,
while `2` and `4` are checked directly. The main result is
`not_isNearFPerfect_two_mul_prime_pow`.
Near `F`-perfect numbers are defined in `MathlibExt.NumberTheory.FkPerfect`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 13.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sum_range_two_pow_modEq (c : ℕ) (hc : 2 ≤ c) :
    (∑ i ∈ Finset.range (c + 1), 2 ^ (i * 2)) ≡ 5 [MOD 8] := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hc
  clear hc
  induction t with
  | zero => decide
  | succ t ih =>
    have hstep : 2 + (t + 1) + 1 = (2 + t + 1) + 1 := by omega
    rw [hstep, Finset.sum_range_succ]
    have h0 : (2 : ℕ) ^ ((2 + t + 1) * 2) ≡ 0 [MOD 8] :=
      Nat.modEq_zero_iff_dvd.mpr (by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ∣ 2 ^ ((2 + t + 1) * 2) := Nat.pow_dvd_pow 2 (by omega))
    simpa using ih.add h0

private theorem sq_mod_eight_ne_five (d : ℕ) : ¬ d ^ 2 ≡ 5 [MOD 8] := by
  intro hcon
  have hmod : d ^ 2 % 8 = 5 % 8 := hcon
  rw [Nat.pow_mod] at hmod
  have hall : ∀ m : Fin 8, (m : ℕ) ^ 2 % 8 ≠ 5 % 8 := by decide
  exact hall ⟨d % 8, by omega⟩ hmod

private theorem not_isNearFPerfect_two_pow_one : ¬ IsNearFPerfect (2 ^ 1) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  have e1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [e1] at hdvd hlt hsum
  have hd1 : d = 1 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_right (Nat.ne_of_lt hlt)
  subst hd1
  have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  simp only [Nat.prime_two.divisors, Finset.sum_insert h1, Finset.sum_singleton] at hsum
  norm_num at hsum

private theorem not_isNearFPerfect_two_pow_two : ¬ IsNearFPerfect (2 ^ 2) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [e2] at hdvd hlt hsum
  have hdiv4 : (4 : ℕ).divisors = {1, 2, 4} := by decide
  have hdmem := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [hdiv4] at hdmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
  have hsum4 : (∑ e ∈ (4 : ℕ).divisors, e ^ 2) = 21 := by decide
  rw [hsum4] at hsum
  rcases hdmem with rfl | rfl | rfl
  · norm_num at hsum
  · norm_num at hsum
  · omega

private theorem not_isNearFPerfect_two_pow (c : ℕ) (hc : 1 ≤ c) :
    ¬ IsNearFPerfect (2 ^ c) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases hc1 : c = 1
  · subst hc1
    exact not_isNearFPerfect_two_pow_one ⟨d, hdvd, hlt, hsum⟩
  · by_cases hc2 : c = 2
    · subst hc2
      exact not_isNearFPerfect_two_pow_two ⟨d, hdvd, hlt, hsum⟩
    · have hc3 : 3 ≤ c := by omega
      have hsigma : (∑ e ∈ (2 ^ c).divisors, e ^ 2) =
          ∑ i ∈ Finset.range (c + 1), 2 ^ (i * 2) := by
        rw [← ArithmeticFunction.sigma_apply,
          ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two]
      have hleft : (∑ e ∈ (2 ^ c).divisors, e ^ 2) ≡ 5 [MOD 8] := by
        rw [hsigma]
        exact sum_range_two_pow_modEq c (by omega)
      have h2c : (2 : ℕ) ^ c ≡ 0 [MOD 8] :=
        Nat.modEq_zero_iff_dvd.mpr (by
          calc (8 : ℕ) = 2 ^ 3 := by norm_num
            _ ∣ 2 ^ c := Nat.pow_dvd_pow 2 hc3)
      have hterm1 : ((2 ^ c : ℕ) ^ 2) ≡ 0 [MOD 8] := by
        simpa using h2c.pow 2
      have hterm3 : (3 * 2 ^ c : ℕ) ≡ 0 [MOD 8] := by
        simpa using (Nat.ModEq.refl 3).mul h2c
      have hrhs : ((2 ^ c : ℕ) ^ 2 + d ^ 2 + 3 * 2 ^ c) ≡ d ^ 2 [MOD 8] := by
        simpa using (hterm1.add (Nat.ModEq.refl (d ^ 2))).add hterm3
      rw [hsum] at hleft
      exact sq_mod_eight_ne_five d (hrhs.symm.trans hleft)

/-- **No near $F$-perfect number of the form $2p^a$.** For every prime $p$ and every natural
number $a$, the number $n = 2p^a$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 13. -/
theorem not_isNearFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 * p ^ a) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases h2 : p = 2
  · subst h2
    rw [show (2 : ℕ) * 2 ^ a = 2 ^ (a + 1) by ring] at hdvd hlt hsum
    exact not_isNearFPerfect_two_pow (a + 1) (by omega) ⟨d, hdvd, hlt, hsum⟩
  · have hpo : Odd p := hp.odd_of_ne_two h2
    obtain ⟨hdvd5, -⟩ := klNearPerfectWith_two_mul_prime_pow_imp p a 2 3 d hp hpo
      (by norm_num) (by norm_num) ⟨hdvd, hlt, hsum⟩
    norm_num at hdvd5
    have hle := Nat.le_of_dvd (by norm_num) hdvd5
    have hp3 : 3 ≤ p := by
      have h2le := hp.two_le
      omega
    have h9 : 9 ≤ p ^ 2 := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    omega

end MathlibExt.NumberTheory.FkPerfectWanted
