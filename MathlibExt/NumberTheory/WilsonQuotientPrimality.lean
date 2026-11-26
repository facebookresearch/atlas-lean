/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A primality criterion from the Wilson quotient sum

An alternating factorial sum telescopes to evaluate `Z(2n - 1)`. Splitting its factorial at
`n` gives an integer witness whose residue distinguishes prime from composite `n`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.WilsonQuotientsWanted

/-- **Morozov's Wilson quotients.** For natural numbers $k$ and $n$, $M_k(n)$ is the rational
number

$$M_k(n) = \frac{1 + (-1)^k \, k! \, (n - k - 1)!}{n},$$

where $n - k - 1$ is truncated subtraction of natural numbers and division by $0$ gives $0$. -/
def wilsonQuotientM (k n : ℕ) : ℚ :=
  (1 + (-1 : ℚ) ^ k * (Nat.factorial k * Nat.factorial (n - k - 1) : ℚ)) / n

/-- **Morozov's Wilson quotient sum.** For a natural number $n$, $Z(n)$ is the rational number
$Z(n) = \sum_{k=0}^{n-1} M_k(n)$, where $M_k(n)$ are Morozov's Wilson quotients. -/
def wilsonQuotientZ (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, wilsonQuotientM k n

private theorem wilsonQuotientZ_two_mul_sub_one (n : ℕ) (hn : 1 ≤ n) :
    wilsonQuotientZ (2 * n - 1) = 1 + (Nat.factorial (2 * n - 2) : ℚ) / n := by
  let m := 2 * n - 1
  let f (k : ℕ) : ℚ := (-1 : ℚ) ^ k * (k.factorial : ℚ) * ((m - k).factorial : ℚ)
  let g (k : ℕ) : ℚ := (-1 : ℚ) ^ k * (k.factorial * (m - k - 1).factorial : ℚ)
  have hm : 0 < m := by dsimp [m]; omega
  have step (k : ℕ) (hk : k ∈ Finset.range m) :
      ((m : ℚ) + 1) * g k = f k - f (k + 1) := by
    have hkm := Finset.mem_range.mp hk
    have hsub : m - k = (m - k - 1) + 1 := by omega
    have hadd : m - k - 1 + k + 1 = m := by omega
    have haddR : ((m - k - 1 : ℕ) : ℚ) + (k : ℚ) + 1 = m := by exact_mod_cast hadd
    dsimp only [f, g]
    rw [show m - (k + 1) = m - k - 1 by omega, hsub, Nat.factorial_succ, pow_succ,
      Nat.factorial_succ]
    push_cast
    rw [← haddR]
    ring
  have htelescope : ((m : ℚ) + 1) * (∑ k ∈ Finset.range m, g k) = f 0 - f m := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ k ∈ Finset.range m, (f k - f (k + 1)) := Finset.sum_congr rfl step
      _ = -(∑ k ∈ Finset.range m, (f (k + 1) - f k)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun k _ => (neg_sub (f (k + 1)) (f k)).symm)
      _ = _ := by rw [Finset.sum_range_sub, neg_sub]
  have hm' : m + 1 = 2 * n := by dsimp [m]; omega
  have hodd : Odd m := ⟨n - 1, by dsimp [m]; omega⟩
  have hsign : (-1 : ℚ) ^ m = -1 := hodd.neg_one_pow
  have hmR : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpred : m - 1 = 2 * n - 2 := by dsimp [m]; omega
  have hfac : (m.factorial : ℚ) = (m : ℚ) * ((m - 1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred hm.ne').symm
  have hsum : ((m : ℚ) + 1) * (∑ k ∈ Finset.range m, g k) =
      2 * (m : ℚ) * ((m - 1).factorial : ℚ) := by
    rw [htelescope]
    simp [f, hsign, hfac, two_mul, add_mul]
  have hmn : (m : ℚ) + 1 = 2 * (n : ℚ) := by exact_mod_cast hm'
  change (∑ k ∈ Finset.range m, (1 + g k) / (m : ℚ)) = _
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hpred, hmn] at hsum
  field_simp
  linarith

private theorem factorial_add_eq_mul_shifted_prod (n k : ℕ) (hn : 0 < n) :
    (n + k).factorial = n * (n - 1).factorial * ∏ i ∈ Finset.range k, (n + (i + 1)) := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.factorial_succ, Nat.sub_add_cancel hn]
  | succ k ih =>
    rw [← Nat.add_assoc, Nat.factorial_succ, ih, Finset.prod_range_succ, Nat.add_assoc]
    ac_rfl

/-- **A primality criterion from the Wilson quotient sum Z(2n − 1).** For every natural number
$n \ge 1$, Morozov's Wilson quotient sum $Z(2n - 1)$ is an integer, and it is divisible by $n$
if and only if $n = 1$ or $n$ is prime.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 4. -/
theorem exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ (2 * n - 1) ∧
      ((z ≡ 0 [ZMOD (n : ℤ)]) ↔ n = 1 ∨ n.Prime) := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · refine ⟨2, ?_, iff_of_true Int.modEq_one (Or.inl rfl)⟩
    norm_num [wilsonQuotientZ, wilsonQuotientM, Finset.sum_range_succ]
  let q := ∏ i ∈ Finset.range (n - 2), (n + (i + 1))
  refine ⟨1 + ((n - 1).factorial : ℤ) * (q : ℤ), ?_, ?_⟩
  · rw [wilsonQuotientZ_two_mul_sub_one n hn.le,
      show 2 * n - 2 = n + (n - 2) by omega,
      factorial_add_eq_mul_shifted_prod n (n - 2) (by omega)]
    change _ = 1 + ((n * (n - 1).factorial * q : ℕ) : ℚ) / n
    push_cast
    have hnR : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · rw [or_iff_right hn.ne']
    constructor
    · intro hz
      by_contra hnp
      -- A proper prime divisor already divides `(n - 1)!`.
      let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn.ne'
      have hpn : p < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
      have hpz := hz.of_dvd (show (p : ℤ) ∣ (n : ℤ) by exact_mod_cast Nat.minFac_dvd n)
      have hfac : ((n - 1).factorial : ZMod p) = 0 := by
        obtain ⟨a, ha⟩ := Nat.dvd_factorial hp.pos (show p ≤ n - 1 by omega)
        simp [ha, Nat.cast_mul]
      have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
      have hpz' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr hpz
      push_cast at hpz'
      exact (one_ne_zero : (1 : ZMod p) ≠ 0) (by simpa only [hfac, zero_mul, add_zero] using hpz')
    · intro hp
      have hfac : ((n - 1).factorial : ZMod n) = -1 :=
        (Nat.prime_iff_fac_equiv_neg_one hn.ne').mp hp
      have hnlast : ((n - 1 : ℕ) : ZMod n) = -1 := by
        apply eq_neg_of_add_eq_zero_left
        calc
          _ = ((n - 1 + 1 : ℕ) : ZMod n) := by simp only [Nat.cast_add, Nat.cast_one]
          _ = 0 := by rw [Nat.sub_add_cancel hn.le, ZMod.natCast_self]
      have hprev : ((n - 2).factorial : ZMod n) = 1 := by
        have h := hfac
        conv_lhs at h =>
          rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
            show n - 2 + 1 = n - 1 by omega, hnlast]
        simpa using h
      have hq : (q : ZMod n) = ((n - 2).factorial : ZMod n) := by
        dsimp only [q]
        rw [Nat.factorial_eq_prod_range_add_one]
        simp only [Nat.cast_prod, Nat.cast_add, ZMod.natCast_self, zero_add]
      apply (ZMod.intCast_eq_intCast_iff _ _ n).mp
      push_cast
      simp [hfac, hq, hprev]

private theorem wilsonQuotientZ_of_even (n : ℕ) (hn : 1 ≤ n) (heven : Even n) :
    wilsonQuotientZ n = 1 := by
  let f (k : ℕ) : ℚ := (-1) ^ k * ((k.factorial : ℚ) * ((n - 1 - k).factorial : ℚ))
  have hodd : Odd (n - 1) := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j - 1, by omega⟩
  -- Reflect the range: the factorials swap and the sign changes.
  have hflip (k : ℕ) (hk : k ∈ Finset.range n) : f (n - 1 - k) = -f k := by
    have hk' := Finset.mem_range.mp hk
    have hsub : n - 1 - (n - 1 - k) = k := by omega
    have hadd : n - 1 - k + k = n - 1 := by omega
    have hkk : Even (k + k) := ⟨k, rfl⟩
    have hsign : (-1 : ℚ) ^ (n - 1 - k) = -((-1 : ℚ) ^ k) := by
      calc
        _ = (-1 : ℚ) ^ (n - 1 - k) * (-1) ^ (k + k) := by rw [hkk.neg_one_pow, mul_one]
        _ = (-1 : ℚ) ^ (n - 1) * (-1) ^ k := by rw [pow_add _ k k, ← mul_assoc, ← pow_add, hadd]
        _ = _ := by rw [hodd.neg_one_pow, neg_one_mul]
    simp only [f, hsub, hsign, neg_mul]
    rw [mul_comm ((n - 1 - k).factorial : ℚ) (k.factorial : ℚ)]
  have hsum : (∑ k ∈ Finset.range n, f k) = 0 := by
    have h := calc
      (∑ k ∈ Finset.range n, f k) = ∑ k ∈ Finset.range n, f (n - 1 - k) :=
        (Finset.sum_range_reflect f n).symm
      _ = ∑ k ∈ Finset.range n, -f k := Finset.sum_congr rfl hflip
      _ = -(∑ k ∈ Finset.range n, f k) := Finset.sum_neg_distrib f
    linarith only [h]
  have hnR : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [wilsonQuotientZ, wilsonQuotientM, Nat.sub_right_comm n _ 1]
  change (∑ k ∈ Finset.range n, (1 + f k) / (n : ℚ)) = 1
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, hsum, add_zero]
  exact mul_inv_cancel₀ hnR

/-- **The Wilson quotient sum is an integer.** For every natural number $n \ge 1$, Morozov's
Wilson quotient sum $Z(n)$ is an integer.

Source: Ivan V. Morozov, "On Quotients of a More General
Theorem of Wilson", Theorem 1. -/
theorem exists_int_eq_wilsonQuotientZ
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℚ) = wilsonQuotientZ n := by
  rcases Nat.even_or_odd n with heven | ⟨k, hk⟩
  · exact ⟨1, by simpa using (wilsonQuotientZ_of_even n hn heven).symm⟩
  · obtain ⟨z, hz, _⟩ :=
      exists_int_eq_wilsonQuotientZ_two_mul_sub_one_modEq_zero_iff (k + 1) (by omega)
    exact ⟨z, by simpa only [show 2 * (k + 1) - 1 = n by omega] using hz⟩

end MathlibExt.NumberTheory.WilsonQuotientsWanted
