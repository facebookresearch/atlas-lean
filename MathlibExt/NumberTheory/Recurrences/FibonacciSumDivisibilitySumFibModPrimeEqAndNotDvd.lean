/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Sum of the first `p` Fibonacci numbers modulo a prime `p`

This module proves `sum_fib_mod_prime_eq_and_not_dvd`: for a prime `p > 5`, the sum
`F_1 + ⋯ + F_p` of the first `p` Fibonacci numbers satisfies `S % p = 1` when
`p % 5 = 1 ∨ p % 5 = 4`, `S % p = p - 2` when `p % 5 = 2 ∨ p % 5 = 3`, and `¬ p ∣ S`
in all cases. The proof computes with the Fibonacci matrix over `ZMod p` and evaluates
`5 ^ (p / 2)` by Euler's criterion and quadratic reciprocity.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci Numbers",
*INTEGERS* 25 (2025), Article A87 (<https://math.colgate.edu/~integers/z87/z87.pdf>),
Theorem 1.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem fibMat_pow (p n : ℕ) :
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (n + 1) =
    !![((Nat.fib (n + 2) : ℕ) : ZMod p), ((Nat.fib (n + 1) : ℕ) : ZMod p);
       ((Nat.fib (n + 1) : ℕ) : ZMod p), ((Nat.fib n : ℕ) : ZMod p)] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_one, Nat.fib_two, Nat.fib_one, Nat.fib_zero]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two] <;> ring

private theorem two_ne_zero_zmod (p : ℕ) (hp5 : 5 < p) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hz
    omega
  simpa using h

private theorem fib_key (p : ℕ) (hp : p.Prime) (hp5 : 5 < p) :
    ((Nat.fib p : ℕ) : ZMod p) = (5 : ZMod p) ^ (p / 2) ∧
    2 * ((Nat.fib (p + 1) : ℕ) : ZMod p) = (5 : ZMod p) ^ (p / 2) + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hppos : 0 < p := hp.pos
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp5
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := !![1, 1; 1, 0] with hM
  set D : Matrix (Fin 2) (Fin 2) (ZMod p) := (2 : ZMod p) • M - 1 with hD
  have hDsq : D ^ 2 = (5 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hDpow : D ^ p = (5 : ZMod p) ^ (p / 2) • D := by
    have h1 : D ^ p = D ^ (2 * (p / 2) + 1) := by
      congr 1
      obtain ⟨k, hk⟩ := hpodd
      omega
    rw [h1, pow_add, pow_one, pow_mul, hDsq, smul_pow, one_pow, smul_mul_assoc, one_mul]
  have hFrob : D ^ p = (2 : ZMod p) • M ^ p - 1 := by
    have hcomm : Commute ((2 : ZMod p) • M) (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) :=
      (Commute.one_right _).neg_right
    have h := add_pow_char_of_commute p hcomm
    have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
    have hD' : ((2 : ZMod p) • M + (-1) : Matrix (Fin 2) (Fin 2) (ZMod p)) = D := by
      rw [hD, sub_eq_add_neg]
    rw [hD', smul_pow, h2p, Odd.neg_pow hpodd, one_pow] at h
    rw [sub_eq_add_neg]
    exact h
  have hmain : (2 : ZMod p) • M ^ p - 1 = (5 : ZMod p) ^ (p / 2) • D := by
    rw [← hFrob, hDpow]
  have hMp : M ^ p = !![((Nat.fib (p + 1) : ℕ) : ZMod p), ((Nat.fib p : ℕ) : ZMod p);
      ((Nat.fib p : ℕ) : ZMod p), ((Nat.fib (p - 1) : ℕ) : ZMod p)] := by
    have e : M ^ p = M ^ (p - 1 + 1) := by
      congr 1
      omega
    have hMpow := fibMat_pow p (p - 1)
    rw [← hM] at hMpow
    rw [e, hMpow]
    have e1 : p - 1 + 2 = p + 1 := by omega
    have e2 : p - 1 + 1 = p := by omega
    rw [e1, e2]
  have h01 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (ZMod p) => X 0 1) hmain
  have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (ZMod p) => X 0 0) hmain
  rw [hMp] at h01 h00
  simp [hD, hM] at h01 h00
  refine ⟨?_, ?_⟩
  · apply mul_left_cancel₀ h2ne
    linear_combination h01
  · linear_combination h00

private theorem sum_fib_eq (p : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, Nat.fib i = Nat.fib (p + 2) - 1 := by
  have h1 := Nat.fib_succ_eq_succ_sum (p + 1)
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < p + 1), Nat.fib_zero, zero_add,
    Finset.Ico_add_one_right_eq_Icc] at h1
  have e : p + 1 + 1 = p + 2 := by omega
  rw [e] at h1
  omega

private theorem legendre5_flip (p : ℕ) [Fact p.Prime] (hp5 : 5 < p) :
    legendreSym p ((5 : ℕ) : ℤ) = legendreSym 5 ((p : ℕ) : ℤ) := by
  exact legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) rfl (by omega)

private theorem euler5 (p : ℕ) [Fact p.Prime] :
    (((legendreSym p ((5 : ℕ) : ℤ)) : ℤ) : ZMod p) = (5 : ZMod p) ^ (p / 2) := by
  have h := legendreSym.eq_pow p ((5 : ℕ) : ℤ)
  simpa [Int.cast_natCast] using h

private theorem pow5_eq_one (p : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (hcase : p % 5 = 1 ∨ p % 5 = 4) : (5 : ZMod p) ^ (p / 2) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hflip := legendre5_flip p hp5
  have heuler := euler5 p
  have hne : ((p : ℕ) : ZMod 5) ≠ 0 := by
    intro hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hdvd : 5 ∣ p := hz
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hdvd
    omega
  have hcast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff p (p % 5) 5).mpr (Nat.mod_modEq p 5).symm
  have hsq : IsSquare ((p : ℕ) : ZMod 5) := by
    rcases hcase with h1 | h4
    · rw [hcast, h1, Nat.cast_one]
      exact ⟨1, by simp⟩
    · rw [hcast, h4]
      exact ⟨(2 : ZMod 5), by decide⟩
  have hval : legendreSym 5 ((p : ℕ) : ℤ) = 1 := (legendreSym.eq_one_iff' 5 hne).mpr hsq
  rw [hflip, hval] at heuler
  simpa using heuler.symm

private theorem pow5_eq_neg_one (p : ℕ) (hp : p.Prime) (hp5 : 5 < p)
    (hcase : p % 5 = 2 ∨ p % 5 = 3) : (5 : ZMod p) ^ (p / 2) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hflip := legendre5_flip p hp5
  have heuler := euler5 p
  have hcast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) :=
    (ZMod.natCast_eq_natCast_iff p (p % 5) 5).mpr (Nat.mod_modEq p 5).symm
  have hnsq : ¬ IsSquare ((p : ℕ) : ZMod 5) := by
    rcases hcase with h2 | h3
    · rw [hcast, h2]
      intro hsq
      obtain ⟨r, hr⟩ := hsq
      fin_cases r <;> revert hr <;> decide
    · rw [hcast, h3]
      intro hsq
      obtain ⟨r, hr⟩ := hsq
      fin_cases r <;> revert hr <;> decide
  have hval : legendreSym 5 ((p : ℕ) : ℤ) = -1 :=
    (legendreSym.eq_neg_one_iff' 5).mpr hnsq
  rw [hflip, hval] at heuler
  simpa using heuler.symm

/-- **Sum of the first $p$ Fibonacci numbers modulo a prime $p$.** Let $p > 5$ be a prime, let
$F_i$ denote the $i$-th Fibonacci number, with $F_1 = F_2 = 1$, and let
$S = F_1 + F_2 + \dots + F_p$. If $p \equiv 1$ or $4 \pmod 5$, then $S$ leaves remainder $1$ on
division by $p$; if $p \equiv 2$ or $3 \pmod 5$, then $S$ leaves remainder $p - 2$ on division
by $p$; and in every case $p$ does not divide $S$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 1. -/
public theorem sum_fib_mod_prime_eq_and_not_dvd
    (p : ℕ) (hp : p.Prime) (hp5 : 5 < p) :
    ((p % 5 = 1 ∨ p % 5 = 4) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 1) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = p - 2) ∧
      ¬p ∣ (∑ i ∈ Finset.Icc 1 p, Nat.fib i)
    := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum : ∑ i ∈ Finset.Icc 1 p, Nat.fib i = Nat.fib (p + 2) - 1 := sum_fib_eq p
  have hkey := fib_key p hp hp5
  have hfib1 : 1 ≤ Nat.fib (p + 2) := by
    have hpos : 0 < Nat.fib (p + 2) := Nat.fib_pos.mpr (by omega)
    omega
  have hadd : ((Nat.fib (p + 2) : ℕ) : ZMod p) =
      ((Nat.fib p : ℕ) : ZMod p) + ((Nat.fib (p + 1) : ℕ) : ZMod p) := by
    rw [Nat.fib_add_two, Nat.cast_add]
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hp5
  have h1 : (p % 5 = 1 ∨ p % 5 = 4) → (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 1 := by
    intro hcase
    have he : (5 : ZMod p) ^ (p / 2) = 1 := pow5_eq_one p hp hp5 hcase
    have hF : ((Nat.fib (p + 2) : ℕ) : ZMod p) = 2 := by
      apply mul_left_cancel₀ h2ne
      rw [hadd]
      linear_combination 2 * hkey.1 + hkey.2 + 3 * he
    have hS1 : ((∑ i ∈ Finset.Icc 1 p, Nat.fib i : ℕ) : ZMod p) = 1 := by
      rw [hsum, Nat.cast_sub hfib1, hF]
      ring
    have hmod : (∑ i ∈ Finset.Icc 1 p, Nat.fib i) ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using hS1)
    calc (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 1 % p := hmod
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (p % 5 = 2 ∨ p % 5 = 3) → (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = p - 2 := by
    intro hcase
    have he : (5 : ZMod p) ^ (p / 2) = -1 := pow5_eq_neg_one p hp hp5 hcase
    have hF : ((Nat.fib (p + 2) : ℕ) : ZMod p) = -1 := by
      apply mul_left_cancel₀ h2ne
      rw [hadd]
      linear_combination 2 * hkey.1 + hkey.2 + 3 * he
    have hS2 : ((∑ i ∈ Finset.Icc 1 p, Nat.fib i : ℕ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) := by
      rw [hsum, Nat.cast_sub hfib1, hF, Nat.cast_sub (show 2 ≤ p by omega),
        ZMod.natCast_self]
      ring
    have hmod : (∑ i ∈ Finset.Icc 1 p, Nat.fib i) ≡ (p - 2) [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hS2
    calc (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = (p - 2) % p := hmod
      _ = p - 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : ¬ p ∣ (∑ i ∈ Finset.Icc 1 p, Nat.fib i) := by
    intro hdvd
    have hmod0 : (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    have h5p : ¬ 5 ∣ p := by
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hd
      omega
    have h5ne : p % 5 ≠ 0 := fun h0 => h5p (Nat.dvd_of_mod_eq_zero h0)
    have hlt : p % 5 < 5 := by omega
    by_cases hc : p % 5 = 1 ∨ p % 5 = 4
    · rw [h1 hc] at hmod0
      exact one_ne_zero hmod0
    · have hc2 : p % 5 = 2 ∨ p % 5 = 3 := by omega
      rw [h2 hc2] at hmod0
      omega
  exact ⟨h1, h2, h3⟩

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
