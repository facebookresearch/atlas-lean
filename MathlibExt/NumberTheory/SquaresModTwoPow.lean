/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Squares modulo consecutive powers of two

We classify the residues that cease to be squares when the exponent of two increases
by one, for both odd and even starting exponents.
-/

namespace MetaMathlibExt

namespace SquaresModTwoPow

private theorem isSquare_iff {x m : ℕ} :
    IsSquare (x : ZMod m) ↔ ∃ r t : ℤ, (x : ℤ) = r ^ 2 + m * t := by
  rw [isSquare_iff_exists_sq, ZMod.exists]
  refine exists_congr fun r ↦ ?_
  rw [eq_comm, ← Int.cast_pow, ← Int.cast_natCast x, ZMod.intCast_eq_intCast_iff,
    Int.modEq_iff_add_fac]

/-- Cancelling a factor of four in a square congruence halves the root. -/
private theorem isSquare_four_mul_iff (x m : ℕ) :
    IsSquare ((4 * x : ℕ) : ZMod (4 * m)) ↔ IsSquare (x : ZMod m) := by
  rw [isSquare_iff, isSquare_iff]
  push_cast
  constructor
  · rintro ⟨r, t, h⟩
    rw [mul_assoc] at h
    have hr := Int.sq_emod_four r
    obtain ⟨s, rfl⟩ : (2 : ℤ) ∣ r := by omega
    refine ⟨s, t, ?_⟩
    rw [mul_pow] at h
    omega
  · rintro ⟨r, t, h⟩
    exact ⟨2 * r, t, by rw [h]; ring⟩

/-- An odd root modulo a multiple of eight lifts when the modulus doubles. -/
private theorem four_dvd_of_not_isSquare {x m : ℕ} (hs : IsSquare (x : ZMod (8 * m)))
    (hn : ¬IsSquare (x : ZMod (16 * m))) : 4 ∣ x := by
  obtain ⟨r, t, ht⟩ := isSquare_iff.mp hs
  push_cast at ht
  obtain ⟨s, hr | hr⟩ := Int.even_or_odd' r
  · exact_mod_cast (show (4 : ℤ) ∣ (x : ℤ) from
      ⟨s ^ 2 + 2 * m * t, by rw [ht, hr]; ring⟩)
  · exfalso
    apply hn
    refine isSquare_iff.mpr ⟨r + 4 * m * t, -(s * t + m * t ^ 2), ?_⟩
    rw [ht, hr]
    push_cast
    ring

private theorem exceptional_residue (k x : ℕ) (hx : x < 8 * 4 ^ k) :
    (IsSquare (x : ZMod (4 * 4 ^ k)) ∧ ¬IsSquare (x : ZMod (8 * 4 ^ k))) ↔
      x = 5 * 4 ^ k := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, mul_one] at hx ⊢
    interval_cases x <;> unfold IsSquare <;> decide
  | succ k ih =>
    rw [pow_succ' 4 k, mul_left_comm 8 4, mul_left_comm 5 4]
    rw [pow_succ' 4 k, mul_left_comm 8 4] at hx
    by_cases h : 4 ∣ x
    · obtain ⟨y, rfl⟩ := h
      rw [isSquare_four_mul_iff, isSquare_four_mul_iff, ih y (by omega)]
      omega
    · constructor
      · rintro ⟨hs, hn⟩
        apply (h (four_dvd_of_not_isSquare (m := 2 * 4 ^ k) ?_ ?_)).elim
        · rwa [show 8 * (2 * 4 ^ k) = 4 * (4 * 4 ^ k) by ring]
        · rwa [show 16 * (2 * 4 ^ k) = 4 * (8 * 4 ^ k) by ring]
      · rintro rfl
        exact (h (dvd_mul_right ..)).elim

/-- For the step from an odd exponent to an even one, each pair of exceptional residues
is four times the preceding pair. -/
private theorem exceptional_residues_odd_to_even (k x : ℕ) (hx : x < 4 ^ k * 4) :
    (IsSquare (x : ZMod (4 ^ k * 2)) ∧ ¬IsSquare (x : ZMod (4 ^ k * 4))) ↔
      x = 4 ^ k * 2 ∨ x = 4 ^ k * 3 := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, one_mul] at hx ⊢
    interval_cases x <;> unfold IsSquare <;> decide
  | succ k ih =>
    rw [pow_succ' 4 k, mul_assoc 4 (4 ^ k) 4] at hx
    rw [pow_succ' 4 k, mul_assoc 4 (4 ^ k) 2, mul_assoc 4 (4 ^ k) 4, mul_assoc 4 (4 ^ k) 3]
    by_cases h : 4 ∣ x
    · obtain ⟨y, rfl⟩ := h
      rw [isSquare_four_mul_iff, isSquare_four_mul_iff, ih y (by omega)]
      omega
    · constructor
      · rintro ⟨hs, hn⟩
        apply (h (four_dvd_of_not_isSquare (m := 4 ^ k) ?_ ?_)).elim
        · rwa [show 8 * 4 ^ k = 4 * (4 ^ k * 2) by ring]
        · rwa [show 16 * 4 ^ k = 4 * (4 ^ k * 4) by ring]
      · omega

end SquaresModTwoPow

/-- **Residues that are squares modulo $2^{2k}$ but not modulo $2^{2k+1}$.** Let $k \ge 0$ and let
$x$ be an integer with $0 \le x < 2^{2k+1}$, where the exponent $2k - 2$ is truncated at $0$. Then
$x$ is a square modulo $2^{2k}$ but not a square modulo $2^{2k+1}$ if and only if
$x = 2^{2k} + 2^{2k-2}$.

For $k \ge 1$ this is the unique such residue; for $k = 0$ both sides of the equivalence are false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 3
(`integers-2025-A32-lem-3`). -/
public theorem isSquare_mod_two_pow_even_not_odd_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k + 1)) :
    (IsSquare (x : ZMod (2 ^ (2 * k))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k + 1)))) ↔
      x = 2 ^ (2 * k) + 2 ^ (2 * k - 2) := by
  cases k with
  | zero =>
    norm_num at hx ⊢
    interval_cases x <;> unfold IsSquare <;> decide
  | succ k =>
    have he : 2 * (k + 1) = 2 * k + 2 := by omega
    have hpow : (2 : ℕ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; rfl
    have hsmall : (2 : ℕ) ^ (2 * (k + 1)) = 4 * 4 ^ k := by
      rw [he, pow_add, hpow]
      ring
    have hlarge : (2 : ℕ) ^ (2 * (k + 1) + 1) = 8 * 4 ^ k := by
      rw [pow_succ, hsmall]
      ring
    rw [hlarge] at hx
    rw [hlarge, hsmall, he, Nat.add_sub_cancel, hpow, ← Nat.succ_mul]
    exact SquaresModTwoPow.exceptional_residue k x hx

/-- **Residues that are squares modulo $2^{2k-1}$ but not modulo $2^{2k}$.** Let $k \ge 0$ and let
$x$ be an integer with $0 \le x < 2^{2k}$, where the exponents $2k - 1$ and $2k - 2$ are truncated
at $0$. Then $x$ is a square modulo $2^{2k-1}$ but not a square modulo $2^{2k}$ if and only if
$x = 2^{2k-1}$ or $x = 2^{2k-1} + 2^{2k-2}$.

For $k \ge 1$ these are exactly two residues; for $k = 0$ both sides of the equivalence are false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 2
(`integers-2025-A32-lem-2`). -/
public theorem isSquare_mod_two_pow_odd_not_even_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k)) :
    (IsSquare (x : ZMod (2 ^ (2 * k - 1))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k)))) ↔
      x = 2 ^ (2 * k - 1) ∨ x = 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2) := by
  cases k with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst x
    norm_num
  | succ k =>
    have hp : (2 : ℕ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; rfl
    have hlarge : (2 : ℕ) ^ (2 * (k + 1)) = 4 ^ k * 4 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, hp]
      rfl
    have hsmall : (2 : ℕ) ^ (2 * (k + 1) - 1) = 4 ^ k * 2 := by
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, pow_succ, hp]
    rw [hlarge] at hx
    rw [hlarge, hsmall, show 2 * (k + 1) - 2 = 2 * k by omega, hp,
      show 4 ^ k * 2 + 4 ^ k = 4 ^ k * 3 by omega]
    exact SquaresModTwoPow.exceptional_residues_odd_to_even k x hx

end MetaMathlibExt
