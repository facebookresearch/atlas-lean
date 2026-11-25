/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
import MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-!
# Prime terms of Lucas sequences with square second parameter

When `Q = s² ≠ 0` and `P > 2s` for the positive square root `s`, only the term at index
two of `U(P, Q)` can be prime. At larger even indices `P` is a proper divisor, and at odd indices
the addition formula gives a difference of squares.
-/

namespace MetaMathlibExt

namespace lucasU_square_q_finite_primes

open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted

private theorem odd_term (L : LucasSequenceParams) (k : ℕ) :
    lucasU L (2 * k + 1) = lucasU L (k + 1) ^ 2 - L.q * lucasU L k ^ 2 := by
  have companion (j : ℕ) : lucasV L j = 2 * lucasU L (j + 1) - L.p * lucasU L j := by
    have h := two_mul_lucasU_add L j 1
    simp only [show lucasV L 1 = L.p from rfl, show lucasU L 1 = 1 from rfl, mul_one] at h
    linarith
  have h := two_mul_lucasU_add L (k + 1) k
  rw [show k + 1 + k = 2 * k + 1 by omega, companion k, companion (k + 1),
    lucasU_add_two L k] at h
  linarith only [h]

/-- The gap between successive terms after scaling by `s + 1` is always positive. -/
private theorem growth (L : LucasSequenceParams) {s : ℤ} (hs : 1 ≤ s)
    (hq : L.q = s ^ 2) (hp : 2 * s < L.p) (k : ℕ) :
    0 ≤ lucasU L k ∧ (s + 1) * lucasU L k < lucasU L (k + 1) := by
  induction k with
  | zero => simp [lucasU]
  | succ k ih =>
    have hpos := (mul_nonneg (by omega : 0 ≤ s + 1) ih.1).trans ih.2.le
    refine ⟨hpos, ?_⟩
    rw [lucasU_add_two, hq]
    have hgap : 0 < lucasU L (k + 1) - s * lucasU L k := by linarith [ih.1, ih.2]
    nlinarith only [mul_pos (by omega : 0 < s) hgap,
      mul_nonneg (by omega : 0 ≤ L.p - 2 * s - 1) hpos]

end lucasU_square_q_finite_primes

open lucasU_square_q_finite_primes

/-- **Lucas sequences with square $Q$ have finitely many prime terms.** Let $P$ and $Q$ be
integers with $P \ge 1$ and $P^2 - 4Q > 0$, where $Q \ne 0$ is a perfect square, and let
$U_n = U_n(P, Q)$ be the Lucas sequence with $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = PU_{n+1} - QU_n$. Then $|U_n|$ is prime for only finitely many natural
numbers $n$.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 4(a)
(quoted from their reference [2]) (`integers-2025-A42-thm-4`). -/
public theorem lucasU_square_q_finite_primes {P Q : ℤ} (hQ : Q ≠ 0) (hP : 1 ≤ P)
    (hD : 0 < P ^ 2 - 4 * Q) (hsq : IsSquare Q) :
    {n : ℕ | (lucasU ⟨P, Q, hQ⟩ n).natAbs.Prime}.Finite := by
  obtain ⟨r, hr⟩ := hsq
  let s := |r|
  have hs : 1 ≤ s := abs_pos.mpr fun (h : r = 0) => hQ (by simp [hr, h])
  have hq : Q = s ^ 2 := by
    change Q = |r| ^ 2
    rwa [sq_abs, pow_two]
  have hp : 2 * s < P := lt_of_pow_lt_pow_left₀ 2 (by omega) (by linarith only [hD, hq])
  let L : LucasSequenceParams := ⟨P, Q, hQ⟩
  have bounds := growth L hs hq hp
  have hmono : StrictMono (lucasU L) := strictMono_nat_of_lt_succ fun k => by
    obtain ⟨h₀, h₁⟩ := bounds k
    linarith [mul_nonneg (by omega : 0 ≤ s) h₀]
  apply (Set.finite_lt_nat 3).subset
  intro n hn
  change (lucasU L n).natAbs.Prime at hn
  change n < 3
  by_contra! h
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hd := (p_dvd_lucasU_two_mul_and_lucasV_of_odd L).1 k
    have hlt := hmono (show 2 < 2 * k by omega)
    have h₂ : lucasU L 2 = P := by simp [L, lucasU]
    rw [h₂] at hlt
    exact Nat.not_prime_of_dvd_of_lt (Int.natAbs_dvd_natAbs.mpr hd) (by dsimp [L]; omega)
      (Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega : 0 ≤ P) hlt) hn
  · have hk := hmono (show 0 < k by omega)
    change 0 < lucasU L k at hk
    have hsmall : 1 < lucasU L (k + 1) - s * lucasU L k := by
      linarith [(bounds k).2]
    have hlarge : 1 < lucasU L (k + 1) + s * lucasU L k := by
      linarith [mul_nonneg (by omega : 0 ≤ s) hk.le]
    have hfactor : lucasU L (2 * k + 1) =
        (lucasU L (k + 1) - s * lucasU L k) * (lucasU L (k + 1) + s * lucasU L k) := by
      rw [odd_term, show L.q = s ^ 2 from hq]
      ring
    rw [hfactor, Int.natAbs_mul] at hn
    exact Nat.not_prime_mul (by omega) (by omega) hn

end MetaMathlibExt
