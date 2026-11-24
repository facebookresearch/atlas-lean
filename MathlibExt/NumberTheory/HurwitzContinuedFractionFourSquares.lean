/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic

/-!
# Errors of Hurwitz continued fraction convergents

`hurwitzQ_mul_sub_hurwitzP` expresses the convergent error as a signed reciprocal
product of the iterates and recovers the next iterate from two consecutive errors.

The iterates and convergents follow Zhaonan Wang and Yingpu Deng, *Finding Sums of Four
Squares via Complex Continued Fractions*. Rounding ties go to the larger integer in each
coordinate. The final index of a finite expansion is legal, and its next iterate is zero.
-/

open Complex

namespace MetaMathlibExt

@[expose] public section

/-- **Hurwitz rounding to the nearest Gaussian integer.** For a complex number $z$, let
$[z] = m + n i$, where $m = \lfloor \operatorname{Re} z + 1/2 \rfloor$ and
$n = \lfloor \operatorname{Im} z + 1/2 \rfloor$; that is, the real and imaginary parts of $z$ are
rounded to the nearest integer, with halves rounded up. Then $[z]$ is a Gaussian integer nearest
to $z$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (notation `[z]`). -/
noncomputable def hurwitzRound (z : ℂ) : ℂ :=
  (⌊z.re + 1 / 2⌋ : ℂ) + (⌊z.im + 1 / 2⌋ : ℂ) * I

/-- **Iterates of the Hurwitz algorithm.** For a complex number $z$, the Hurwitz iterates are
$z_0 = z$ and $z_{n+1} = (z_n - [z_n])^{-1}$ for $n \ge 0$, where $[u]$ is the Gaussian integer
nearest to $u$, obtained by rounding the real and imaginary parts of $u$ to the nearest integer
with halves rounded up, and where the inverse of $0$ is taken to be $0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzIter (z : ℂ) : ℕ → ℂ
  | 0 => z
  | n + 1 => (hurwitzIter z n - hurwitzRound (hurwitzIter z n))⁻¹

/-- **Partial quotients of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz
iterates $z_0 = z, z_1, z_2, \dots$. For $n \ge 0$, the $n$-th partial quotient is $a_n = [z_n]$,
the Gaussian integer nearest to $z_n$, obtained by rounding the real and imaginary parts of
$z_n$ to the nearest integer with halves rounded up.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzDigit (z : ℂ) (n : ℕ) : ℂ :=
  hurwitzRound (hurwitzIter z n)

/-- **Consecutive pairs of Hurwitz convergents.** Let $z$ be a complex number with Hurwitz
partial quotients $a_0, a_1, a_2, \dots$. This is the sequence whose term for $n \ge 0$ is the
pair of pairs of complex numbers $((P_{n-1}, Q_{n-1}), (P_n, Q_n))$, where $P_{-1} = 1$,
$Q_{-1} = 0$, $P_0 = a_0$, $Q_0 = 1$, and $P_{n+1} = a_{n+1} P_n + P_{n-1}$ and
$Q_{n+1} = a_{n+1} Q_n + Q_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzPQ (z : ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, 0), (hurwitzDigit z 0, 1))
  | n + 1 =>
    (((hurwitzPQ z n).2.1, (hurwitzPQ z n).2.2),
      (hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.1 + (hurwitzPQ z n).1.1,
        hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.2 + (hurwitzPQ z n).1.2))

/-- **Convergent numerators of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz
partial quotients $a_0, a_1, a_2, \dots$. Its convergent numerators $P_n$, $n \ge 0$, are given by
$P_{-1} = 1$, $P_0 = a_0$ and $P_{n+1} = a_{n+1} P_n + P_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzP (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.1

/-- **Convergent denominators of the Hurwitz expansion.** Let $z$ be a complex number with
Hurwitz partial quotients $a_0, a_1, a_2, \dots$. Its convergent denominators $Q_n$, $n \ge 0$,
are given by $Q_{-1} = 0$, $Q_0 = 1$ and $Q_{n+1} = a_{n+1} Q_n + Q_{n-1}$ for $n \ge 0$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzQ (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.2

/-- **Legal indices of the Hurwitz expansion.** Let $z$ be a complex number with Hurwitz iterates
$z_j$ and partial quotients $a_j$. A natural number $n$ is a legal index for $z$ when
$z_j \ne a_j$ for every $j < n$, that is, when the Hurwitz expansion of $z$ has not terminated
before step $n$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (remark after Proposition 1). -/
def HurwitzLegal (z : ℂ) (n : ℕ) : Prop :=
  ∀ j < n, hurwitzIter z j ≠ hurwitzDigit z j

/-- **Rounding error of the nearest Gaussian integer.** For every complex number $z$, let $[z]$ be
the Gaussian integer nearest to $z$, obtained by rounding the real and imaginary parts to the
nearest integer with halves rounded up. Then $|\operatorname{Re}(z - [z])| \le 1/2$ and
$|\operatorname{Im}(z - [z])| \le 1/2$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (the set `Φ`). -/
theorem abs_re_sub_hurwitzRound_le (z : ℂ) :
    |(z - hurwitzRound z).re| ≤ 1 / 2 ∧ |(z - hurwitzRound z).im| ≤ 1 / 2 := by
  simp only [hurwitzRound, sub_re, add_re, intCast_re, mul_re, intCast_im, I_re, I_im,
    sub_im, add_im, mul_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
  have h1 := Int.floor_le (z.re + 1 / 2)
  have h2 := Int.lt_floor_add_one (z.re + 1 / 2)
  have h3 := Int.floor_le (z.im + 1 / 2)
  have h4 := Int.lt_floor_add_one (z.im + 1 / 2)
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- **Recursion for the Hurwitz convergents.** Let $z$ be a complex number with Hurwitz partial
quotients $a_n$, convergent numerators $P_n$ and convergent denominators $Q_n$. Then
$P_0 = a_0$, $Q_0 = 1$, $P_1 = a_1 a_0 + 1$ and $Q_1 = a_1$, and for every $n \ge 0$,
$P_{n+2} = a_{n+2} P_{n+1} + P_n$ and $Q_{n+2} = a_{n+2} Q_{n+1} + Q_n$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
theorem hurwitzPQ_recursion (z : ℂ) (n : ℕ) :
    hurwitzP z 0 = hurwitzDigit z 0 ∧ hurwitzQ z 0 = 1 ∧
      hurwitzP z 1 = hurwitzDigit z 1 * hurwitzDigit z 0 + 1 ∧
      hurwitzQ z 1 = hurwitzDigit z 1 ∧
      hurwitzP z (n + 2) = hurwitzDigit z (n + 2) * hurwitzP z (n + 1) + hurwitzP z n ∧
      hurwitzQ z (n + 2) = hurwitzDigit z (n + 2) * hurwitzQ z (n + 1) + hurwitzQ z n := by
  simp [hurwitzP, hurwitzQ, hurwitzPQ]

namespace hurwitzQ_mul_sub_hurwitzP

private noncomputable def error (z : ℂ) (pq : ℂ × ℂ) : ℂ := pq.2 * z - pq.1

-- The pair at index zero includes the initial error Q₋₁ z - P₋₁ = -1.
private theorem error_step (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    error z (hurwitzPQ z n).1 ≠ 0 ∧
      error z (hurwitzPQ z n).2 = -error z (hurwitzPQ z n).1 / hurwitzIter z (n + 1) := by
  induction n with
  | zero => simp [error, hurwitzPQ, hurwitzIter, hurwitzDigit]
  | succ n ih =>
    obtain ⟨hne, hstep⟩ := ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))
    have hz : hurwitzIter z (n + 1) ≠ 0 :=
      inv_ne_zero (sub_ne_zero.mpr (hn n (Nat.lt_succ_self n)))
    refine ⟨hstep ▸ div_ne_zero (neg_ne_zero.mpr hne) hz, ?_⟩
    have hrec : error z (hurwitzPQ z (n + 1)).2 =
        hurwitzDigit z (n + 1) * error z (hurwitzPQ z n).2 + error z (hurwitzPQ z n).1 := by
      simp only [error, hurwitzPQ]
      ring
    rw [hrec]
    change _ = -error z (hurwitzPQ z n).2 / (hurwitzIter z (n + 1) - hurwitzDigit z (n + 1))⁻¹
    rw [div_inv_eq_mul]
    linear_combination (eq_div_iff hz).mp hstep

end hurwitzQ_mul_sub_hurwitzP

/-- **Error of the Hurwitz convergents.** Let $z$ be a complex number with Hurwitz iterates
$z_0 = z, z_1, z_2, \dots$, convergent numerators $P_n$ and convergent denominators $Q_n$. For
every legal index $n$ for $z$,
$$Q_n z - P_n = (-1)^n (z_1 z_2 \cdots z_{n+1})^{-1},$$
and if moreover $n \ge 1$, then $z_{n+1} = -(Q_{n-1} z - P_{n-1}) / (Q_n z - P_n)$. Here the
inverse of $0$ and any quotient by $0$ are taken to be $0$.

The case $n = 0$ of the second identity, $z_1 = (z - a_0)^{-1}$ with $a_0$ the first partial
quotient (and $Q_{-1} = 0$, $P_{-1} = 1$), is the definition of the iterates.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Proposition 1 (`integers-2024-A25-prop-1`). -/
theorem hurwitzQ_mul_sub_hurwitzP (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    hurwitzQ z n * z - hurwitzP z n =
        (-1) ^ n * (∏ j ∈ Finset.range (n + 1), hurwitzIter z (j + 1))⁻¹ ∧
      (1 ≤ n → hurwitzIter z (n + 1) =
        -(hurwitzQ z (n - 1) * z - hurwitzP z (n - 1)) / (hurwitzQ z n * z - hurwitzP z n)) := by
  induction n with
  | zero => simp [hurwitzQ, hurwitzP, hurwitzPQ, hurwitzIter, hurwitzDigit]
  | succ n ih =>
    obtain ⟨hne, hstep⟩ := hurwitzQ_mul_sub_hurwitzP.error_step z (n + 1) hn
    change hurwitzQ z n * z - hurwitzP z n ≠ 0 at hne
    change hurwitzQ z (n + 1) * z - hurwitzP z (n + 1) =
      -(hurwitzQ z n * z - hurwitzP z n) / hurwitzIter z (n + 2) at hstep
    rw [hstep]
    refine ⟨?_, fun _ => (div_div_cancel₀ (neg_ne_zero.mpr hne)).symm⟩
    rw [(ih (fun j hj => hn j (Nat.lt_succ_of_lt hj))).1, Finset.prod_range_succ _ (n + 1),
      pow_succ, mul_inv_rev, div_eq_mul_inv]
    ring

end

end MetaMathlibExt
