/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic

/-!
# Sums of four squares via Hurwitz complex continued fractions

Statements from Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex
Continued Fractions*, INTEGERS 24 (2024), Article A25 (arXiv:2205.00642; TeX source read for
the definitions).

The Hurwitz algorithm expands `z = z_0 ∈ ℂ` by `a_n = [z_n]` (the nearest Gaussian integer,
`hurwitzRound`) and `z_{n+1} = (z_n - a_n)⁻¹` (`hurwitzIter`); the `Q`-pairs are
`P_{-1} = 1, P_0 = a_0, P_{n+1} = a_{n+1} P_n + P_{n-1}` and
`Q_{-1} = 0, Q_0 = 1, Q_{n+1} = a_{n+1} Q_n + Q_{n-1}` (`hurwitzP`, `hurwitzQ`). The paper's
nearest-integer rounding does not fix ties; we round halves up (`⌊t + 1/2⌋`). An index `n` is
*legal* (`HurwitzLegal z n`) when the expansion has not terminated before step `n`, i.e.
`z_j ≠ a_j` for all `j < n`; for `z ∈ ℚ[i]` with expansion `[a_0; …, a_m]` these are the
`n ≤ m`. After termination Lean's `0⁻¹ = 0` gives `z_{m+1} = 0`.
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
public theorem_wanted hurwitzQ_mul_sub_hurwitzP (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    hurwitzQ z n * z - hurwitzP z n =
        (-1) ^ n * (∏ j ∈ Finset.range (n + 1), hurwitzIter z (j + 1))⁻¹ ∧
      (1 ≤ n → hurwitzIter z (n + 1) =
        -(hurwitzQ z (n - 1) * z - hurwitzP z (n - 1)) / (hurwitzQ z n * z - hurwitzP z n))

/-- **Hurwitz's theorem: the convergent denominators grow in absolute value.** Let $z$ be a
complex number and let $Q_0, Q_1, \dots$ be the convergent denominators of its Hurwitz continued
fraction expansion. For every $n \ge 0$ such that $n + 1$ is a legal index for $z$ (the
expansion has not terminated before step $n + 1$), $|Q_n| < |Q_{n+1}|$.

Since $Q_0 = 1$, this gives $1 = |Q_0| < |Q_1| < \cdots < |Q_m|$ for every legal index $m$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 1 (`integers-2024-A25-lem-1`). -/
public theorem_wanted norm_hurwitzQ_lt_succ (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ‖hurwitzQ z n‖ < ‖hurwitzQ z (n + 1)‖

/-- **Lakein's first theorem on Hurwitz convergents.** Let $z$ be a complex number and let $P_k$
and $Q_k$ be the convergent numerators and denominators of its Hurwitz continued fraction
expansion. For every legal index $k$ for $z$ (the expansion has not terminated before step $k$),
$|z - P_k / Q_k| \le 1 / |Q_k|^2$.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 2 (`integers-2024-A25-lem-2`). -/
public theorem_wanted norm_sub_hurwitz_convergent_le (z : ℂ) (k : ℕ) (hk : HurwitzLegal z k) :
    ‖z - hurwitzP z k / hurwitzQ z k‖ ≤ 1 / ‖hurwitzQ z k‖ ^ 2

/-- **Sums of four squares via Hurwitz continued fractions.** Let $w$, $x$, $y$ be natural numbers
such that $w$ is odd and not a perfect square, $2x < w$, $2y < w$ and $w$ divides
$x^2 + y^2 + 1$. Expand $z = (x + yi)/w$ by the Hurwitz algorithm, with convergent numerators
$P_n$ and convergent denominators $Q_n$. Then there is exactly one natural number $n$ such that
$n + 1$ is a legal index for $z$, $|Q_n| \le \sqrt{w} < |Q_{n+1}|$, and, if $|Q_n| \ne \sqrt{w}$,
$w = |(x + yi) Q_n - w P_n|^2 + |Q_n|^2$.

When it holds, the last identity is a representation of $w$ as a sum of four squares.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Theorem 1 (`integers-2024-A25-thm-1`). -/
public theorem_wanted hurwitz_four_squares (w x y : ℕ) (hw : Odd w) (hsq : ¬ IsSquare w)
    (hx : 2 * x < w) (hy : 2 * y < w) (hmod : w ∣ x ^ 2 + y ^ 2 + 1) :
    let z : ℂ := (x + y * I) / w
    ∃! n, HurwitzLegal z (n + 1) ∧ ‖hurwitzQ z n‖ ≤ Real.sqrt w ∧
        Real.sqrt w < ‖hurwitzQ z (n + 1)‖ ∧
        (‖hurwitzQ z n‖ ≠ Real.sqrt w →
          (w : ℝ) = normSq ((x + y * I) * hurwitzQ z n - w * hurwitzP z n) +
            normSq (hurwitzQ z n))

end

end MetaMathlibExt
