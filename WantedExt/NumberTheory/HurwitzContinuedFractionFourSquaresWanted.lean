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

/-- The Gaussian integer nearest to `z`, rounding real and imaginary parts to the nearest
integer (halves rounded up).

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (notation `[z]`). -/
noncomputable def hurwitzRound (z : ℂ) : ℂ :=
  (⌊z.re + 1 / 2⌋ : ℂ) + (⌊z.im + 1 / 2⌋ : ℂ) * I

/-- The iteration sequence `z_0 = z`, `z_{n+1} = (z_n - [z_n])⁻¹` of the Hurwitz algorithm.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzIter (z : ℂ) : ℕ → ℂ
  | 0 => z
  | n + 1 => (hurwitzIter z n - hurwitzRound (hurwitzIter z n))⁻¹

/-- The partial quotients `a_n = [z_n]` of the Hurwitz algorithm.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzDigit (z : ℂ) (n : ℕ) : ℂ :=
  hurwitzRound (hurwitzIter z n)

/-- Consecutive `Q`-pairs `((P_{n-1}, Q_{n-1}), (P_n, Q_n))` of the Hurwitz expansion of `z`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzPQ (z : ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, 0), (hurwitzDigit z 0, 1))
  | n + 1 =>
    (((hurwitzPQ z n).2.1, (hurwitzPQ z n).2.2),
      (hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.1 + (hurwitzPQ z n).1.1,
        hurwitzDigit z (n + 1) * (hurwitzPQ z n).2.2 + (hurwitzPQ z n).1.2))

/-- The convergent numerator `P_n` (`n ≥ 0`) of the Hurwitz expansion of `z`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzP (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.1

/-- The convergent denominator `Q_n` (`n ≥ 0`) of the Hurwitz expansion of `z`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
noncomputable def hurwitzQ (z : ℂ) (n : ℕ) : ℂ :=
  (hurwitzPQ z n).2.2

/-- `n` is a legal index: the Hurwitz expansion of `z` has not terminated before step `n`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2 (remark after Proposition 1). -/
def HurwitzLegal (z : ℂ) (n : ℕ) : Prop :=
  ∀ j < n, hurwitzIter z j ≠ hurwitzDigit z j

/-- `z - [z]` lies in the square `|Re| ≤ 1/2`, `|Im| ≤ 1/2`.

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

/-- The initial `Q`-pairs and the recursion `P_{n+1} = a_{n+1} P_n + P_{n-1}`,
`Q_{n+1} = a_{n+1} Q_n + Q_{n-1}` for `n ≥ 1`, with `P_1 = a_1 a_0 + 1` and `Q_1 = a_1`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Section 2. -/
theorem hurwitzPQ_recursion (z : ℂ) (n : ℕ) :
    hurwitzP z 0 = hurwitzDigit z 0 ∧ hurwitzQ z 0 = 1 ∧
      hurwitzP z 1 = hurwitzDigit z 1 * hurwitzDigit z 0 + 1 ∧
      hurwitzQ z 1 = hurwitzDigit z 1 ∧
      hurwitzP z (n + 2) = hurwitzDigit z (n + 2) * hurwitzP z (n + 1) + hurwitzP z n ∧
      hurwitzQ z (n + 2) = hurwitzDigit z (n + 2) * hurwitzQ z (n + 1) + hurwitzQ z n := by
  simp [hurwitzP, hurwitzQ, hurwitzPQ]

/-- For legal `n ≥ 0`, `Q_n z - P_n = (-1)^n (z_1 ⋯ z_{n+1})⁻¹`, and for legal `n ≥ 1`,
`z_{n+1} = -(Q_{n-1} z - P_{n-1}) / (Q_n z - P_n)`. The `n = 0` case of the second identity,
`z_1 = (z - a_0)⁻¹` (with `Q_{-1} = 0`, `P_{-1} = 1`), is the definition of `hurwitzIter`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Proposition 1 (`integers-2024-A25-prop-1`). -/
public theorem_wanted hurwitzQ_mul_sub_hurwitzP (z : ℂ) (n : ℕ) (hn : HurwitzLegal z n) :
    hurwitzQ z n * z - hurwitzP z n =
        (-1) ^ n * (∏ j ∈ Finset.range (n + 1), hurwitzIter z (j + 1))⁻¹ ∧
      (1 ≤ n → hurwitzIter z (n + 1) =
        -(hurwitzQ z (n - 1) * z - hurwitzP z (n - 1)) / (hurwitzQ z n * z - hurwitzP z n))

/-- (Hurwitz, 1887) `1 = |Q_0| < |Q_1| < ⋯ < |Q_m|` for every legal `m`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 1 (`integers-2024-A25-lem-1`). -/
public theorem_wanted norm_hurwitzQ_lt_succ (z : ℂ) (n : ℕ) (hn : HurwitzLegal z (n + 1)) :
    ‖hurwitzQ z n‖ < ‖hurwitzQ z (n + 1)‖

/-- (First Lakein theorem) For every legal `k`, `|z - P_k / Q_k| ≤ 1 / |Q_k|^2`.

Source: Zhaonan Wang and Yingpu Deng, *Finding Sums of Four Squares via Complex Continued
Fractions*, INTEGERS 24 (2024), Article A25, Lemma 2 (`integers-2024-A25-lem-2`). -/
public theorem_wanted norm_sub_hurwitz_convergent_le (z : ℂ) (k : ℕ) (hk : HurwitzLegal z k) :
    ‖z - hurwitzP z k / hurwitzQ z k‖ ≤ 1 / ‖hurwitzQ z k‖ ^ 2

/-- **Main theorem.** Let `w` be odd and not a square, and let `0 ≤ x, y < w/2` with
`x^2 + y^2 ≡ -1 (mod w)`; expand `z = (x + y i)/w` by the Hurwitz algorithm. There is a unique
legal `n` (with `n + 1` legal) such that `|Q_n| ≤ √w < |Q_{n+1}|`, and if `|Q_n| ≠ √w` then
`w = |(x + y i) Q_n - w P_n|^2 + |Q_n|^2`, a representation of `w` as a sum of four squares.

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
