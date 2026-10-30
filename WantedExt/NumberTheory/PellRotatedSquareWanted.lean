/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Pell

/-!
# Integer solutions of the Pell equation in a closed rotated square region

Statements from Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in
a Closed Rotated Square Region*, INTEGERS 25 (2025), Article A112.

For a positive nonsquare integer `D`, the fundamental solution `(α, β)` of `x² - D y² = 1` is
the coordinates of a Mathlib fundamental solution `a : Pell.Solution₁ D` (`Pell.IsFundamental a`,
which forces `0 < D` and `D` nonsquare), and `u_n + v_n √D = (α + β √D)^n` are the coordinates of
`a ^ n`. The real interpolations `u(x)` and `v(x)` of (1.3)-(1.4) are `pellU` and `pellV`; both
bases `α ± β √D` are positive, so real powers are used.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The function `u(x) = ((α + β √D)^x + (α - β √D)^x) / 2` of Equation (1.3).

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.3). -/
public noncomputable def pellU (D α β : ℤ) (x : ℝ) : ℝ :=
  ((α + β * Real.sqrt D) ^ x + (α - β * Real.sqrt D) ^ x) / 2

/-- The function `v(x) = ((α + β √D)^x - (α - β √D)^x) / (2 √D)` of Equation (1.4).

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.4). -/
public noncomputable def pellV (D α β : ℤ) (x : ℝ) : ℝ :=
  ((α + β * Real.sqrt D) ^ x - (α - β * Real.sqrt D) ^ x) / (2 * Real.sqrt D)

/-- `u(0) = 1`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.3). -/
public theorem pellU_zero (D α β : ℤ) : pellU D α β 0 = 1 := by
  norm_num [pellU]

/-- `v(0) = 0`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 1, Equation (1.4). -/
public theorem pellV_zero (D α β : ℤ) : pellV D α β 0 = 0 := by
  norm_num [pellV]

/-- Every integer solution of `x² - D y² = 1` is `(i u_n, j v_n)` for some `n ≥ 0` and signs
`i, j ∈ {1, -1}`, where `u_n + v_n √D = (α + β √D)^n`; conversely every such pair is a solution.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 1.1
(`integers-2025-A112-prop-1-1`). -/
public theorem_wanted pell_solutions_eq_signed_powers {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (x y : ℤ) :
    x ^ 2 - D * y ^ 2 = 1 ↔
      ∃ n : ℕ, ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        x = i * (a ^ n).x ∧ y = j * (a ^ n).y

/-- The functions `u` and `v` interpolate the solution sequences: `u(n) = u_n` and `v(n) = v_n`
for all integers `n ≥ 0`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 1.2
(`integers-2025-A112-prop-1-2`). -/
public theorem_wanted pellU_pellV_natCast {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (n : ℕ) :
    pellU D a.x a.y n = (a ^ n).x ∧ pellV D a.x a.y n = (a ^ n).y

/-- Closed form of `g = f⁻¹`, `f = u + v`: for real `x ≥ 1`, with
`z = (D x - √(D x² - D + 1)) / (D - 1)`, the value
`g(x) = cosh⁻¹(z) / log(α + β √D) = log(z + √(z² - 1)) / log(α + β √D)` is nonnegative and
satisfies `u(g(x)) + v(g(x)) = x`. The inverse cosine is written through its logarithmic form.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.2, Equation (2.1)
(`integers-2025-A112-thm-2-2`). -/
public theorem_wanted pell_inverse_closed_form {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x : ℝ} (hx : 1 ≤ x) :
    let z : ℝ := (D * x - Real.sqrt (D * x ^ 2 - D + 1)) / (D - 1)
    let g : ℝ := Real.log (z + Real.sqrt (z ^ 2 - 1)) / Real.log (a.x + a.y * Real.sqrt D)
    0 ≤ g ∧ pellU D a.x a.y g + pellV D a.x a.y g = x

/-- For real `x ≥ 1` and `t = g(x)` (the `t ≥ 0` with `u(t) + v(t) = x`),
`⌊g(x)⌋ = ⌊(log ⌊x⌋ + C) / log(α + β √D)⌋` with `C = log(2 √D / (1 + √D))`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.3, Equation (2.5)
(`integers-2025-A112-thm-2-3`). -/
public theorem_wanted pell_inverse_floor {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x t : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t)
    (htx : pellU D a.x a.y t + pellV D a.x a.y t = x) :
    ⌊t⌋ = ⌊(Real.log (⌊x⌋ : ℝ) + Real.log (2 * Real.sqrt D / (1 + Real.sqrt D))) /
      Real.log (a.x + a.y * Real.sqrt D)⌋

/-- Solutions of the Pell equation in the closed rotated square `|x| + |y| ≤ λ`: the set
`Q_{F_D}(λ) = {(x, y) ∈ ℤ² : x² - D y² = 1, |x| + |y| ≤ λ}` is empty for `λ < 1`; for `λ ≥ 1` and
`t = g(λ)` (the `t ≥ 0` with `u(t) + v(t) = λ`) it is the set of `(i u_n, j v_n)` with
`i, j ∈ {1, -1}` and integers `0 ≤ n ≤ g(λ)`, and it has `2 + 4 ⌊g(λ)⌋` elements.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.1
(`integers-2025-A112-thm-2-1`). -/
public theorem_wanted pell_solutions_in_rotated_square {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (lam : ℝ) :
    let Q : Set (ℤ × ℤ) := {p | p.1 ^ 2 - D * p.2 ^ 2 = 1 ∧ ((|p.1| + |p.2| : ℤ) : ℝ) ≤ lam}
    (lam < 1 → Q = ∅) ∧
    ∀ t : ℝ, 1 ≤ lam → 0 ≤ t → pellU D a.x a.y t + pellV D a.x a.y t = lam →
      Q = {p | ∃ n : ℕ, (n : ℝ) ≤ t ∧ ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        p = (i * (a ^ n).x, j * (a ^ n).y)} ∧
      Q.ncard = 2 + 4 * ⌊t⌋₊

/-- Explicit form of Theorem 2.1: for `λ ≥ 1`, with `C = log(2 √D / (1 + √D))` and
`m = ⌊(log ⌊λ⌋ + C) / log(α + β √D)⌋`, the solutions of `x² - D y² = 1` with `|x| + |y| ≤ λ` are
the `(i u_n, j v_n)` with `i, j ∈ {1, -1}` and `0 ≤ n ≤ m`, and there are `2 + 4 m` of them; for
`λ < 1` there are none.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Corollary 2.4
(`integers-2025-A112-cor-2-4`). -/
public theorem_wanted pell_solutions_in_rotated_square_explicit {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) (lam : ℝ) :
    let Q : Set (ℤ × ℤ) := {p | p.1 ^ 2 - D * p.2 ^ 2 = 1 ∧ ((|p.1| + |p.2| : ℤ) : ℝ) ≤ lam}
    let m : ℤ := ⌊(Real.log (⌊lam⌋ : ℝ) + Real.log (2 * Real.sqrt D / (1 + Real.sqrt D))) /
      Real.log (a.x + a.y * Real.sqrt D)⌋
    (lam < 1 → Q = ∅) ∧
    (1 ≤ lam →
      Q = {p | ∃ n : ℕ, (n : ℤ) ≤ m ∧ ∃ i j : ℤ, (i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1) ∧
        p = (i * (a ^ n).x, j * (a ^ n).y)} ∧
      (Q.ncard : ℤ) = 2 + 4 * m)

/-- The real solutions `R_{i,j}(x) = (i u(x) + a, j v(x) + b)` of the shifted Pell equation
`(x - a)² - D (y - b)² = 1` eventually lie in the closed quadrants: `R_{1,1}` in the first,
`R_{-1,1}` in the second, `R_{-1,-1}` in the third and `R_{1,-1}` in the fourth. The printed
statement swaps the third and fourth quadrants; this is the reading of the paper's proof.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.1
(`integers-2025-A112-prop-3-1`). -/
public theorem_wanted pell_shifted_real_solutions_eventually_in_quadrants {D : ℤ}
    {w : Pell.Solution₁ D} (hw : Pell.IsFundamental w) (a b : ℤ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (0 ≤ pellU D w.x w.y x + a ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ -pellV D w.x w.y x + b ≤ 0) ∧
      (0 ≤ pellU D w.x w.y x + a ∧ -pellV D w.x w.y x + b ≤ 0)

/-- For integers `a ≠ 0` and `b`, the largest `L¹` norm of an intercept of the shifted Pell curve
`(x - a)² - D (y - b)² = 1`, among `(a ± √(1 + D b²), 0)` and `(0, b ± √((a² - 1) / D))`, is
`|a| + √(1 + D b²)`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.2
(`integers-2025-A112-prop-3-2`). -/
public theorem_wanted pell_shifted_intercepts_max {D a : ℤ} (hD : 0 < D) (ha : a ≠ 0) (b : ℤ) :
    |(a : ℝ)| + Real.sqrt (1 + D * b ^ 2) =
      max (max |a + Real.sqrt (1 + D * b ^ 2)| |a - Real.sqrt (1 + D * b ^ 2)|)
        (max |b + Real.sqrt ((a ^ 2 - 1) / D)| |b - Real.sqrt ((a ^ 2 - 1) / D)|)

/-- The function `f_{i,j}(x) = |i u(x) + a| + |j v(x) + b|`, the `L¹` norm of the real solution
`R_{i,j}(x)` of the shifted Pell equation `(x - a)² - D (y - b)² = 1`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 3, definition of `f_{i,j}`. -/
public noncomputable def pellShiftedNorm (D α β a b i j : ℤ) (x : ℝ) : ℝ :=
  |i * pellU D α β x + a| + |j * pellV D α β x + b|

/-- `f_{i,j}(0) = |i + a| + |b|`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Section 3, definition of `f_{i,j}`. -/
public theorem pellShiftedNorm_zero (D α β a b i j : ℤ) :
    pellShiftedNorm D α β a b i j 0 = |(i : ℝ) + a| + |(b : ℝ)| := by
  simp [pellShiftedNorm, pellU_zero, pellV_zero]

/-- The constant `K = |a| + max(|b| + 1, √(1 + D b²))` of Theorem 3.3.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 3.3, definition of `K`. -/
public noncomputable def pellShiftBound (D a b : ℤ) : ℝ :=
  |(a : ℝ)| + max (|(b : ℝ)| + 1) (Real.sqrt (1 + D * b ^ 2))

/-- `K = 1` for the unshifted equation `a = b = 0`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 3.3, definition of `K`. -/
public theorem pellShiftBound_zero_zero (D : ℤ) : pellShiftBound D 0 0 = 1 := by
  simp [pellShiftBound]

/-- `f_{i,j}(0) ≤ K` for all signs `i, j ∈ {1, -1}`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.5
(`integers-2025-A112-lem-3-5`). -/
public theorem_wanted pellShiftedNorm_zero_le_pellShiftBound (D α β a b : ℤ) {i j : ℤ}
    (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    pellShiftedNorm D α β a b i j 0 ≤ pellShiftBound D a b

/-- With `x₁ = sup {x ≥ 0 : f_{i,j}(x) = K}` (Equation (3.6)), `f_{i,j}(x) ≤ K` for all
`x ∈ [0, x₁]`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.6
(`integers-2025-A112-lem-3-6`). -/
public theorem_wanted pellShiftedNorm_le_pellShiftBound {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1)
    {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ≤ sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}) :
    pellShiftedNorm D w.x w.y a b i j x ≤ pellShiftBound D a b

/-- With `x₁ = sup {x ≥ 0 : f_{i,j}(x) = K}` (Equation (3.6)), on `[x₁, ∞)` the function
`f_{i,j}` equals `u + v + i a + j b` (Equation (3.7)), is strictly increasing, and maps
`[x₁, ∞)` bijectively onto `[K, ∞)`.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Lemma 3.7
(`integers-2025-A112-lem-3-7`). -/
public theorem_wanted pellShiftedNorm_bijOn_Ici {D : ℤ} {w : Pell.Solution₁ D}
    (hw : Pell.IsFundamental w) (a b : ℤ) {i j : ℤ} (hi : i = 1 ∨ i = -1) (hj : j = 1 ∨ j = -1) :
    let x₁ : ℝ := sSup {y : ℝ | 0 ≤ y ∧
      pellShiftedNorm D w.x w.y a b i j y = pellShiftBound D a b}
    (∀ x, x₁ ≤ x →
      pellShiftedNorm D w.x w.y a b i j x = pellU D w.x w.y x + pellV D w.x w.y x + i * a + j * b) ∧
    StrictMonoOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) ∧
    Set.BijOn (pellShiftedNorm D w.x w.y a b i j) (Set.Ici x₁) (Set.Ici (pellShiftBound D a b))

end

end MetaMathlibExt
