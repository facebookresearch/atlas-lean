/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.Pell

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- The `y`-component of the least positive integral solution of the negative Pell equation
`x² - d y² = -1` (the least `y > 0` with `x² + 1 = d y²` for some `x : ℕ`), and `0` when there is
none.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundY (d : ℕ) : ℕ :=
  if h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 then Nat.find h else 0

/-- The `x`-component `√(d Y² - 1)` of the least positive integral solution
`(X, Y)` of `x² - d y² = -1`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellFundX (d : ℕ) : ℕ :=
  Nat.sqrt (d * negPellFundY d ^ 2 - 1)

open Classical in
/-- If `x² - d y² = -1` has a positive integral solution, `(negPellFundX d, negPellFundY d)` is
one, with positive `y`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_spec {d : ℕ} (h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    0 < negPellFundY d ∧ negPellFundX d ^ 2 + 1 = d * negPellFundY d ^ 2 := by
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  obtain ⟨hpos, x, hx⟩ := Nat.find_spec h
  rw [← hY] at hpos hx
  refine ⟨hpos, ?_⟩
  have : d * negPellFundY d ^ 2 - 1 = x ^ 2 := by omega
  simp only [negPellFundX, this, Nat.sqrt_eq']
  exact hx

open Classical in
/-- Minimality: `negPellFundY d` is at most every positive `y` for which `x² - d y² = -1` has a
solution.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFundY_le {d y : ℕ} (hy : 0 < y) (hx : ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2) :
    negPellFundY d ≤ y := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = d * y ^ 2 := ⟨y, hy, hx⟩
  have hY : negPellFundY d = Nat.find h := by simp [negPellFundY, h]
  rw [hY]
  exact Nat.find_min' h ⟨hy, hx⟩

open Classical in
/-- For `d = 2` the least positive solution of `x² - 2 y² = -1` is `(1, 1)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)-(24)
(`integers-2024-A111-prop-5`). -/
theorem negPellFund_two : negPellFundY 2 = 1 ∧ negPellFundX 2 = 1 := by
  have h : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 + 1 = 2 * y ^ 2 := ⟨1, by norm_num, 1, by norm_num⟩
  have hY : negPellFundY 2 = 1 := by
    simp only [negPellFundY, h, dite_true]
    rw [Nat.find_eq_iff]
    exact ⟨⟨by norm_num, 1, by norm_num⟩, fun n hn ⟨hn0, _⟩ => by omega⟩
  refine ⟨hY, ?_⟩
  simp [negPellFundX, hY]

/-- The `x`-sequence `f_n` of the powers `ε^n = f_n + g_n √d` of the least positive unit
`ε = X + Y √d` of norm `-1` in `ℤ[√d]` (`(X, Y)` the least positive solution of `x² - d y² = -1`).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellF (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).re

/-- The `y`-sequence `g_n` of the powers `ε^n = f_n + g_n √d` of the least positive unit
`ε = X + Y √d` of norm `-1` in `ℤ[√d]`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
noncomputable def negPellG (d n : ℕ) : ℤ :=
  ((⟨negPellFundX d, negPellFundY d⟩ : ℤ√(d : ℤ)) ^ n).im

/-- `f_0 = 1` and `g_0 = 0`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
@[simp]
theorem negPellF_zero_negPellG_zero (d : ℕ) : negPellF d 0 = 1 ∧ negPellG d 0 = 0 := by
  simp [negPellF, negPellG]

/-- Recurrence from `ε^{n+1} = ε^n ε`: `f_{n+1} = f_n X + d g_n Y` and
`g_{n+1} = f_n Y + g_n X`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPell_succ (d n : ℕ) :
    negPellF d (n + 1) = negPellF d n * negPellFundX d + d * negPellG d n * negPellFundY d ∧
      negPellG d (n + 1) = negPellF d n * negPellFundY d + negPellG d n * negPellFundX d := by
  simp [negPellF, negPellG, pow_succ]

/-- For `d = 2`: `f_1 = g_1 = 1`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5, (23)
(`integers-2024-A111-prop-5`). -/
theorem negPellF_two_one : negPellF 2 1 = 1 ∧ negPellG 2 1 = 1 := by
  simp [negPellF, negPellG, negPellFund_two]

/-- Angle bisectors: if `|a| ≠ |b|`, `c ≠ 0`, and the lines `y = c x` and `y = -c⁻¹ x` bisect
the angles between `y = a x` and `y = b x`, then `(a - c)² (b² + 1) = (b - c)² (a² + 1)` (1).

A line `y = s x` bisects the angles between `y = a x` and `y = b x` when its point `(1, s)` is
equidistant from both lines: `|a - s| / √(a² + 1) = |b - s| / √(b² + 1)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(a)
(`integers-2024-A111-prop-1`). -/
public theorem_wanted bisector_slope_equation (a b c : ℝ) (hab : |a| ≠ |b|) (hc : c ≠ 0)
    (hbis : |a - c| / √(a ^ 2 + 1) = |b - c| / √(b ^ 2 + 1))
    (hbis' : |a + c⁻¹| / √(a ^ 2 + 1) = |b + c⁻¹| / √(b ^ 2 + 1)) :
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- Every rational solution `(a, b, c)` of `(a - c)² (b² + 1) = (b - c)² (a² + 1)` with
`|a| ≠ |b|` has the form `c = (a b₂ + a₂ b) / (b₂ + a₂)` or `c = (a b₂ - a₂ b) / (b₂ - a₂)`,
where `(a, a₂)` and `(b, b₂)` are rational solutions of `x² - d y² = -1` for one positive
square-free integer `d`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 1(b)
(`integers-2024-A111-prop-1`). -/
public theorem_wanted bisector_equation_rat_solution (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧
      b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((b₂ + a₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (b₂ + a₂)) ∨
        (b₂ - a₂ ≠ 0 ∧ c = (a * b₂ - a₂ * b) / (b₂ - a₂)))

/-- Symmetries of (1): if `(a, b, c)` is a real solution of
`(a - c)² (b² + 1) = (b - c)² (a² + 1)`, then so are `(a, b, -c⁻¹)` (for `c ≠ 0`), `(-a, -b, -c)`
and `(b, a, c)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(a)
(`integers-2024-A111-prop-2`). -/
public theorem_wanted bisector_equation_symm (a b c : ℝ)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    (c ≠ 0 → (a - -c⁻¹) ^ 2 * (b ^ 2 + 1) = (b - -c⁻¹) ^ 2 * (a ^ 2 + 1)) ∧
      (-a - -c) ^ 2 * ((-b) ^ 2 + 1) = (-b - -c) ^ 2 * ((-a) ^ 2 + 1) ∧
      (b - c) ^ 2 * (a ^ 2 + 1) = (a - c) ^ 2 * (b ^ 2 + 1)

/-- If `a = 0` or `b = 0`, then `(a - c)² (b² + 1) = (b - c)² (a² + 1)` has no nontrivial integral
solutions (every integral solution has `|a| = |b|`).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 2(b)
(`integers-2024-A111-prop-2`). -/
public theorem_wanted bisector_equation_int_zero (a b c : ℤ) (h0 : a = 0 ∨ b = 0)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) : |a| = |b|

/-- Integral solutions of (1): every integral solution `(a, b, c)` of
`(a - c)² (b² + 1) = (b - c)² (a² + 1)` with `|a| ≠ |b|` is, after switching `a` and `b` if
necessary, `± (f_{(2m-1)(2n-1)}, f_{(2m-1)(2n+1)}, g_{(2m-1) 2n} / g_{2m-1})` for the sequences of
some square-free `d > 1` whose negative Pell equation is solvable in integers and some
`m, n > 0` (9), or `± (f_{2n-1}, -f_{2n+1}, f_{2n})` for `d = 2` and some `n > 0` (10).

The quotient `g_{(2m-1) 2n} / g_{2m-1}` is integer division; it is exact.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3 (`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_int_solution (a b c : ℤ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ((∃ d m n : ℕ, 1 < d ∧ Squarefree d ∧ (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) ∧ 0 < m ∧
          0 < n ∧
          let t : ℤ × ℤ × ℤ := (s * negPellF d ((2 * m - 1) * (2 * n - 1)),
            s * negPellF d ((2 * m - 1) * (2 * n + 1)),
            s * (negPellG d ((2 * m - 1) * (2 * n)) / negPellG d (2 * m - 1)))
          (a, b, c) = t ∨ (b, a, c) = t) ∨
        ∃ n : ℕ, 0 < n ∧
          let t : ℤ × ℤ × ℤ := (s * negPellF 2 (2 * n - 1), -(s * negPellF 2 (2 * n + 1)),
            s * negPellF 2 (2 * n))
          (a, b, c) = t ∨ (b, a, c) = t)

/-- Converse of Theorem 3, Form (9): for `d > 1` whose negative Pell equation is solvable in
integers and `m, n > 0`, `(f_{(2m-1)(2n-1)}, f_{(2m-1)(2n+1)}, g_{(2m-1) 2n} / g_{2m-1})` solves
`(a - c)² (b² + 1) = (b - c)² (a² + 1)`.

Square-freeness of `d` is not needed here.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (9)
(`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_form_nine (d m n : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (hm : 0 < m) (hn : 0 < n) :
    let a := negPellF d ((2 * m - 1) * (2 * n - 1))
    let b := negPellF d ((2 * m - 1) * (2 * n + 1))
    let c := negPellG d ((2 * m - 1) * (2 * n)) / negPellG d (2 * m - 1)
    negPellG d (2 * m - 1) ∣ negPellG d ((2 * m - 1) * (2 * n)) ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- Converse of Theorem 3, Form (10): for `n > 0`, `(f_{2n-1}, -f_{2n+1}, f_{2n})` with `d = 2`
solves `(a - c)² (b² + 1) = (b - c)² (a² + 1)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 3, converse for (10)
(`integers-2024-A111-thm-3`). -/
public theorem_wanted bisector_equation_form_ten (n : ℕ) (hn : 0 < n) :
    let a := negPellF 2 (2 * n - 1)
    let b := -negPellF 2 (2 * n + 1)
    let c := negPellF 2 (2 * n)
    (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- Classes of solutions of a general Pell equation: for `d > 0` not a square and `z ≠ 0`, if
`x² - d y² = z` is solvable in integers, there are finitely many solutions `(a_i, b_i)` such that
every solution satisfies `x + y √d = ± ε^n (a_i + b_i √d)` for some `i` and `n ∈ ℤ`.

`ε` is taken to be the fundamental solution of `x² - d y² = 1` (Mathlib `Pell.IsFundamental`);
since its powers are among the powers of the fundamental unit of norm `±1`, this form implies the
source's.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 6 (quoting its reference [4,
Corollary 3.5]) (`integers-2024-A111-thm-6`). -/
public theorem_wanted generalPell_finitely_many_classes (d : ℤ) (hd₀ : 0 < d)
    (hd : ¬IsSquare d) (ε : Pell.Solution₁ d) (hε : Pell.IsFundamental ε) (z : ℤ) (hz : z ≠ 0)
    (hsol : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = z) :
    ∃ s : Finset (ℤ × ℤ), (∀ p ∈ s, p.1 ^ 2 - d * p.2 ^ 2 = z) ∧
      ∀ x y : ℤ, x ^ 2 - d * y ^ 2 = z → ∃ p ∈ s, ∃ n : ℤ, ∃ σ : ℤ√d, (σ = 1 ∨ σ = -1) ∧
        (⟨x, y⟩ : ℤ√d) = σ * ((ε ^ n : Pell.Solution₁ d) : ℤ√d) * ⟨p.1, p.2⟩

/-- For a positive square-free integer `d`, `x² - d y² = -1` has a rational solution if and only
if `d` has no prime divisor congruent to `3` modulo `4`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 5 (`integers-2024-A111-thm-5`). -/
public theorem_wanted negPell_rat_solvable_iff (d : ℕ) (hd : 0 < d) (hsq : Squarefree d) :
    (∃ x y : ℚ, x ^ 2 - d * y ^ 2 = -1) ↔ ∀ p : ℕ, p.Prime → p ∣ d → p % 4 ≠ 3

/-- Basic properties of `f_n, g_n` for `d > 1` whose negative Pell equation is solvable in
integers: `f_n² - d g_n² = (-1)^n` (24), `(g_n)` is strictly increasing, `(f_n)` is strictly
increasing from `n = 1`, and `f_n = (εⁿ + ε'ⁿ) / 2`, `g_n = (εⁿ - ε'ⁿ) / (2 √d)` (25)-(26) with
`ε = X + Y √d`, `ε' = X - Y √d`.

Deviation: `(f_n)` is not strictly increasing from `n = 0` when `d = 2` (`f_0 = f_1 = 1`), so
monotonicity of `f` is stated on `n ≥ 1`. (23) holds by definition.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 5 (`integers-2024-A111-prop-5`). -/
public theorem_wanted negPell_sequences_basic (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) :
    (∀ n : ℕ, negPellF d n ^ 2 - d * negPellG d n ^ 2 = (-1) ^ n) ∧
      StrictMono (negPellG d) ∧ StrictMonoOn (negPellF d) (Set.Ici 1) ∧
      ∀ n : ℕ,
        (negPellF d n : ℝ) = ((negPellFundX d + negPellFundY d * √d) ^ n +
          (negPellFundX d - negPellFundY d * √d) ^ n) / 2 ∧
        (negPellG d n : ℝ) = ((negPellFundX d + negPellFundY d * √d) ^ n -
          (negPellFundX d - negPellFundY d * √d) ^ n) / (2 * √d)

/-- Addition and double formulas: for `m ≥ n`,
`f_{m+n} = f_m f_n + d g_m g_n`, `g_{m+n} = f_m g_n + g_m f_n`,
`f_{m-n} = (-1)^n (f_m f_n - d g_m g_n)`, `g_{m-n} = (-1)^{n+1} (f_m g_n - g_m f_n)`,
`f_{2n} = f_n² + d g_n²`, `g_{2n} = 2 f_n g_n`.

Only solvability of `x² - d y² = -1` is assumed (the source's `d > 1` is not needed).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 6 (`integers-2024-A111-prop-6`). -/
public theorem_wanted negPell_addition_formulas (d : ℕ) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (m n : ℕ) (hnm : n ≤ m) :
    negPellF d (m + n) = negPellF d m * negPellF d n + d * negPellG d m * negPellG d n ∧
      negPellG d (m + n) = negPellF d m * negPellG d n + negPellG d m * negPellF d n ∧
      negPellF d (m - n) =
        (-1) ^ n * (negPellF d m * negPellF d n - d * negPellG d m * negPellG d n) ∧
      negPellG d (m - n) =
        (-1) ^ (n + 1) * (negPellF d m * negPellG d n - negPellG d m * negPellF d n) ∧
      negPellF d (2 * n) = negPellF d n ^ 2 + d * negPellG d n ^ 2 ∧
      negPellG d (2 * n) = 2 * negPellF d n * negPellG d n

/-- Sum and difference formulas: for `m > n`, `f_{m+n} ± f_{m-n}` and `g_{m+n} ± g_{m-n}` equal
`2 f_m f_n`, `2 d g_m g_n`, `2 g_m f_n` or `2 f_m g_n` according to the parity of `n`
((33)-(36)).

Only solvability of `x² - d y² = -1` is assumed (the source's `d > 1` is not needed).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 7 (`integers-2024-A111-prop-7`). -/
public theorem_wanted negPell_sum_difference_formulas (d : ℕ)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hnm : n < m) :
    negPellF d (m + n) + negPellF d (m - n) =
        (if n % 2 = 0 then 2 * negPellF d m * negPellF d n
          else 2 * d * negPellG d m * negPellG d n) ∧
      negPellF d (m + n) - negPellF d (m - n) =
        (if n % 2 = 0 then 2 * d * negPellG d m * negPellG d n
          else 2 * negPellF d m * negPellF d n) ∧
      negPellG d (m + n) + negPellG d (m - n) =
        (if n % 2 = 0 then 2 * negPellG d m * negPellF d n
          else 2 * negPellF d m * negPellG d n) ∧
      negPellG d (m + n) - negPellG d (m - n) =
        (if n % 2 = 0 then 2 * negPellF d m * negPellG d n
          else 2 * negPellG d m * negPellF d n)

/-- For `d > 1` whose negative Pell equation is solvable in integers, `g_n ≤ f_n`, with equality
if and only if `d = 2` and `n = 1`.

The record's second sentence (printed `f_1 ≥ d - 1`, with a displaced `√` glyph; the literal
reading fails at `d = 5`, `f_1 = 2`) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 2, first sentence
(`integers-2024-A111-cor-2`). -/
public theorem_wanted negPellG_le_negPellF (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) :
    negPellG d n ≤ negPellF d n ∧ (negPellF d n = negPellG d n ↔ d = 2 ∧ n = 1)

/-- For `d > 1` whose negative Pell equation is solvable in integers and `n > 0`,
`gcd(d, f_n) = gcd(f_n, g_n) = 1`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(a) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPell_gcd_eq_one (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (n : ℕ) (hn : 0 < n) :
    Int.gcd d (negPellF d n) = 1 ∧ Int.gcd (negPellF d n) (negPellG d n) = 1

/-- For `d > 1` whose negative Pell equation is solvable in integers and `0 < n ≤ m`: if `m` is a
multiple of `n` with even quotient, then `gcd(f_m, f_n) = 1`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(b) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellF_gcd_of_even_quotient (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (hdvd : n ∣ m) (heven : Even (m / n)) :
    Int.gcd (negPellF d m) (negPellF d n) = 1

/-- For `d > 1` whose negative Pell equation is solvable in integers and `0 < n ≤ m`: `f_n ∣ f_m`
if and only if either `d = 2` and `n = 1`, or `m` is a multiple of `n` with odd quotient.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(c) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellF_dvd_iff (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    negPellF d n ∣ negPellF d m ↔ (d = 2 ∧ n = 1) ∨ (n ∣ m ∧ Odd (m / n))

/-- For `d > 1` whose negative Pell equation is solvable in integers and `0 < n ≤ m`: `g_n ∣ g_m`
if and only if `n ∣ m`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 11(d) (`integers-2024-A111-thm-11`). -/
public theorem_wanted negPellG_dvd_iff (d : ℕ) (hd : 1 < d)
    (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    negPellG d n ∣ negPellG d m ↔ n ∣ m

/-- If `d ≡ 1 (mod 4)` and `z ≡ 2 (mod 4)`, then `|x² - d y²| = z` has no integral solutions.

The source's `z > 1` is not needed. The second sentence of part (a) (on `S(d)` and `l_2`) is not
formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(a), first sentence
(`integers-2024-A111-lem-1`). -/
public theorem_wanted abs_sq_sub_mul_sq_ne_of_two_mod_four (d z : ℤ) (hd : d % 4 = 1)
    (hz : z % 4 = 2) (x y : ℤ) : |x ^ 2 - d * y ^ 2| ≠ z

/-- If `d ≡ 1 (mod 8)` and `z ≡ 4 (mod 8)`, then every integral solution of `|x² - d y²| = z` is a
pair of even integers.

The source's `z > 1` is not needed. The second sentence of part (c) (on `η`) is not formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(c), first sentence
(`integers-2024-A111-lem-1`). -/
public theorem_wanted even_of_abs_sq_sub_mul_sq_four_mod_eight (d z : ℤ) (hd : d % 8 = 1)
    (hz : z % 8 = 4) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y

/-- If `d ≡ 5 (mod 8)` and `z ≡ 0 (mod 8)`, then every integral solution of `|x² - d y²| = z` is a
pair of even integers.

The source's `z > 1` is not needed.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Lemma 1(d) (`integers-2024-A111-lem-1`). -/
public theorem_wanted even_of_abs_sq_sub_mul_sq_zero_mod_eight (d z : ℤ) (hd : d % 8 = 5)
    (hz : z % 8 = 0) (x y : ℤ) (h : |x ^ 2 - d * y ^ 2| = z) : Even x ∧ Even y

open Classical in
/-- `S(d)`: the primes `p` for which `|x² - d y²| = p^l` has a strictly primitive integral solution
(`x` and `d y` coprime) for some integer `l > 0`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-thm-8`). -/
def strictPrimitivePrimes (d : ℤ) : Set ℕ :=
  {p | p.Prime ∧ ∃ l : ℕ, 0 < l ∧ ∃ x y : ℤ, IsCoprime x (d * y) ∧ |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ l}

open Classical in
/-- `l_p`: for `p ∈ S(d)`, the least integer `l > 0` such that `|x² - d y²| = p^l` has a strictly
primitive integral solution; `0` when `p ∉ S(d)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
noncomputable def strictPrimitiveExponent (d : ℤ) (p : ℕ) : ℕ :=
  if h : p ∈ strictPrimitivePrimes d then Nat.find h.2 else 0

open Classical in
/-- `l_p = 0` for `p ∉ S(d)` (in particular for every non-prime `p`).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_of_not_mem {d : ℤ} {p : ℕ} (hp : p ∉ strictPrimitivePrimes d) :
    strictPrimitiveExponent d p = 0 := by
  simp [strictPrimitiveExponent, hp]

open Classical in
/-- For `p ∈ S(d)`, `l_p > 0` and `|x² - d y²| = p^{l_p}` has a strictly primitive integral
solution.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_spec {d : ℤ} {p : ℕ} (hp : p ∈ strictPrimitivePrimes d) :
    0 < strictPrimitiveExponent d p ∧ ∃ x y : ℤ, IsCoprime x (d * y) ∧
      |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ strictPrimitiveExponent d p := by
  have hl : strictPrimitiveExponent d p = Nat.find hp.2 := by simp [strictPrimitiveExponent, hp]
  rw [hl]
  exact Nat.find_spec hp.2

open Classical in
/-- Minimality of `l_p`: for `p ∈ S(d)`, every exponent `l > 0` for which `|x² - d y²| = p^l`
has a strictly primitive integral solution satisfies `l_p ≤ l`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_le {d : ℤ} {p l : ℕ} (hp : p ∈ strictPrimitivePrimes d)
    (hl : 0 < l) (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ |x ^ 2 - d * y ^ 2| = (p : ℤ) ^ l) :
    strictPrimitiveExponent d p ≤ l := by
  have he : strictPrimitiveExponent d p = Nat.find hp.2 := by simp [strictPrimitiveExponent, hp]
  rw [he]
  exact Nat.find_min' hp.2 ⟨hl, h⟩

/-- `7 ∈ S(2)`, witnessed by `3² - 2 · 1² = 7`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-thm-8`). -/
theorem seven_mem_strictPrimitivePrimes_two : 7 ∈ strictPrimitivePrimes 2 :=
  ⟨by decide, 1, by norm_num, 3, 1, ⟨1, -1, by norm_num⟩, by norm_num⟩

open Classical in
/-- `l_7 = 1` for `d = 2`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Notation 2
(`integers-2024-A111-cor-1`). -/
theorem strictPrimitiveExponent_two_seven : strictPrimitiveExponent 2 7 = 1 := by
  have hp := seven_mem_strictPrimitivePrimes_two
  have hl : strictPrimitiveExponent 2 7 = Nat.find hp.2 := by
    simp only [strictPrimitiveExponent, hp, dite_true]
  rw [hl]
  have h1 := (Nat.find_spec hp.2).1
  have h2 : Nat.find hp.2 ≤ 1 :=
    Nat.find_min' hp.2 ⟨Nat.one_pos, 3, 1, ⟨1, -1, by norm_num⟩, by norm_num⟩
  omega

/-- Rational solutions of (1) for `d = 1`: if `(a, b, c)` is a rational solution of
`(a - c)² (b² + 1) = (b - c)² (a² + 1)` with `|a| ≠ |b|`, and `a`, `b` are `x`-components of
rational solutions of `x² - y² = -1`, then for some integers `l, m, n` with `|l| ≠ |m|`,
`l m ≠ n²`, `l m n ≠ 0`: `a = (l² - n²) / (2 l n)`, `b = (m² - n²) / (2 m n)` and
`c = (l m - n²) / ((l + m) n)` or `c = -((l + m) n) / (l m - n²)` (2).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(i)
(`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_rat_solution_pythagorean (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - b₂ ^ 2 = -1) :
    ∃ l m n : ℤ, |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      (c = ((l : ℚ) * m - n ^ 2) / ((l + m) * n) ∨ c = -(((l : ℚ) + m) * n) / (l * m - n ^ 2))

/-- Converse of Theorem 1(i): for integers `l, m, n` with `|l| ≠ |m|`, `l m ≠ n²`, `l m n ≠ 0`,
both triples of Form (2) solve `(a - c)² (b² + 1) = (b - c)² (a² + 1)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (2) (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_form_two (l m n : ℤ) (hlm : |l| ≠ |m|)
    (hn2 : l * m ≠ n ^ 2) (h0 : l * m * n ≠ 0) :
    let a : ℚ := ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n)
    let b : ℚ := ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n)
    ∀ c ∈ ({((l : ℚ) * m - n ^ 2) / ((l + m) * n), -(((l : ℚ) + m) * n) / (l * m - n ^ 2)} :
        Set ℚ), (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)

/-- Rational solutions of (1) for square-free `d > 1`, Form (3): if `(a, b, c)` is a rational
solution of `(a - c)² (b² + 1) = (b - c)² (a² + 1)` with `|a| ≠ |b|`, and `a`, `b` are
`x`-components of rational solutions of `x² - d y² = -1`, then there are `α = a + a₂ √d` and
`β = b + b₂ √d` of norm `-1` with `c = ± ((αβ - (αβ)') / (α + β - (α + β)'))^{±1}`, i.e.
`c = (a b₂ + a₂ b) / (a₂ + b₂)` or `c = -(a₂ + b₂) / (a b₂ + a₂ b)`.

`α, β` are written through their rational coordinates; `β ≠ ±α` follows from `|a| ≠ |b|`. The
theorem's second part (the factorization of `α, β` through `η`, `ξ_p` and `S(d)`) is not
formalized.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1(ii), first
sentence (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_rat_solution_negPell (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (a b c : ℚ) (hab : |a| ≠ |b|)
    (h : (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))
    (ha : ∃ a₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1) (hb : ∃ b₂ : ℚ, b ^ 2 - d * b₂ ^ 2 = -1) :
    ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧ b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((a₂ + b₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (a₂ + b₂)) ∨
        (a * b₂ + a₂ * b ≠ 0 ∧ c = -(a₂ + b₂) / (a * b₂ + a₂ * b)))

/-- Converse of Theorem 1(ii) for Form (3): if `a² - d a₂² = b² - d b₂² = -1`, then
`c = (a b₂ + a₂ b) / (a₂ + b₂)` (when `a₂ + b₂ ≠ 0`) and `c = -(a₂ + b₂) / (a b₂ + a₂ b)` (when
`a b₂ + a₂ b ≠ 0`) solve `(a - c)² (b² + 1) = (b - c)² (a² + 1)`.

The nonvanishing hypotheses make the quotients in (3) defined.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 1, converse
for (3) (`integers-2024-A111-thm-1`). -/
public theorem_wanted bisector_equation_form_three (d : ℤ) (a a₂ b b₂ : ℚ)
    (ha : a ^ 2 - d * a₂ ^ 2 = -1) (hb : b ^ 2 - d * b₂ ^ 2 = -1) :
    (a₂ + b₂ ≠ 0 → let c := (a * b₂ + a₂ * b) / (a₂ + b₂)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1)) ∧
    (a * b₂ + a₂ * b ≠ 0 → let c := -(a₂ + b₂) / (a * b₂ + a₂ * b)
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1))

/-- Products of strictly primitive solutions: for distinct primes `p_i` and `n_i ∈ ℕ`, if
`a_i ∈ ℤ[√d]` has `|N(a_i)| = p_i^{n_i}` with `re a_i` and `d · im a_i` coprime, then
`∏ a_i` is a strictly primitive solution of `|x² - d y²| = ∏ p_i^{n_i}` (13).

The sign `±` in (13) is dropped; negation preserves both conclusions.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(a)
(`integers-2024-A111-prop-3`). -/
public theorem_wanted strictlyPrimitive_prod (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) {r : ℕ}
    (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (n : Fin r → ℕ)
    (a : Fin r → ℤ√d) (ha : ∀ i, IsCoprime (a i).re (d * (a i).im))
    (hN : ∀ i, |(a i).norm| = (p i : ℤ) ^ n i) :
    IsCoprime (∏ i, a i).re (d * (∏ i, a i).im) ∧ |(∏ i, a i).norm| = ∏ i, (p i : ℤ) ^ n i

/-- Powers of strictly primitive solutions: for an odd prime `p` and `m, n > 0`, if
`a ∈ ℤ[√d]` has `|N(a)| = p^m` with `re a` and `d · im a` coprime, then `a^n` is a strictly
primitive solution of `|x² - d y²| = p^{m n}` (14).

Deviation: `p ≠ 2` is added. For `p = 2` the statement is false as printed: `d = 3`,
`a = 1 + √3` (`N(a) = -2`), `n = 2` gives `a² = 4 + 2√3` with `gcd(4, 6) = 2`. The sign `±` in
(14) is dropped.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(b)
(`integers-2024-A111-prop-3`). -/
public theorem_wanted strictlyPrimitive_pow (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (a : ℤ√d)
    (ha : IsCoprime a.re (d * a.im)) (hN : |a.norm| = (p : ℤ) ^ m) :
    IsCoprime (a ^ n).re (d * (a ^ n).im) ∧ |(a ^ n).norm| = (p : ℤ) ^ (m * n)

/-- If `x² - d y² = -1` is solvable in integers and `x² - d y² = z ≠ 0` has a strictly primitive
integral solution (`x` and `d y` coprime), then so does `x² - d y² = -z`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 4
(`integers-2024-A111-prop-4`). -/
public theorem_wanted strictlyPrimitive_neg (d : ℤ) (hd : 1 < d) (hsq : Squarefree d) (z : ℤ)
    (hz : z ≠ 0) (hneg : ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1)
    (h : ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = z) :
    ∃ x y : ℤ, IsCoprime x (d * y) ∧ x ^ 2 - d * y ^ 2 = -z

/-- For a prime `p`, `|x² - d y²| = z` has a strictly primitive integral solution for some
multiple `z` of `p` if and only if `p` splits in `ℚ(√d)`, i.e. `(p)` has exactly two prime
ideals above it in the ring of integers of `K = ℚ(√d)`.

`K` is any number field of degree `2` containing a square root `s` of `d`. Deviation: the source
assumes only `d ≢ 5 (mod 8)` or `p ≠ 2`; here `p = 2` additionally requires `d ≡ 1 (mod 8)` or
`d ≡ 2 (mod 4)`. For `d ≡ 3 (mod 4)` and `p = 2` the statement is false as printed: `d = 3`,
`(x, y) = (1, 1)` gives `|1 - 3| = 2` with `gcd(1, 3) = 1`, while `2` ramifies in `ℚ(√3)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 7
(`integers-2024-A111-thm-7`). -/
public theorem_wanted exists_strictlyPrimitive_dvd_iff_split (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (s : K) (hs : s ^ 2 = d) (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2 ∨ d % 8 = 1 ∨ d % 4 = 2) :
    (∃ x y : ℤ, IsCoprime x (d * y) ∧ (p : ℤ) ∣ x ^ 2 - d * y ^ 2) ↔
      ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2

/-- If `d ≡ 1 (mod 8)`, or `d ≡ 5 (mod 8)` and the fundamental unit `η` of `ℚ(√d)` lies in
`ℤ[√d]`, or `d ≡ 2 (mod 4)`, then `S(d)` is the set of primes that split in `ℚ(√d)`.

`η ∈ ℤ[√d]` is stated as: every unit of the ring of integers lies in `ℤ[s]` (equivalent, since
the units are `±η^n`). Deviation: the source also lists `d ≡ 3 (mod 4)`, where the statement is
false as printed: `2 ∈ S(3)` by `|1² - 3 · 1²| = 2`, but `2` ramifies in `ℚ(√3)`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 8(a)
(`integers-2024-A111-thm-8`). -/
public theorem_wanted strictPrimitivePrimes_eq_split (d : ℤ) (hd : 1 < d) (hsq : Squarefree d)
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (s : K) (hs : s ^ 2 = d)
    (hcase : d % 8 = 1 ∨ (d % 8 = 5 ∧ ∀ u : (NumberField.RingOfIntegers K)ˣ,
      ((u : NumberField.RingOfIntegers K) : K) ∈ Algebra.adjoin ℤ {s}) ∨ d % 4 = 2) :
    strictPrimitivePrimes d =
      {p : ℕ | p.Prime ∧ ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

/-- If `d ≡ 5 (mod 8)` and the fundamental unit `η` of `ℚ(√d)` does not lie in `ℤ[√d]`, then
`S(d)` consists of `2` and the primes that split in `ℚ(√d)`.

`η ∉ ℤ[√d]` is stated as: some unit of the ring of integers lies outside `ℤ[s]`.

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 8(b)
(`integers-2024-A111-thm-8`). -/
public theorem_wanted strictPrimitivePrimes_eq_split_insert_two (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (s : K) (hs : s ^ 2 = d) (h5 : d % 8 = 5)
    (hη : ∃ u : (NumberField.RingOfIntegers K)ˣ,
      ((u : NumberField.RingOfIntegers K) : K) ∉ Algebra.adjoin ℤ {s}) :
    strictPrimitivePrimes d = insert 2
      {p : ℕ | p.Prime ∧ ((Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K)).ncard = 2}

/-- For `p ∈ S(d)`, `l_p` is at most the class number of `ℚ(√d)`.

Deviation: stated for `d ≡ 2, 3 (mod 4)`; the source excludes only `d ≡ 1 (mod 4)` with `p = 2`.
For `d ≡ 5 (mod 8)` it is false as printed: `ℚ(√37)` has class number `1`, but `l_3 = 3` for
`d = 37` (`8² - 37 · 1² = 27`; `|x² - 37 y²| = 3` and `= 9` have no strictly primitive solutions,
since the elements of norm `±3` and `±9` generating primitive ideals are `(5 ± √37) / 2` and
`(31 ± 5√37) / 2` times units, and all units lie in `ℤ[√37]`).

Source: Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with
Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 1
(`integers-2024-A111-cor-1`). -/
public theorem_wanted strictPrimitiveExponent_le_classNumber (d : ℤ) (hd : 1 < d)
    (hsq : Squarefree d) (hd4 : d % 4 = 2 ∨ d % 4 = 3) (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (s : K) (hs : s ^ 2 = d) (p : ℕ)
    (hp : p ∈ strictPrimitivePrimes d) :
    strictPrimitiveExponent d p ≤ NumberField.classNumber K

end

end MetaMathlibExt
