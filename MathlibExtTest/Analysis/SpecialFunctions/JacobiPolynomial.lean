/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.JacobiPolynomial

/-! Tests for shifted Jacobi and Gegenbauer polynomials: every public statement restated,
plus concrete evaluations of the definitions. -/

namespace MathlibExtTest.Analysis.SpecialFunctions.JacobiPolynomial

open _root_.Polynomial

open Real MeasureTheory


/-- **Sturm–Liouville equation.** For `a > 0`,
`x (1 - x) R'' + (a - (a + b) x) R' = -n (n + a + b - 1) R` (as polynomials). -/
example {a : ℝ} (ha : 0 < a) (b : ℝ) (n : ℕ) :
    X * (1 - X) * derivative (derivative (shiftedJacobi a b n)) +
        (C a - C (a + b) * X) * derivative (shiftedJacobi a b n) =
      -C ((n : ℝ) * (n + a + b - 1)) * shiftedJacobi a b n := by
  apply _root_.Polynomial.shiftedJacobi_ode <;> assumption

/-- For `a, b > 0` every polynomial is integrable against the weight `x^(a-1) (1-x)^(b-1)` on
`[0, 1]`, so the orthogonality and norm integrals below are genuine (not Lean's junk `0`). -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℝ[X]) :
    IntervalIntegrable (fun x => p.eval x * (x ^ (a - 1) * (1 - x) ^ (b - 1))) volume 0 1 := by
  apply _root_.Polynomial.intervalIntegrable_eval_mul_weight <;> assumption

/-- **Orthogonality.** For `a, b > 0` and `m ≠ n`,
`∫₀¹ R_m(x) R_n(x) x^(a-1) (1-x)^(b-1) dx = 0`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b m).eval x * (shiftedJacobi a b n).eval x *
      (x ^ (a - 1) * (1 - x) ^ (b - 1)) = 0 := by
  apply _root_.Polynomial.integral_shiftedJacobi_mul_shiftedJacobi <;> assumption

/-- **Norm, `n = 0`.** `R_0 = 1` and `∫₀¹ x^(a-1) (1-x)^(b-1) dx = Γ(a) Γ(b) / Γ(a + b)`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b 0).eval x ^ 2 * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Gamma a * Gamma b / Gamma (a + b) := by
  apply _root_.Polynomial.integral_shiftedJacobi_zero_sq <;> assumption

/-- **Norms, `n ≥ 1`.** For `a, b > 0`,
`∫₀¹ R_n(x)² x^(a-1) (1-x)^(b-1) dx = n! Γ(a)² Γ(n+b) / (Γ(n+a) (2n+a+b-1) Γ(n+a+b-1))`. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1, (shiftedJacobi a b n).eval x ^ 2 * (x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      (n.factorial : ℝ) * Gamma a ^ 2 * Gamma (n + b) /
        (Gamma (n + a) * (2 * n + a + b - 1) * Gamma (n + a + b - 1)) := by
  apply _root_.Polynomial.integral_shiftedJacobi_sq <;> assumption

/-- **Shifted Legendre case.** `R_n^{(1,1)}` is Mathlib's `shiftedLegendre n` (normalization
constant `1`). -/
example (n : ℕ) :
    shiftedJacobi 1 1 n = (shiftedLegendre n).map (Int.castRingHom ℝ) := by
  apply _root_.Polynomial.shiftedJacobi_one_one <;> assumption

/-- **First polynomial.** `R_1^{(a,b)} = 1 - ((a + b) / a) X`; with `shiftedJacobi_ode` its
eigenvalue is `1 · (1 + a + b - 1) = a + b`. -/
example (a b : ℝ) : shiftedJacobi a b 1 = 1 - C ((a + b) / a) * X := by
  apply _root_.Polynomial.shiftedJacobi_one <;> assumption

/-- **Gegenbauer case.** `C_n^{(3/2)}(1 - 2x) = C(n + 2, 2) · R_n^{(2,2)}(x)`. -/
example (n : ℕ) :
    (gegenbauer (3 / 2) n).comp (1 - C 2 * X) =
      C (((n + 2).choose 2 : ℕ) : ℝ) * shiftedJacobi 2 2 n := by
  apply _root_.Polynomial.gegenbauer_three_halves_comp <;> assumption

/-- `R_0 = 1` by the defining sum. -/
example (a b : ℝ) : shiftedJacobi a b 0 = 1 := by simp [shiftedJacobi]

/-- The normalization `R_n(0) = 1`. -/
example (a b : ℝ) (n : ℕ) : (shiftedJacobi a b n).eval 0 = 1 := by
  rw [shiftedJacobi, eval_finsetSum]
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro k _ hk
    simp [hk]
  · simp
  · simp

/-- The first Gegenbauer polynomials from the recurrence, evaluated:
`C_2^{(ν)}(x) = 2ν(ν + 1)x² - ν`. -/
example (ν x : ℝ) : (gegenbauer ν 0).eval x = 1 ∧ (gegenbauer ν 1).eval x = 2 * ν * x ∧
    (gegenbauer ν 2).eval x = 2 * ν * (ν + 1) * x ^ 2 - ν := by
  refine ⟨by simp, by simp [gegenbauer_one], ?_⟩
  rw [show (2 : ℕ) = 0 + 2 from rfl, gegenbauer_two_add]
  simp
  ring

/-- At the singular parameter `a = 0` the totalized formula gives `R_1 = 1` (the
`k = 1` term has denominator `(0)_1 = 0`). -/
example (b : ℝ) : shiftedJacobi 0 b 1 = 1 := by
  simp [shiftedJacobi, Finset.sum_range_succ]

/-- `R_2^{(1,1)} = 1 - 6x + 6x²`, the shifted Legendre polynomial `P_2(1 - 2x)`. -/
example : shiftedJacobi 1 1 2 = 1 - 6 * X + 6 * X ^ 2 := by
  rw [shiftedJacobi_one_one]
  have hc : Nat.choose 4 2 = 6 := rfl
  norm_num [shiftedLegendre, Finset.sum_range_succ, hc]
  ring_nf

end MathlibExtTest.Analysis.SpecialFunctions.JacobiPolynomial
