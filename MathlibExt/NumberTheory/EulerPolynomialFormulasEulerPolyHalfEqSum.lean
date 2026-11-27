/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
public import MathlibExt.NumberTheory.EulerPolynomialStirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler polynomials at `(x + 1)/2` via generalized Stirling polynomials

`eulerPoly_half_eq_sum` expresses the scaled Euler polynomial `2^n E_n((x + 1)/2)` as a
finite sum of generalized Stirling polynomials `genStirlingPoly n k`, weighted by factorials
and the Taylor coefficients `eulerAlpha` of `(2 + 2z)/(2 + 2z + z^2)`, both defined in
`MathlibExt.NumberTheory.EulerPolynomialStirling`. The proof applies the
operator `T₂ + 1` to both sides and telescopes the resulting sums with the recurrence
defining `eulerAlpha`.

Statements from Nouara Mokhtari, Rachid Boumahdi, and
Farid Bencherif, "Generalizations of Several Explicit
Formulas for Euler Polynomials", *INTEGERS* 25 (2025),
Article A65
(<https://math.colgate.edu/~integers/vol25.html>).
-/

set_option autoImplicit false

@[expose] public section

open Polynomial Finset

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- equation lemmas for eulerAlpha
private theorem eulerAlpha_zero : eulerAlpha 0 = 1 := rfl

private theorem eulerAlpha_one : eulerAlpha 1 = 0 := rfl

private theorem eulerAlpha_succ_succ (k : ℕ) :
    eulerAlpha (k + 2) = -eulerAlpha (k + 1) - eulerAlpha k / 2 := rfl

private theorem eulerAlpha_rec (k : ℕ) :
    2 * eulerAlpha (k + 2) + 2 * eulerAlpha (k + 1) + eulerAlpha k = 0 := by
  rw [eulerAlpha_succ_succ]
  ring

/-- The forward difference operator `Δ = T₁ - 1`. -/
private noncomputable def fwdDiff : Module.End ℚ ℚ[X] :=
  (taylor (1 : ℚ) : Module.End ℚ ℚ[X]) - 1

/-- The operator `L = T₂ + 1` annihilating the difference of the two sides. -/
private noncomputable def Lop : Module.End ℚ ℚ[X] :=
  (taylor (2 : ℚ) : Module.End ℚ ℚ[X]) + 1

/-- Evaluating an iterate of the polynomial forward difference at `x` gives Mathlib's iterated
forward difference, at step one, of the evaluation map of the polynomial at `x`. -/
private theorem eval_fwdDiff_pow (k : ℕ) (p : ℚ[X]) (x : ℚ) :
    ((fwdDiff ^ k) p).eval x = (_root_.fwdDiff (1 : ℚ))^[k] (fun y => p.eval y) x := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    have hstep : (fun y => (fwdDiff p).eval y) = _root_.fwdDiff (1 : ℚ) (fun y => p.eval y) := by
      funext y
      simp [fwdDiff, _root_.fwdDiff, taylor_eval]
    rw [pow_succ, mul_apply_eq_comp, ih, Function.iterate_succ_apply, hstep]

private theorem fwdDiff_pow_X_pow (k n : ℕ) :
    (fwdDiff ^ k) (X ^ n) =
      ∑ j ∈ Finset.range (k + 1),
        ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) • (X + C (j : ℚ)) ^ n := by
  apply Polynomial.funext
  intro x
  rw [eval_fwdDiff_pow, fwdDiff_iter_eq_sum_shift, eval_finsetSum]
  apply sum_congr rfl
  intro j _
  simp [zsmul_eq_mul, mul_comm]

private theorem genStirling_eq (n k : ℕ) :
    genStirlingPoly n k = (1 / (Nat.factorial k : ℚ)) • (fwdDiff ^ k) (X ^ n) := by
  simp only [genStirlingPoly, fwdDiff_pow_X_pow]

/-- The right-hand side in operator form. -/
private noncomputable def Rhs (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), (eulerAlpha k) • (fwdDiff ^ k) (X ^ n)

private theorem rhs_eq_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((Nat.factorial k : ℚ) * eulerAlpha k) •
      genStirlingPoly n k) = Rhs n := by
  unfold Rhs
  apply sum_congr rfl
  intro k _
  rw [genStirling_eq, smul_smul]
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hscalar : ((Nat.factorial k : ℚ) * eulerAlpha k) * (1 / (Nat.factorial k : ℚ)) =
      eulerAlpha k := by
    field
  rw [hscalar]

private theorem fwdDiff_C (a : ℚ) : fwdDiff (C a) = 0 := by
  apply Polynomial.funext
  intro x
  simp [fwdDiff]

private theorem fwdDiff_pow_X_pow_eq_zero_of_lt {m n : ℕ} (h : n < m) :
    (fwdDiff ^ m) (X ^ n) = 0 := by
  apply Polynomial.funext
  intro x
  rw [eval_fwdDiff_pow, eval_zero]
  simp only [eval_pow, eval_X]
  rw [fwdDiff_iter_pow_eq_zero_of_lt h, Pi.zero_apply]

private theorem fwdDiff_apply (q : ℚ[X]) : fwdDiff q = taylor (1 : ℚ) q - q := by
  simp [fwdDiff]

private theorem taylor_one_eq (q : ℚ[X]) : taylor (1 : ℚ) q = q + fwdDiff q := by
  rw [fwdDiff_apply]
  abel

private theorem fwdDiff_sq_apply (q : ℚ[X]) :
    (fwdDiff ^ 2) q = fwdDiff (fwdDiff q) := by
  rw [pow_two, mul_apply_eq_comp]

private theorem taylor_two_eq (q : ℚ[X]) :
    taylor (2 : ℚ) q = q + (2 : ℚ) • fwdDiff q + (fwdDiff ^ 2) q := by
  have h11 : taylor (1 : ℚ) (taylor (1 : ℚ) q) = taylor (2 : ℚ) q := by
    rw [taylor_taylor]
    congr 1
    norm_num
  have e1 := taylor_one_eq q
  have e2 := taylor_one_eq (fwdDiff q)
  rw [← h11, e1, map_add, e1, e2, ← fwdDiff_sq_apply, two_smul]
  abel

private theorem Lop_apply (p : ℚ[X]) : Lop p = taylor (2 : ℚ) p + p := by
  simp [Lop]

private theorem Lop_eq_zero (p : ℚ[X]) (h : Lop p = 0) : p = 0 := by
  by_contra hp
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hsum : (taylor (2 : ℚ) p).leadingCoeff + p.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_taylor]
    intro hz
    apply hlead
    linarith
  have hlc : (taylor (2 : ℚ) p + p).leadingCoeff =
      (taylor (2 : ℚ) p).leadingCoeff + p.leadingCoeff :=
    leadingCoeff_add_of_degree_eq (degree_taylor p 2) hsum
  rw [leadingCoeff_taylor] at hlc
  have h0 : (taylor (2 : ℚ) p + p).leadingCoeff = 0 := by
    have hLp : taylor (2 : ℚ) p + p = Lop p := (Lop_apply p).symm
    rw [hLp, h, leadingCoeff_zero]
  rw [h0] at hlc
  apply hlead
  linarith

private theorem telescope (f : ℕ → ℚ[X]) (M : ℕ) :
    (∑ k ∈ Finset.range (M + 1 + 1),
      (eulerAlpha k) • ((2 : ℚ) • f k + (2 : ℚ) • f (k + 1) + f (k + 1 + 1))) =
      (2 : ℚ) • f 0 + (2 : ℚ) • f 1 +
        (2 * eulerAlpha (M + 1) + eulerAlpha M) • f (M + 1 + 1) +
        (eulerAlpha (M + 1)) • f (M + 1 + 1 + 1) := by
  induction M with
  | zero =>
    simp [Finset.sum_range_succ, eulerAlpha_zero, eulerAlpha_one]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : 2 * eulerAlpha (M + 1 + 1) + 2 * eulerAlpha (M + 1) + eulerAlpha M = 0 := by
      have h2 : M + 1 + 1 = M + 2 := by omega
      rw [h2]
      exact eulerAlpha_rec M
    have hkey : (2 * eulerAlpha (M + 1) + eulerAlpha M) = -(2 * eulerAlpha (M + 1 + 1)) := by
      linarith [hrec]
    rw [hkey]
    module

private theorem fwdDiff_pow_succ_apply (k : ℕ) (p : ℚ[X]) :
    fwdDiff ((fwdDiff ^ k) p) = (fwdDiff ^ (k + 1)) p := by
  rw [pow_succ', mul_apply_eq_comp]

private theorem fwdDiff_sq_pow_apply (k : ℕ) (p : ℚ[X]) :
    (fwdDiff ^ 2) ((fwdDiff ^ k) p) = (fwdDiff ^ (k + 1 + 1)) p := by
  have hkk : fwdDiff ^ 2 * fwdDiff ^ k = fwdDiff ^ (k + 1 + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hkk, mul_apply_eq_comp]

private theorem Lop_fwdDiff_pow (k n : ℕ) :
    Lop ((fwdDiff ^ k) (X ^ n)) =
      (2 : ℚ) • (fwdDiff ^ k) (X ^ n) + (2 : ℚ) • (fwdDiff ^ (k + 1)) (X ^ n) +
        (fwdDiff ^ (k + 1 + 1)) (X ^ n) := by
  have hT := taylor_two_eq ((fwdDiff ^ k) (X ^ n))
  rw [Lop_apply, hT, ← fwdDiff_pow_succ_apply k (X ^ n), ← fwdDiff_sq_pow_apply k (X ^ n)]
  module

private theorem Lop_Rhs_succ (M : ℕ) :
    Lop (Rhs (M + 1)) = (2 : ℚ) • X ^ (M + 1) + (2 : ℚ) • fwdDiff (X ^ (M + 1)) := by
  have hR : Rhs (M + 1) =
      ∑ k ∈ Finset.range (M + 1 + 1), (eulerAlpha k) • (fwdDiff ^ k) (X ^ (M + 1)) := rfl
  rw [hR, map_sum]
  simp only [map_smul, Lop_fwdDiff_pow]
  have htel := telescope (fun j => (fwdDiff ^ j) (X ^ (M + 1))) M
  have htel2 : (∑ k ∈ Finset.range (M + 1 + 1), (eulerAlpha k) •
        ((2 : ℚ) • (fwdDiff ^ k) (X ^ (M + 1)) +
          (2 : ℚ) • (fwdDiff ^ (k + 1)) (X ^ (M + 1)) +
          (fwdDiff ^ (k + 1 + 1)) (X ^ (M + 1)))) =
      (2 : ℚ) • (fwdDiff ^ 0) (X ^ (M + 1)) + (2 : ℚ) • (fwdDiff ^ 1) (X ^ (M + 1)) +
        (2 * eulerAlpha (M + 1) + eulerAlpha M) • (fwdDiff ^ (M + 1 + 1)) (X ^ (M + 1)) +
        eulerAlpha (M + 1) • (fwdDiff ^ (M + 1 + 1 + 1)) (X ^ (M + 1)) := htel
  rw [htel2]
  have hvan1 : (fwdDiff ^ (M + 1 + 1)) (X ^ (M + 1)) = 0 :=
    fwdDiff_pow_X_pow_eq_zero_of_lt (by omega)
  have hvan2 : (fwdDiff ^ (M + 1 + 1 + 1)) (X ^ (M + 1)) = 0 :=
    fwdDiff_pow_X_pow_eq_zero_of_lt (by omega)
  rw [pow_zero, one_apply_eq_self, pow_one, hvan1, hvan2]
  simp

private theorem Lop_Rhs_zero :
    Lop (Rhs 0) = (2 : ℚ) • X ^ (0 : ℕ) + (2 : ℚ) • fwdDiff (X ^ (0 : ℕ)) := by
  have hR : Rhs 0 = 1 := by
    simp [Rhs, eulerAlpha_zero]
  have hL : Lop (Rhs 0) = (2 : ℚ) • (1 : ℚ[X]) := by
    rw [hR, Lop_apply, taylor_one, C_1, two_smul]
  rw [hL]
  simp only [pow_zero]
  have h1 : fwdDiff (1 : ℚ[X]) = 0 := by
    rw [← C_1, fwdDiff_C]
  rw [h1]
  simp

/-- The left-hand side in operator form. -/
private noncomputable def Lhs (n : ℕ) : ℚ[X] :=
  (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2 : ℚ) * (X + 1))

private theorem two_pow_mul_half_pow (n : ℕ) : (2 : ℚ) ^ n * (1 / 2) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

private theorem comp_X_pow (n : ℕ) :
    (X ^ n).comp (C (1 / 2 : ℚ) * (X + 1)) = (C (1 / 2 : ℚ) * (X + 1)) ^ n := by
  rw [pow_comp, X_comp]

private theorem comp_X_pow_smul (n : ℕ) :
    (2 : ℚ) ^ n • (X ^ n).comp (C (1 / 2 : ℚ) * (X + 1)) = (X + 1) ^ n := by
  rw [comp_X_pow, mul_pow, ← C_pow, C_mul', smul_smul, two_pow_mul_half_pow, one_smul]

private theorem comp_taylor_one (p : ℚ[X]) :
    (taylor (1 : ℚ) p).comp (C (1 / 2 : ℚ) * (X + 1)) =
      taylor (2 : ℚ) (p.comp (C (1 / 2 : ℚ) * (X + 1))) := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, taylor_eval]
  have hs : ∀ y : ℚ, (C (1 / 2) * (X + 1) : ℚ[X]).eval y = (y + 1) / 2 := by
    intro y
    rw [eval_mul, eval_C, eval_add, eval_X, eval_one]
    ring
  rw [hs, hs]
  congr 1
  ring

private theorem shift_comp (n : ℕ) :
    taylor (2 : ℚ) ((eulerPoly n).comp (C (1 / 2 : ℚ) * (X + 1))) +
        (eulerPoly n).comp (C (1 / 2 : ℚ) * (X + 1)) =
      (2 : ℚ) • (X ^ n).comp (C (1 / 2 : ℚ) * (X + 1)) := by
  have h := congrArg (fun p : ℚ[X] => p.comp (C (1 / 2 : ℚ) * (X + 1))) (eulerPoly_shift n)
  rw [add_comp, comp_taylor_one] at h
  have hsmul : ((2 : ℚ) • X ^ n).comp (C (1 / 2 : ℚ) * (X + 1)) =
      (2 : ℚ) • (X ^ n).comp (C (1 / 2 : ℚ) * (X + 1)) := by
    simp only [smul_eq_C_mul, mul_comp, C_comp]
  rw [hsmul] at h
  exact h

private theorem Lop_Lhs (n : ℕ) :
    Lop (Lhs n) = (2 : ℚ) • X ^ n + (2 : ℚ) • fwdDiff (X ^ n) := by
  have hsc := congrArg (fun p : ℚ[X] => (2 : ℚ) ^ n • p) (shift_comp n)
  rw [smul_add, ← map_smul] at hsc
  have hL : (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2 : ℚ) * (X + 1)) = Lhs n := rfl
  rw [hL, ← Lop_apply] at hsc
  rw [hsc, smul_smul, mul_comm ((2 : ℚ) ^ n) 2, ← smul_smul, comp_X_pow_smul]
  have hX1 : (X + 1 : ℚ[X]) ^ n = taylor (1 : ℚ) (X ^ n) := by
    rw [← C_1, ← taylor_X_pow]
  rw [hX1, taylor_one_eq, smul_add]

private theorem main_eq (n : ℕ) : Lhs n = Rhs n := by
  have hL := Lop_Lhs n
  have hR : Lop (Rhs n) = (2 : ℚ) • X ^ n + (2 : ℚ) • fwdDiff (X ^ n) := by
    cases n with
    | zero => exact Lop_Rhs_zero
    | succ M => exact Lop_Rhs_succ M
  have hsub : Lop (Lhs n - Rhs n) = 0 := by
    rw [map_sub, hL, hR, sub_self]
  have h0 := Lop_eq_zero _ hsub
  exact sub_eq_zero.mp h0

/-- **Euler polynomials at (x + 1)/2 via generalized Stirling polynomials.** Let $E_n(x)$ denote
the Euler polynomial, $\alpha_k$ the Taylor coefficients of $(2 + 2z)/(2 + 2z + z^2)$, and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every $n \ge 0$, as polynomials in $x$ with rational coefficients,
$2^n E_n\left(\frac{x + 1}{2}\right) = \sum_{k=0}^{n} k! \, \alpha_k \, S(n, k, x)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1. -/
public theorem eulerPoly_half_eq_sum (n : ℕ) :
    (2 : ℚ) ^ n • (eulerPoly n).comp (C (1 / 2) * (X + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.factorial k : ℚ) * eulerAlpha k) •
          genStirlingPoly n k := by
  rw [rhs_eq_sum]
  exact main_eq n

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
