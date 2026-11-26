/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
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
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler polynomials at `(x + 1)/2` via generalized Stirling polynomials

`eulerPoly_half_eq_sum` expresses the scaled Euler polynomial `2^n E_n((x + 1)/2)` as a
finite sum of generalized Stirling polynomials `genStirlingPoly n k`, weighted by factorials
and the Taylor coefficients `eulerAlpha` of `(2 + 2z)/(2 + 2z + z^2)`. The proof applies the
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

/-- **Generalized Stirling polynomial.** For natural numbers $n$ and $k$, the generalized
Stirling polynomial $S(n, k, x)$ is the polynomial in $x$ with rational coefficients
$$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n.$$

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Proposition 3.1 (definition). -/
noncomputable def genStirlingPoly (n k : ℕ) : ℚ[X] :=
  (1 / (Nat.factorial k : ℚ)) •
    ∑ j ∈ Finset.range (k + 1),
      ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) •
        (X + C (j : ℚ)) ^ n

/-- **Taylor coefficients of (2 + 2z)/(2 + 2z + z²).** The rational numbers $\alpha_k$,
$k \ge 0$, are defined by $\alpha_0 = 1$, $\alpha_1 = 0$ and
$2\alpha_{k+2} + 2\alpha_{k+1} + \alpha_k = 0$ for every $k \ge 0$. They are the Taylor
coefficients of $(2 + 2z)/(2 + 2z + z^2)$ at $z = 0$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Lemma 2.2 (generating function). -/
def eulerAlpha : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | k + 2 => -eulerAlpha (k + 1) - eulerAlpha k / 2

-- equation lemmas for eulerAlpha
private theorem eulerAlpha_zero : eulerAlpha 0 = 1 := rfl

private theorem eulerAlpha_one : eulerAlpha 1 = 0 := rfl

private theorem eulerAlpha_succ_succ (k : ℕ) :
    eulerAlpha (k + 2) = -eulerAlpha (k + 1) - eulerAlpha k / 2 := rfl

private theorem eulerAlpha_rec (k : ℕ) :
    2 * eulerAlpha (k + 2) + 2 * eulerAlpha (k + 1) + eulerAlpha k = 0 := by
  rw [eulerAlpha_succ_succ]
  ring

/-- The average of the Euler polynomial at adjacent arguments recovers the monomial. -/
private theorem eulerPoly_shift (n : ℕ) :
    taylor 1 (eulerPoly n) + eulerPoly n = (2 : ℚ) • X ^ n := by
  apply Polynomial.funext
  intro x
  have dup := bernoulliFun_mul (n + 1) (m := 2) (by decide) ((x : ℝ) / 2)
  have cast_eval (y : ℚ) : bernoulliFun (n + 1) (y : ℝ) =
      ((Polynomial.bernoulli (n + 1)).eval y : ℚ) := by
    exact Polynomial.eval_map_apply (algebraMap ℚ ℝ) y
  norm_num [sum_range_succ] at dup
  rw [show 2 * ((x : ℝ) / 2) = x by ring,
    show (x : ℝ) / 2 + 1 / 2 = ((x + 1 : ℚ) / 2 : ℚ) by push_cast; ring,
    show (x : ℝ) / 2 = ((x / 2 : ℚ) : ℝ) by push_cast; rfl,
    cast_eval, cast_eval, cast_eval] at dup
  have hd : (Polynomial.bernoulli (n + 1)).eval x =
      2 ^ n * ((Polynomial.bernoulli (n + 1)).eval (x / 2) +
        (Polynomial.bernoulli (n + 1)).eval ((x + 1) / 2)) := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [pow_succ] at dup
    linarith
  have step := Polynomial.bernoulli_eval_one_add (n + 1) x
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at step
  rw [add_comm 1 x] at step
  simp only [eval_add, taylor_eval, eulerPoly, eval_smul, eval_sub, eval_comp, eval_mul,
    eval_C, eval_X, eval_pow, smul_eq_mul]
  simp only [one_div_mul_eq_div]
  field_simp
  rw [pow_succ]
  linear_combination step + 2 * hd

/-- The forward difference operator `Δ = T₁ - 1`. -/
private noncomputable def fwdDiff : Module.End ℚ ℚ[X] :=
  (taylor (1 : ℚ) : Module.End ℚ ℚ[X]) - 1

/-- The operator `L = T₂ + 1` annihilating the difference of the two sides. -/
private noncomputable def Lop : Module.End ℚ ℚ[X] :=
  (taylor (2 : ℚ) : Module.End ℚ ℚ[X]) + 1

private theorem taylor_one_pow (j : ℕ) (p : ℚ[X]) :
    ((taylor (1 : ℚ) : Module.End ℚ ℚ[X]) ^ j) p = taylor (j : ℚ) p := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, taylor_taylor, Nat.cast_add, Nat.cast_one]

private theorem neg_one_pow_apply (m : ℕ) (p : ℚ[X]) :
    ((-1 : Module.End ℚ ℚ[X]) ^ m) p = (-1 : ℚ) ^ m • p := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, pow_succ, ← smul_smul]
    congr 1
    simp

-- Evaluate the binomial theorem for commuting endomorphisms at a polynomial.
private theorem binomial_apply (a b : Module.End ℚ ℚ[X]) (hab : Commute a b)
    (k : ℕ) (p : ℚ[X]) :
    ((a + b) ^ k) p = ∑ j ∈ range (k + 1),
      (k.choose j : ℚ) • (a ^ j) ((b ^ (k - j)) p) := by
  rw [hab.add_pow]
  simp only [LinearMap.sum_apply, mul_apply_eq_comp, natCast_apply_eq_smul, map_nsmul,
    Nat.cast_smul_eq_nsmul]

private theorem fwdDiff_pow_X_pow (k n : ℕ) :
    (fwdDiff ^ k) (X ^ n) =
      ∑ j ∈ Finset.range (k + 1),
        ((Nat.choose k j : ℚ) * (-1) ^ (k - j)) • (X + C (j : ℚ)) ^ n := by
  have hcomm : Commute (taylor (1 : ℚ) : Module.End ℚ ℚ[X])
      (-1 : Module.End ℚ ℚ[X]) := by
    simp only [Commute, SemiconjBy]
    apply LinearMap.ext
    intro p
    simp [mul_apply_eq_comp, map_neg]
  have hdecomp : fwdDiff = (taylor (1 : ℚ) : Module.End ℚ ℚ[X]) + (-1) := by
    simp [fwdDiff, sub_eq_add_neg]
  rw [hdecomp, binomial_apply _ _ hcomm]
  apply sum_congr rfl
  intro j hj
  rw [taylor_one_pow, neg_one_pow_apply, map_smul, taylor_X_pow, ← smul_smul]

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

private theorem fwdDiff_degree_lt (p : ℚ[X]) (hp : p ≠ 0) :
    (fwdDiff p).degree < p.degree := by
  have hdeg : (taylor (1 : ℚ) p).degree = p.degree := degree_taylor p 1
  have h0 : taylor (1 : ℚ) p ≠ 0 := by
    intro h
    rw [h, degree_zero] at hdeg
    exact hp (Polynomial.degree_eq_bot.mp hdeg.symm)
  have hlt := degree_sub_lt_left hdeg h0 (leadingCoeff_taylor (1 : ℚ) p)
  rw [hdeg] at hlt
  simpa [fwdDiff] using hlt

private theorem natDegree_fwdDiff_pow (k n : ℕ) :
    ((fwdDiff ^ k) (X ^ n)).natDegree ≤ n - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (fwdDiff ^ (k + 1)) (X ^ n) = fwdDiff ((fwdDiff ^ k) (X ^ n)) := by
      rw [pow_succ', mul_apply_eq_comp]
    rw [hstep]
    by_cases hq : (fwdDiff ^ k) (X ^ n) = 0
    · rw [hq, map_zero, natDegree_zero]
      omega
    · have hlt := fwdDiff_degree_lt _ hq
      have hle : (fwdDiff ((fwdDiff ^ k) (X ^ n))).natDegree ≤
          ((fwdDiff ^ k) (X ^ n)).natDegree - 1 := by
        by_cases h0 : fwdDiff ((fwdDiff ^ k) (X ^ n)) = 0
        · rw [h0, natDegree_zero]
          omega
        · have hlt'' := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
            (hlt.trans_eq (Polynomial.degree_eq_natDegree hq))
          omega
      omega

private theorem fwdDiff_pow_succ_X_pow_eq_zero (n : ℕ) :
    (fwdDiff ^ (n + 1)) (X ^ n) = 0 := by
  have hstep : (fwdDiff ^ (n + 1)) (X ^ n) = fwdDiff ((fwdDiff ^ n) (X ^ n)) := by
    rw [pow_succ', mul_apply_eq_comp]
  rw [hstep]
  have hle := natDegree_fwdDiff_pow n n
  rw [Nat.sub_self] at hle
  have hC : (fwdDiff ^ n) (X ^ n) = C (((fwdDiff ^ n) (X ^ n)).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hle)
  rw [hC, fwdDiff_C]

private theorem fwdDiff_pow_succ_succ_X_pow_eq_zero (n : ℕ) :
    (fwdDiff ^ (n + 2)) (X ^ n) = 0 := by
  have h2 : n + 2 = (n + 1) + 1 := by omega
  rw [h2, pow_succ', mul_apply_eq_comp, fwdDiff_pow_succ_X_pow_eq_zero, map_zero]

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
    fwdDiff_pow_succ_X_pow_eq_zero (M + 1)
  have hvan2 : (fwdDiff ^ (M + 1 + 1 + 1)) (X ^ (M + 1)) = 0 := by
    rw [pow_succ', mul_apply_eq_comp, hvan1, map_zero]
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
