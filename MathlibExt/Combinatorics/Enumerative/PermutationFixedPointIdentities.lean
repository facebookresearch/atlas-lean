/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Pochhammer
import MathlibExt.LinearAlgebra.Matrix.DeterminantLemma

/-!
# Signed fixed-point identities for permutations

Pain's falling-factorial identity follows by differentiating the signed fixed-point
generating polynomial, expressed as a determinant. Pain's factorial-ratio identity follows by
applying to the same polynomial the linear functional sending `X ^ m` to `m! / (m + k)!`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted

open Polynomial

/-- The Leibniz expansion counts fixed points, while the all-ones matrix gives
a rank-one update of the scalar matrix with diagonal entry `X - 1`. -/
private theorem signed_fixedPoint_polynomial (n : ℕ) :
    (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ[X]) * X ^ Fintype.card (Function.fixedPoints σ)) =
      (X - C 1) ^ n + (n : ℝ[X]) * (X - C 1) ^ (n - 1) := by
  let u : Fin n → ℝ[X] := fun _ => 1
  let A : Matrix (Fin n) (Fin n) ℝ[X] := (X - C 1 : ℝ[X]) • 1
  calc
    _ = (A + Matrix.vecMulVec u u).det := by
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => congrArg (_ * ·) ?_
      have hEntry (i : Fin n) :
          (A + Matrix.vecMulVec u u) (σ i) i = if σ i = i then X else 1 := by
        by_cases h : σ i = i <;> simp [A, u, Matrix.vecMulVec_apply, h]
      simp_rw [hEntry]
      rw [← Finset.prod_filter, Finset.prod_const]
      congr 1
      exact Fintype.card_subtype (fun i => σ i = i)
    _ = _ := by
      simp [A, u, Matrix.det_add_vecMulVec, Matrix.adjugate_smul,
        Matrix.smul_mulVec, dotProduct, nsmul_eq_mul]

-- The polynomial argument also applies at order zero. Keep the stated positive-order hypothesis.
set_option linter.unusedVariables false in
/-- **Pain's signed falling-factorial identity for fixed points.** Let $n$ and $k$ be natural
numbers with $n \ge 2$, $k \ge 1$ and $k + 1 \le n$, and let $x$ be a real number. For a
permutation $\sigma$ of $\lbrace 0, 1, \dots, n-1 \rbrace$, write $\operatorname{sgn}(\sigma)$ for
its sign and $\operatorname{fix}(\sigma)$ for its number of fixed points, and for a natural number
$m$ write $(m)_k = m(m-1)\cdots(m-k+1)$ for the falling factorial. Then, summing over all
permutations $\sigma$ of this set,
$$\sum_{\sigma} \operatorname{sgn}(\sigma) (\operatorname{fix}(\sigma))_k
x^{\operatorname{fix}(\sigma) - k} = \frac{n!}{(n-k)!} (x-1)^{n-k-1} (x + n - k - 1),$$
where a term with $\operatorname{fix}(\sigma) < k$ is $0$ because then
$(\operatorname{fix}(\sigma))_k = 0$.

The left side is the $k$-th derivative in $x$ of
$\sum_{\sigma} \operatorname{sgn}(\sigma) x^{\operatorname{fix}(\sigma)}$.

Source: Jean-Christophe Pain, "Identities for Permutations with Fixed
Points", Theorem 2. -/
theorem sum_perm_sign_falling_fixedPoints_mul_pow
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (x : ℝ) :
    (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (∏ j ∈ Finset.range k,
          ((Fintype.card (Function.fixedPoints σ) : ℝ) - j)) *
        x ^ (Fintype.card (Function.fixedPoints σ) - k)) =
      (x - 1) ^ (n - k - 1) *
        (Nat.factorial n : ℝ) * (x + n - k - 1) /
          (Nat.factorial (n - k) : ℝ) := by
  -- Differentiate the determinant identity term by term and evaluate at x.
  have hpoly := congrArg (fun p : ℝ[X] => (derivative^[k] p).eval x)
    (signed_fixedPoint_polynomial n)
  simp only [iterate_derivative_sum, iterate_derivative_intCast_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_finsetSum, eval_mul, eval_intCast, eval_C,
    eval_pow, eval_X, iterate_map_add, iterate_derivative_natCast_mul,
    iterate_derivative_X_sub_pow, eval_add, eval_natCast, eval_sub, nsmul_eq_mul] at hpoly
  simp_rw [← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    mul_assoc]
  rw [hpoly]
  have hdesc : ((n - k : ℕ) : ℝ) * n.descFactorial k =
      (n : ℝ) * (n - 1).descFactorial k := by
    have h := Nat.succ_descFactorial (n - 1) k
    rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at h
    exact_mod_cast h
  have hpow : (x - 1) ^ (n - k) = (x - 1) ^ (n - k - 1) * (x - 1) := by
    rw [← pow_succ, show n - k - 1 + 1 = n - k by omega]
  rw [show n - 1 - k = n - k - 1 by omega, hpow, ← mul_assoc (n : ℝ), ← hdesc,
    Nat.cast_sub (show k ≤ n by omega), ← Nat.factorial_mul_descFactorial (show k ≤ n by omega),
    Nat.cast_mul]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) : (_ : ℝ) ≠ 0)).2
  ring

/-- The linear functional on real polynomials sending `X ^ m` to `m! / (m + k)!`, that is, the
value at `1` of the `k`-fold iterated integral of `p` from `0`, which Pain's proof computes. The
proofs below use only its recursion in `k`. -/
private noncomputable def factorialRatio (k : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  lsum fun m => ((Nat.factorial m : ℝ) / (Nat.factorial (m + k) : ℝ)) • LinearMap.id

private theorem factorialRatio_monomial (k m : ℕ) (a : ℝ) :
    factorialRatio k (monomial m a) =
      (Nat.factorial m : ℝ) / (Nat.factorial (m + k) : ℝ) * a := by
  simp [factorialRatio]

private theorem factorialRatio_X_pow (k m : ℕ) :
    factorialRatio k (X ^ m) = (Nat.factorial m : ℝ) / (Nat.factorial (m + k) : ℝ) := by
  rw [X_pow_eq_monomial, factorialRatio_monomial, mul_one]

/-- Multiplication by `X` lowers the value by `k` times the functional of order `k + 1`,
since `(m + 1)! / (m + k + 1)! = m! / (m + k)! - k * m! / (m + k + 1)!`. -/
private theorem factorialRatio_X_mul (k : ℕ) (p : ℝ[X]) :
    factorialRatio k (X * p) = factorialRatio k p - k * factorialRatio (k + 1) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]; ring
  | monomial m a =>
    rw [X_mul_monomial, factorialRatio_monomial, factorialRatio_monomial,
      factorialRatio_monomial, show m + 1 + k = m + k + 1 by omega,
      show m + (k + 1) = m + k + 1 by omega, Nat.factorial_succ m, Nat.factorial_succ (m + k)]
    have h1 : (Nat.factorial m : ℝ) ≠ 0 := by positivity
    have h2 : (Nat.factorial (m + k) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The functional of order `k + 1` on the powers of `X - 1`. -/
private theorem factorialRatio_X_sub_one_pow (k j : ℕ) :
    factorialRatio (k + 1) ((X - C 1) ^ j) =
      (-1 : ℝ) ^ j / ((Nat.factorial k : ℝ) * ((k : ℝ) + 1 + j)) := by
  induction j generalizing k with
  | zero =>
    rw [pow_zero, ← pow_zero (X : ℝ[X]), factorialRatio_X_pow, Nat.factorial_zero,
      zero_add, Nat.factorial_succ]
    push_cast
    have h : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ j ih =>
    rw [pow_succ', sub_mul, map_sub, factorialRatio_X_mul, C_mul', map_smul, smul_eq_mul,
      one_mul, sub_sub_cancel_left, ih (k + 1), Nat.factorial_succ]
    push_cast
    have h : (Nat.factorial k : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- **Pain's signed factorial-ratio identity for fixed points.** Let $n$ and $k$ be natural
numbers with $n \ge 2$ and $k \ge 1$. For a permutation $\sigma$ of
$\lbrace 0, 1, \dots, n-1 \rbrace$, write $\operatorname{sgn}(\sigma)$ for its sign and
$\operatorname{fix}(\sigma)$ for its number of fixed points. Then, summing over all permutations
$\sigma$ of this set,
$$\sum_{\sigma} \operatorname{sgn}(\sigma)
\frac{\operatorname{fix}(\sigma)!}{(\operatorname{fix}(\sigma) + k)!} =
\frac{(-1)^{n+1} \left(n^2 + (k-1)n - (k-1)\right)}{(k-1)! (n+k-1)(n+k)}.$$

Source: Jean-Christophe Pain, "Identities for Permutations with Fixed
Points", Theorem 3. -/
theorem sum_perm_sign_factorial_fixedPoints_div
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((Nat.factorial (Fintype.card (Function.fixedPoints σ)) : ℝ) /
          (Nat.factorial (Fintype.card (Function.fixedPoints σ) + k) : ℝ))) =
      (-1 : ℝ) ^ (n + 1) *
        ((n : ℝ) ^ 2 + ((k : ℝ) - 1) * n - ((k : ℝ) - 1)) /
          ((Nat.factorial (k - 1) : ℝ) * ((n : ℝ) + k - 1) *
            ((n : ℝ) + k)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ n by omega)
  -- Apply the functional to the signed fixed-point polynomial `(X - 1) ^ n + n (X - 1) ^ (n - 1)`.
  have hpoly := congrArg (factorialRatio (k + 1)) (signed_fixedPoint_polynomial (n + 1))
  simp only [map_sum, map_add, ← C_eq_intCast, ← C_eq_natCast, C_mul', map_smul, smul_eq_mul,
    factorialRatio_X_pow, factorialRatio_X_sub_one_pow, Nat.add_sub_cancel] at hpoly
  rw [hpoly, Nat.add_sub_cancel]
  have h : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have h1 : (k : ℝ) + 1 + n ≠ 0 := by positivity
  have h2 : (k : ℝ) + 1 + (n + 1) ≠ 0 := by positivity
  have h3 : ((n + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) - 1 = k + 1 + n := by push_cast; ring
  have h4 : ((n + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) = k + 1 + (n + 1) := by push_cast; ring
  rw [h3, h4]
  push_cast
  field_simp
  ring

end MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted
