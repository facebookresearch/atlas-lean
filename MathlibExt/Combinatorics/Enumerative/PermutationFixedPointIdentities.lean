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
generating polynomial, expressed as a determinant.
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

end MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted
