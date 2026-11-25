/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The Golden–Thompson inequality: commuting case and positivity of its right side

The Golden–Thompson inequality states that `tr e^{A + B} ≤ tr (e^A e^B)` for Hermitian matrices
`A` and `B` (S. Golden, *Lower bounds for the Helmholtz function*, Phys. Rev. 137 (1965) B1127;
C. J. Thompson, *Inequality with applications in statistical mechanics*, J. Math. Phys. 6 (1965)
1812; see P. J. Forrester and C. J. Thompson, *The Golden–Thompson inequality — historical aspects
and random matrix applications*, arXiv:1408.2008v1, equation (1.1)). The general inequality is
recorded as wanted in `WantedExt.LinearAlgebra.Matrix.GoldenThompsonWanted`.

This file proves two pieces of it, and nothing more:

* `trace_exp_add_of_commute`: for **commuting** matrices the two sides are equal, since then
  `e^{A + B} = e^A e^B`; hence `golden_thompson_of_commute`, the inequality restricted to commuting
  matrices.
* `trace_exp_mul_exp_nonneg`: for Hermitian `A`, `B` the right side `tr (e^A e^B)` is a
  nonnegative real number, because it equals `tr (e^{A/2} e^B e^{A/2})`. So the inequality, stated
  in `ℂ` with its partial order, compares two real numbers.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.GoldenThompson

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Golden–Thompson equality for commuting matrices.** If `A` and `B` commute then
`tr e^{A + B} = tr (e^A e^B)`, because `e^{A + B} = e^A e^B` (`Matrix.exp_add_of_commute`). This
is the equality case of the Golden–Thompson inequality (Forrester and Thompson,
arXiv:1408.2008v1, equation (1.1)); no Hermitian hypothesis is needed. -/
theorem trace_exp_add_of_commute {A B : Matrix n n ℂ} (h : Commute A B) :
    (NormedSpace.exp (A + B)).trace = (NormedSpace.exp A * NormedSpace.exp B).trace := by
  rw [Matrix.exp_add_of_commute A B h]

/-- **Golden–Thompson inequality for commuting matrices.** If `A` and `B` commute then
`tr e^{A + B} ≤ tr (e^A e^B)` in the partial order of `ℂ`, with equality. This is only the
restriction to commuting matrices of the Golden–Thompson inequality (Forrester and Thompson,
arXiv:1408.2008v1, equation (1.1)); the general case is wanted. -/
theorem golden_thompson_of_commute {A B : Matrix n n ℂ} (h : Commute A B) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace :=
  (trace_exp_add_of_commute h).le

/-- The exponential of a matrix is the square of the exponential of its half. -/
private lemma exp_eq_exp_half_mul_exp_half (A : Matrix n n ℂ) :
    NormedSpace.exp A =
      NormedSpace.exp ((2⁻¹ : ℝ) • A) * NormedSpace.exp ((2⁻¹ : ℝ) • A) := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
  norm_num

/-- **The right side of Golden–Thompson is a nonnegative real.** For Hermitian `A` and `B`,
`0 ≤ tr (e^A e^B)` in the partial order of `ℂ`, that is, the trace is real and nonnegative. Indeed
`tr (e^A e^B) = tr (X Xᴴ)` with `X = e^{A/2} e^{B/2}`. So the Golden–Thompson inequality
`tr e^{A + B} ≤ tr (e^A e^B)` (Forrester and Thompson, arXiv:1408.2008v1, equation (1.1)) compares
two real numbers even though `e^A e^B` need not be Hermitian. -/
theorem trace_exp_mul_exp_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    0 ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
  set P := NormedSpace.exp ((2⁻¹ : ℝ) • A)
  set Q := NormedSpace.exp ((2⁻¹ : ℝ) • B)
  have hP : P.IsHermitian := Matrix.IsHermitian.exp ((IsSelfAdjoint.all (2⁻¹ : ℝ)).smul hA)
  have hQ : Q.IsHermitian := Matrix.IsHermitian.exp ((IsSelfAdjoint.all (2⁻¹ : ℝ)).smul hB)
  have hX : (NormedSpace.exp A * NormedSpace.exp B).trace =
      ((P * Q) * (P * Q).conjTranspose).trace := by
    rw [exp_eq_exp_half_mul_exp_half A, exp_eq_exp_half_mul_exp_half B, Matrix.conjTranspose_mul,
      hP.eq, hQ.eq, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rfl
  rw [hX]
  exact (Matrix.posSemidef_self_mul_conjTranspose (P * Q)).trace_nonneg

end MathlibExt.LinearAlgebra.Matrix.GoldenThompson
