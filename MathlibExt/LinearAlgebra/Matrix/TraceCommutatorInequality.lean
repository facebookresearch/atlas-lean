/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `tr (XY)² ≤ tr X²Y²` and the case `t = 2` of the Lieb–Thirring trace inequality

For Hermitian matrices `X` and `Y`,
`2 (tr X²Y² - tr (XY)²) = tr (C* C)` with `C = XY - YX`,
so `tr (XY)² ≤ tr X²Y²`, both sides being real. This is the first step of the usual proof of the
Golden–Thompson inequality, and it is the case `t = 2` of the Lieb–Thirring trace inequality
`tr (A^{1/2} B A^{1/2})^t ≤ tr (A^{t/2} B^t A^{t/2})` for positive-semidefinite `A`, `B` and `t ≥ 1`
(E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
draft of May 3, 2009, Theorem 7.4, with the roles of `A` and `B` exchanged). The file proves that
case in the exact form of the wanted
`MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted.araki_lieb_thirring` with `r = 2`,
`q = 1`.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.TraceCommutatorInequality

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Cyclicity of the trace for four factors. -/
private lemma cyc4 (A B C D : Matrix n n ℂ) : (A * B * C * D).trace = (D * A * B * C).trace := by
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- **Commutator identity for traces.** For Hermitian `X` and `Y`, with `C = XY - YX`,
`tr (C* C) = 2 (tr (X X Y Y) - tr (X Y X Y))`. -/
theorem trace_commutator_conjTranspose_mul_self {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) :
    ((X * Y - Y * X).conjTranspose * (X * Y - Y * X)).trace =
      2 * ((X * X * Y * Y).trace - (X * Y * X * Y).trace) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX.eq, hY.eq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  simp only [← Matrix.mul_assoc]
  have h1 : (Y * X * X * Y).trace = (X * X * Y * Y).trace := by rw [cyc4, cyc4, cyc4]
  have h2 : (Y * X * Y * X).trace = (X * Y * X * Y).trace := by rw [cyc4]
  have h4 : (X * Y * Y * X).trace = (X * X * Y * Y).trace := by rw [cyc4]
  rw [h1, h2, h4]
  ring

omit [DecidableEq n] in
/-- **`tr (XY)² ≤ tr X²Y²` for Hermitian matrices.** For Hermitian complex matrices `X` and `Y`,
`tr (X Y X Y) ≤ tr (X X Y Y)` in the partial order of `ℂ`: the difference is the nonnegative real
`tr (C* C) / 2` with `C = XY - YX`. It is the case `t = 2` of the Lieb–Thirring trace inequality
(E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes
draft of May 3, 2009, Theorem 7.4) and the first step of the usual proof of the Golden–Thompson
inequality. -/
theorem trace_mul_mul_mul_mul_le {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) :
    (X * Y * X * Y).trace ≤ (X * X * Y * Y).trace := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (X * Y - Y * X)).trace_nonneg
  rw [trace_commutator_conjTranspose_mul_self hX hY] at h
  have h2 : (0 : ℂ) ≤ (X * X * Y * Y).trace - (X * Y * X * Y).trace := by
    have : (X * X * Y * Y).trace - (X * Y * X * Y).trace =
        (2 : ℂ)⁻¹ * (2 * ((X * X * Y * Y).trace - (X * Y * X * Y).trace)) := by
      field_simp
    rw [this]
    exact mul_nonneg (by norm_num [Complex.nonneg_iff]) h
  exact sub_nonneg.mp h2

/-- The functional-calculus square root of a positive-semidefinite matrix squares back to it. -/
private lemma cfc_rpow_half_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A = A := by
  have hcont : Continuous (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) := Real.continuous_rpow_const (by norm_num)
  rw [← cfc_mul (fun x : ℝ => x ^ (2⁻¹ : ℝ)) (fun x : ℝ => x ^ (2⁻¹ : ℝ)) A hcont.continuousOn
    hcont.continuousOn]
  conv_rhs => rw [← cfc_id' ℝ A (ha := hA.isHermitian)]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
  rw [← Real.rpow_add' hx0 (by norm_num)]
  norm_num

/-- The real square of a Hermitian matrix by the functional calculus is its square. -/
private lemma cfc_rpow_two {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    cfc (· ^ (2 : ℝ) : ℝ → ℝ) M = M * M := by
  have h : (· ^ (2 : ℝ) : ℝ → ℝ) = fun x => x * x := by
    funext x; rw [Real.rpow_two, sq]
  rw [h, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M continuous_id.continuousOn
    continuous_id.continuousOn]
  erw [cfc_id' ℝ M (ha := hM)]

/-- The first power by the functional calculus is the identity on Hermitian matrices. -/
private lemma cfc_rpow_one {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    cfc (· ^ (1 : ℝ) : ℝ → ℝ) M = M := by
  simp only [Real.rpow_one]
  exact cfc_id' ℝ M (ha := hM)

/-- **Lieb–Thirring trace inequality for `t = 2`.** For positive-semidefinite complex matrices `A`
and `B`, `tr (A^{1/2} B A^{1/2})² ≤ tr (A B² A)`. This is the instance `r = 2`, `q = 1` of the
Araki–Lieb–Thirring inequality (H. Araki, Lett. Math. Phys. 19 (1990) 167–170; K. M. R.
Audenaert, arXiv:math/0701129, Theorem 1), stated in the exact form of the wanted
`MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted.araki_lieb_thirring`, and the case
`t = 2` of the Lieb–Thirring trace inequality (E. A. Carlen, *Trace inequalities and quantum
entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 7.4). Powers are
`cfc (· ^ p)`; both sides reduce to `tr (A B A B) ≤ tr (A A B B)`. -/
theorem araki_lieb_thirring_two_one {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    RCLike.re (cfc (· ^ ((2 : ℝ) * 1) : ℝ → ℝ)
        (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * B * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A)).trace ≤
      RCLike.re (cfc (· ^ (1 : ℝ) : ℝ → ℝ)
        (cfc (· ^ ((2 : ℝ) / 2) : ℝ → ℝ) A * cfc (· ^ (2 : ℝ) : ℝ → ℝ) B *
          cfc (· ^ ((2 : ℝ) / 2) : ℝ → ℝ) A)).trace := by
  set S := cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A with hSdef
  have hS : S.IsHermitian := cfc_predicate _ A
  have hSS : S * S = A := cfc_rpow_half_mul_self hA
  have hBh := hB.isHermitian
  have hAh := hA.isHermitian
  have hM : (S * B * S).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hBh.eq, Matrix.mul_assoc]
  have hN : (A * (B * B) * A).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAh.eq,
      hBh.eq]
    simp only [Matrix.mul_assoc]
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  rw [mul_one, cfc_rpow_two hM, h22, cfc_rpow_one hAh, cfc_rpow_two hBh, cfc_rpow_one hN]
  have hL : (S * B * S * (S * B * S)).trace = (A * B * A * B).trace := by
    have : S * B * S * (S * B * S) = S * (B * (S * S) * B * S) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, hSS]
    simp only [Matrix.mul_assoc]
    rw [hSS, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hR : (A * (B * B) * A).trace = (A * A * B * B).trace := by
    rw [← Matrix.mul_assoc A B B, cyc4]
  rw [hL, hR]
  exact (Complex.le_def.mp (trace_mul_mul_mul_mul_le hAh hBh)).1

end MathlibExt.LinearAlgebra.Matrix.TraceCommutatorInequality
