/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import MathlibExt.Analysis.Fourier.AddCircle.FejerKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Complex.Norm

/-!
# Fejér kernels on the unit circle

On `UnitAddCircle = ℝ / ℤ`, let `D_N(x) = ∑ n=0..N, fourier n x`. The continuous
Fejér kernel is `K_N(x) = ‖D_N(x)‖² / (N + 1)`, viewed as a complex-valued function.
It is real and nonnegative and has integral one for the Haar probability measure.
All natural `N`, including `N = 0`, are included. Translations and inversion preserve
its unit mass. The `L²` inner product of `D_N` with itself is `N + 1`.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- **Dirichlet polynomial on the unit circle.** For `N : ℕ`, `D_N : C(UnitAddCircle, ℂ)`
is the sum of Fourier characters with frequencies `0,…,N`. -/
def circleDirichletPolynomial (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ Finset.range (N + 1), fourier (n : ℤ)

/-- **Evaluation of the Dirichlet polynomial.** For `N : ℕ` and `x : UnitAddCircle`,
`circleDirichletPolynomial N x = ∑ n ∈ range (N + 1), fourier (n : ℤ) x`. -/
theorem circleDirichletPolynomial_apply (N : ℕ) (x : UnitAddCircle) :
    circleDirichletPolynomial N x = ∑ n ∈ Finset.range (N + 1), fourier (n : ℤ) x := by
  simp only [circleDirichletPolynomial, ContinuousMap.sum_apply]

/-- **Continuous Fejér kernel on the unit circle.** For `N : ℕ`, this is the continuous
complex-valued Fejér kernel on `ℝ/ℤ`, with value `‖D_N(x)‖² / (N + 1)` at `x`. -/
def circleFejerKernel (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ⟨AddCircle.fejerKernel (T := (1 : ℝ)) N,
    AddCircle.fejerKernel_continuous (T := (1 : ℝ)) N⟩

/-- **Squared-modulus formula for the Fejér kernel.** For `N : ℕ` and `x : UnitAddCircle`,
`circleFejerKernel N x = (‖circleDirichletPolynomial N x‖² / (N + 1) : ℝ)` in `ℂ`. -/
theorem circleFejerKernel_apply (N : ℕ) (x : UnitAddCircle) :
    circleFejerKernel N x = ((‖circleDirichletPolynomial N x‖ ^ 2 / (N + 1 : ℝ)) : ℝ) := by
  change AddCircle.fejerKernel (T := (1 : ℝ)) N x = _
  rw [AddCircle.fejerKernel_eq_ofReal, Complex.normSq_eq_norm_sq]
  simpa only [circleDirichletPolynomial_apply, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv] using
    congrArg (fun r : ℝ => (r : ℂ))
      (mul_comm (((N : ℝ) + 1)⁻¹)
        (‖∑ n ∈ Finset.range (N + 1), fourier (n : ℤ) x‖ ^ 2))

/-- **Nonnegativity of the Fejér kernel.** For every `N : ℕ` and `x : UnitAddCircle`,
`0 ≤ (circleFejerKernel N x).re`. -/
theorem circleFejerKernel_re_nonneg (N : ℕ) (x : UnitAddCircle) :
    0 ≤ (circleFejerKernel N x).re := by
  change 0 ≤ (AddCircle.fejerKernel (T := (1 : ℝ)) N x).re
  exact AddCircle.fejerKernel_nonneg (T := (1 : ℝ)) N x

/-- **Real-valued Fejér kernel.** For every `N : ℕ` and `x : UnitAddCircle`,
`(circleFejerKernel N x).im = 0`. -/
theorem circleFejerKernel_im (N : ℕ) (x : UnitAddCircle) : (circleFejerKernel N x).im = 0 := by
  change (AddCircle.fejerKernel (T := (1 : ℝ)) N x).im = 0
  rw [AddCircle.fejerKernel_eq_ofReal]
  rfl

/-- **Norm of the Fejér kernel.** For every `N : ℕ` and `x : UnitAddCircle`,
`‖circleFejerKernel N x‖ = (circleFejerKernel N x).re`. -/
theorem circleFejerKernel_norm (N : ℕ) (x : UnitAddCircle) :
    ‖circleFejerKernel N x‖ = (circleFejerKernel N x).re := by
  change ‖AddCircle.fejerKernel (T := (1 : ℝ)) N x‖ =
    (AddCircle.fejerKernel (T := (1 : ℝ)) N x).re
  have hn := AddCircle.fejerKernel_nonneg (T := (1 : ℝ)) N x
  rw [AddCircle.fejerKernel_eq_ofReal, Complex.ofReal_re] at hn
  rw [AddCircle.fejerKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn, Complex.ofReal_re]

/-- **L² norm of the Dirichlet polynomial.** For every `N : ℕ`, the `L²` inner product
of `D_N` with itself, for the Haar probability measure on `ℝ/ℤ`, is `(N + 1 : ℂ)`. -/
theorem circleDirichletPolynomial_inner (N : ℕ) :
    ⟪(circleDirichletPolynomial N).toLp 2 AddCircle.haarAddCircle ℂ,
      (circleDirichletPolynomial N).toLp 2 AddCircle.haarAddCircle ℂ⟫_ℂ = (N + 1 : ℂ) := by
  have hOrthonormal :
      Orthonormal ℂ (fun n : ℕ =>
        (fourierLp (T := (1 : ℝ)) 2 (n : ℤ) :
          Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) (i : ℤ) (j : ℤ)
    simpa only [Int.ofNat_inj] using h
  have h := hOrthonormal.inner_sum
    (fun _ : ℕ => (1 : ℂ)) (fun _ : ℕ => (1 : ℂ)) (Finset.range (N + 1))
  simpa only [circleDirichletPolynomial, map_sum, fourierLp, one_smul, map_one, one_mul,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one] using h

/-- **Unit mass of the Fejér kernel.** For every `N : ℕ`,
`∫ x, circleFejerKernel N x ∂AddCircle.haarAddCircle = 1` on `UnitAddCircle`. -/
theorem circleFejerKernel_integral (N : ℕ) :
    (∫ x, circleFejerKernel N x ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  change (∫ x : UnitAddCircle, AddCircle.fejerKernel (T := (1 : ℝ)) N x
    ∂AddCircle.haarAddCircle) = 1
  exact AddCircle.integral_fejerKernel (T := (1 : ℝ)) N

/-- **Unit mass after translation and inversion.** For every `N : ℕ` and `x : UnitAddCircle`,
`∫ t, circleFejerKernel N (x - t) ∂AddCircle.haarAddCircle = 1`. -/
theorem circleFejerKernel_integral_sub (N : ℕ) (x : UnitAddCircle) :
    (∫ t, circleFejerKernel N (x - t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  rw [integral_sub_left_eq_self (circleFejerKernel N)
    (AddCircle.haarAddCircle : Measure UnitAddCircle) x]
  exact circleFejerKernel_integral N

end MathlibExt.Analysis.Fourier
