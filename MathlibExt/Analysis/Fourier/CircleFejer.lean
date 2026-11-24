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
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Complex.Norm

/-!
# Actual normalized-circle Fejer kernel

This stock-only prerequisite supplies a genuine positive normalized kernel
for the Fourier polynomial approximation needed to construct the original
Hardy predual forward map. The kernel is the literal normalized squared
Dirichlet sum. No Hardy, predual, weak-star or desired approximation output is
an input. Source-specific Fourier Hardy carriers stay in the source modules.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- The Dirichlet polynomial with nonnegative frequencies on the normalized additive unit circle. -/
def circleDirichletPolynomial (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ Finset.range (N + 1), fourier (n : ℤ)

/-- Literal pointwise finite Fourier sum of the actual Dirichlet polynomial. -/
theorem circleDirichletPolynomial_apply (N : ℕ) (x : UnitAddCircle) :
    circleDirichletPolynomial N x = ∑ n ∈ Finset.range (N + 1), fourier (n : ℤ) x := by
  simp only [circleDirichletPolynomial, ContinuousMap.sum_apply]

/-- The actual Fejer kernel is the normalized squared absolute Dirichlet polynomial. -/
def circleFejerKernel (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ((N + 1 : ℂ)⁻¹) • (Star.star (circleDirichletPolynomial N) * circleDirichletPolynomial N)

/-- Literal positive real density represented by the actual complex Fejer kernel. -/
theorem circleFejerKernel_apply (N : ℕ) (x : UnitAddCircle) :
    circleFejerKernel N x = ((‖circleDirichletPolynomial N x‖ ^ 2 / (N + 1 : ℝ)) : ℝ) := by
  change (N + 1 : ℂ)⁻¹ * (Star.star (circleDirichletPolynomial N x) *
    circleDirichletPolynomial N x) = _
  have hc : Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x =
      ((‖circleDirichletPolynomial N x‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.star_def, Complex.ofReal_pow] using
      Complex.conj_mul' (circleDirichletPolynomial N x)
  rw [hc, Complex.ofReal_div]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    div_eq_mul_inv]
  exact mul_comm _ _

/-- Positivity of the actual kernel does not require any desired norm-bound certificate. -/
theorem circleFejerKernel_re_nonneg (N : ℕ) (x : UnitAddCircle) : 0 ≤ (circleFejerKernel N x).re := by
  rw [circleFejerKernel_apply]
  change 0 ≤ ‖circleDirichletPolynomial N x‖ ^ 2 / (N + 1 : ℝ)
  exact div_nonneg (sq_nonneg _) (by positivity)

/-- The actual kernel is real-valued. -/
theorem circleFejerKernel_im (N : ℕ) (x : UnitAddCircle) : (circleFejerKernel N x).im = 0 := by
  rw [circleFejerKernel_apply]
  rfl

/-- The norm of the genuine complex kernel equals its nonnegative real density. -/
theorem circleFejerKernel_norm (N : ℕ) (x : UnitAddCircle) :
    ‖circleFejerKernel N x‖ = (circleFejerKernel N x).re := by
  have hn : 0 ≤ ‖circleDirichletPolynomial N x‖ ^ 2 / (N + 1 : ℝ) :=
    div_nonneg (sq_nonneg _) (by positivity)
  rw [circleFejerKernel_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn, Complex.ofReal_re]

/-- The genuine finite Dirichlet L-two vector has its literal squared norm. -/
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

/-- The actual positive normalized kernel has integral exactly one. -/
theorem circleFejerKernel_integral (N : ℕ) :
    (∫ x, circleFejerKernel N x ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  have hi := ContinuousMap.inner_toLp (AddCircle.haarAddCircle : Measure UnitAddCircle)
    (circleDirichletPolynomial N) (circleDirichletPolynomial N)
  have hj : (∫ x, Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = (N + 1 : ℂ) := by
    have he : (fun x : UnitAddCircle => circleDirichletPolynomial N x *
        (starRingEnd ℂ) (circleDirichletPolynomial N x)) =
        fun x => Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x := by
      funext x
      rw [starRingEnd_apply, mul_comm]
    rw [he] at hi
    exact hi.symm.trans (circleDirichletPolynomial_inner N)
  change (∫ x, (N + 1 : ℂ)⁻¹ •
    (Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x)
    ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1
  rw [integral_smul, hj, smul_eq_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N)

/-- Haar invariance gives the actual unit mass for every translated/inverted kernel. -/
theorem circleFejerKernel_integral_sub (N : ℕ) (x : UnitAddCircle) :
    (∫ t, circleFejerKernel N (x - t) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  rw [integral_sub_left_eq_self (circleFejerKernel N)
    (AddCircle.haarAddCircle : Measure UnitAddCircle) x]
  exact circleFejerKernel_integral N

end MathlibExt.Analysis.Fourier
