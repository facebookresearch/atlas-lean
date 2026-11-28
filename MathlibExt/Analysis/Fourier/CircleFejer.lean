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
The coercion lemma `circleFejerKernel_coe` identifies this bundle with the existing
`AddCircle.fejerKernel` at period one. Its real-valued positivity and unit Haar mass
come from the general-period kernel lemmas; translations and inversion preserve that
mass. All natural `N`, including `N = 0`, are included. This module proves that the `L²`
self-inner product of `D_N` is `N + 1`.
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




/-- **Coercion of the bundled unit-circle Fejér kernel.** For every N∈ℕ, the function
underlying circleFejerKernel N is AddCircle.fejerKernel N at period one. Thus the general
kernel formulas, positivity, and Haar normalization apply to this continuous map.
-/
@[simp]
theorem circleFejerKernel_coe (N : ℕ) :
    (circleFejerKernel N : UnitAddCircle → ℂ) =
      AddCircle.fejerKernel (T := (1 : ℝ)) N := rfl

/-- **L² self-inner product of the Dirichlet polynomial.** For every `N : ℕ`, the `L²` inner product
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



end MathlibExt.Analysis.Fourier
