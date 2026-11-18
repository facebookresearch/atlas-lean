/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import MathlibExt.LinearAlgebra.Matrix.MMatrix

/-!
# Planar rate stability criterion

A real planar matrix with negative trace and positive determinant
is Hurwitz, so an equilibrium with such a Jacobian, including a
boundary equilibrium of an admissible rectangle, is locally
exponentially stable by the linearized-stability kernel. The
negative identity is the zero-gain boundary witness.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.Stability

/-- Quadratic with real coefficients of Hurwitz signs has roots of negative real part. -/
theorem quad_neg_re {mu : ℂ} {t d : ℝ} (ht : t < 0) (hd : 0 < d)
    (h : mu ^ 2 - (t : ℂ) * mu + (d : ℂ) = 0) : mu.re < 0 := by
  have hre : mu.re * mu.re - mu.im * mu.im - t * mu.re + d = 0 := by
    have hr := congrArg Complex.re h
    simpa [Complex.add_re, Complex.sub_re, pow_two, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im] using hr
  have him : mu.re * mu.im + mu.im * mu.re - t * mu.im = 0 := by
    have hi := congrArg Complex.im h
    simpa [Complex.add_im, Complex.sub_im, pow_two, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im] using hi
  have hfactor : mu.im * (2 * mu.re - t) = 0 := by
    linear_combination him
  rcases mul_eq_zero.mp hfactor with hy | hx
  · rw [hy] at hre
    simp at hre
    by_contra hcon
    have hle : 0 ≤ mu.re := le_of_not_gt hcon
    nlinarith [hre, hd, ht, hle]
  · linarith [ht, hx]

/-- **Planar trace-determinant Hurwitz criterion.** A real
`2 x 2` matrix with negative trace and positive determinant is
Hurwitz: every complex eigenvalue has negative real part. -/
theorem trace_det_isHurwitz {A : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : A.trace < 0) (hdet : 0 < A.det) : A.IsHurwitz := by
  intro μ hμ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  have hchar := Matrix.charpoly_fin_two (A.map (algebraMap ℝ ℂ))
  rw [hchar] at hμ
  have heval := hμ.eq_zero
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C] at heval
  have htrace : (A.map (algebraMap ℝ ℂ)).trace = algebraMap ℝ ℂ A.trace :=
    (AddMonoidHom.map_trace _ _).symm
  have hdet' : (A.map (algebraMap ℝ ℂ)).det = algebraMap ℝ ℂ A.det := by
    have h := RingHom.map_det (algebraMap ℝ ℂ) A
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [htrace, hdet'] at heval
  exact quad_neg_re htr hdet heval

/-- **Boundary-equilibrium witness.** The negative identity on
the plane, the Jacobian at the zero-gain boundary equilibrium,
is Hurwitz. -/
theorem neg_identity_isHurwitz :
    ((-1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHurwitz := by
  have htr : (-1 : Matrix (Fin 2) (Fin 2) ℝ).trace < 0 := by simp
  have hdet : 0 < (-1 : Matrix (Fin 2) (Fin 2) ℝ).det := by simp [Matrix.det_fin_two]
  exact trace_det_isHurwitz htr hdet

/-- The negative identity has trace `-2` and determinant `1`:
the boundary witness meets the trace-determinant signs. -/
theorem neg_identity_trace_det :
    (-1 : Matrix (Fin 2) (Fin 2) ℝ).trace = -2 ∧
      (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [Matrix.det_fin_two]


end MathlibExt.Biology.Biophysics.NeuralPopulation.Stability
