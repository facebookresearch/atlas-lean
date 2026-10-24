/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The square of the Green's operator's square root

The v1 book defines the square root `A^{1/2}` of the Green's operator for
the Dirichlet Laplacian on `[0, 1]` by its action on the sine eigenbasis:
if `f = ∑' k, c_k b_k` with `c_k = ⟨b_k, f⟩`, then
`A^{1/2} f = ∑' k, (1 / (kπ)) c_k b_k`. The Green's operator itself has the
corresponding expansion with eigenvalues `λ_k = 1 / (k²π²)`.

This file proves the defining property of that square root: applying the
diagonal operator with coefficients `1 / (kπ)` twice equals applying the
diagonal operator with coefficients `1 / (k²π²)`, i.e. `(A^{1/2})² = A`
on the level of eigenbasis expansions. The proof is the general diagonal
operator squaring theorem in
`MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal`, instantiated
at the Green's coefficients.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.greensOperatorSqrt` with `greensEigenvalueSqrt` and
`greensEigenvalue` (Definition, May 13, 2021 section). The v1 file states
only the definition of `A^{1/2}`; the squaring identity is not proved there.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal

namespace MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared

/-- The Green's square-root coefficients `1 / (kπ)` are bounded by `1 / π`. -/
private theorem greensSqrtCoeff_bound (k : ℕ+) :
    ‖(1 / ((k : ℝ) * Real.pi) : ℝ)‖ ≤ 1 / Real.pi := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hk1, hpi])

/-- The square of a Green's square-root coefficient is the Green's eigenvalue. -/
private theorem greensSqrtCoeff_sq (k : ℕ+) :
    ((1 : ℝ) / ((k : ℝ) * Real.pi)) ^ 2 = 1 / ((k : ℝ) ^ 2 * Real.pi ^ 2) := by
  have hk : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The Green's square-root operator squared is the Green's operator.**
Applying the diagonal operator with coefficients `1 / (kπ)` — the v1
definition of `A^{1/2}` — twice equals applying the diagonal operator with
coefficients `1 / (k²π²)`, the Green's operator expansion. -/
theorem greensOperatorSqrt_sq
    (b : HilbertBasis ℕ+ ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) * Real.pi))
        (diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) * Real.pi)) f) =
      diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) f := by
  have hsq := diagonalOperator_sq (b := b)
    (a := fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) * Real.pi)) greensSqrtCoeff_bound f
  have hfun : (fun k : ℕ+ => ((1 : ℝ) / ((k : ℝ) * Real.pi)) ^ 2) =
      (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) :=
    funext fun k => greensSqrtCoeff_sq k
  rw [hfun] at hsq
  exact hsq

end MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared
