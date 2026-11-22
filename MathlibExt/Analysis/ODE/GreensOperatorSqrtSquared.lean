/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
public import MathlibExt.Analysis.ODE.GreensOperator

/-!
# The square of the Green's operator's square root

The v1 book defines the square root `A^{1/2}` of the Green's operator for
the Dirichlet Laplacian on `[0, 1]` by its action on the sine eigenbasis:
if `f = ∑' k, c_k b_k` with `c_k = ⟨b_k, f⟩`, then
`A^{1/2} f = ∑' k, (1 / (kπ)) c_k b_k`. The Green's operator itself has the
corresponding expansion with eigenvalues `λ_k = 1 / (k²π²)`.

This file identifies the canonical square root with a bounded continuous
diagonal map and proves its composition with itself equals the supplied
Green linear operator. The operator must have the canonical self-adjoint
and kernel-a.e. properties, and the basis must represent the actual indexed
sine functions a.e. The proof combines bounded diagonal squaring with the
already proved canonical Green eigendecomposition.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.greensOperatorSqrt` with `greensEigenvalueSqrt` and
`greensEigenvalue` (Definition, May 13, 2021 section). The v1 file states
only the definition of `A^{1/2}`; the squaring identity is not proved there.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal

namespace MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared

open MathlibExt.Analysis.ODE.GreensOperator

/-- The Green's square-root coefficients `1 / (kπ)` are bounded by `1 / π`. -/
private theorem greensSqrtCoeff_bound (k : ℕ+) :
    ‖greensEigenvalueSqrt k‖ ≤ 1 / Real.pi := by
  unfold greensEigenvalueSqrt
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hk1, hpi])

/-- The square of a Green's square-root coefficient is the Green's eigenvalue. -/
private theorem greensSqrtCoeff_sq (k : ℕ+) :
    (greensEigenvalueSqrt k) ^ 2 = greensEigenvalue k := by
  unfold greensEigenvalueSqrt greensEigenvalue
  have hk : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- The canonical Green square root on a certified sine basis equals its
bounded continuous diagonal map. -/
theorem greensOperatorSqrt_eq_diagonal
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ)) {C : ℝ}
    (hC : ∀ k : ℕ+, ‖greensEigenvalueSqrt k‖ ≤ C) (f : L2UnitInterval) :
    greensOperatorSqrt b hb f = diagonalOperator b greensEigenvalueSqrt
      hC f := by
  rw [diagonalOperator_eq_tsum]
  rfl

/-- **The actual Green square-root operator squared equals the Green operator.**
Use the canonical kernel and the certified indexed sine eigenbasis, with the
same self-adjoint/kernel-a.e. hypotheses as its eigendecomposition. -/
theorem greensOperatorSqrt_sq
    (A : Module.End ℝ L2UnitInterval)
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t))
    (f : L2UnitInterval) :
    greensOperatorSqrt b hb (greensOperatorSqrt b hb f) = A f := by
  have hexpand := (greens_operator_eigendecomposition A b hA_sa hb hA_greens).2.2 f
  rw [greensOperatorSqrt_eq_diagonal b hb greensSqrtCoeff_bound,
    greensOperatorSqrt_eq_diagonal b hb greensSqrtCoeff_bound]
  rw [diagonalOperator_sq greensSqrtCoeff_bound, diagonalOperator_eq_tsum]
  simpa only [greensSqrtCoeff_sq] using hexpand.symm

end MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared
