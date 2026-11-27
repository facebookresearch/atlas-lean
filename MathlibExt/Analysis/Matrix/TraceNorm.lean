/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Trace norm and Euclidean linear-map singular values

For a finite square complex matrix `M`, the canonical trace norm is
`Matrix.traceNorm M = Re (Tr (sqrt (Mᴴ * M)))`. The theorem here identifies it with the
finite sum of the singular values of `Matrix.toEuclideanLin M`. The canonical trace norm
and its nonnegativity, zero, scalar and sign laws come from
`QuantumInfo.ForMathlib.MatrixNorm.TraceNorm` in the pinned Physlib dependency.
The identity includes an empty matrix index type and uses the Euclidean inner product.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Trace norm as a sum of Euclidean operator singular values.** Let `n` be a finite
index type with decidable equality and `M : Matrix n n ℂ`. Then the canonical trace norm
`Re (Tr (sqrt (Mᴴ * M)))` equals the sum of `M.toEuclideanLin.singularValues i` for
`0 ≤ i < card n`. The empty-index case gives zero on both sides. -/
theorem traceNorm_eq_sum_linearMap_singularValues (M : Matrix n n ℂ) :
    M.traceNorm = ∑ i ∈ Finset.range (Fintype.card n),
      M.toEuclideanLin.singularValues i := by
  classical
  let e : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := by simp
  have hmul : (Mᴴ * M).toEuclideanLin =
      Mᴴ.toEuclideanLin ∘ₗ M.toEuclideanLin := by
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_mul (EuclideanSpace.basisFun n ℂ).toBasis
        (EuclideanSpace.basisFun n ℂ).toBasis (EuclideanSpace.basisFun n ℂ).toBasis Mᴴ M)
  have hGram : (Mᴴ * M).toEuclideanLin =
      M.toEuclideanLin.adjoint ∘ₗ M.toEuclideanLin := by
    simpa only [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using hmul
  calc
    M.traceNorm = ∑ j : n, _root_.singularValues M j :=
      Matrix.traceNorm_eq_sum_singularValues M
    _ = ∑ i : Fin (Fintype.card n), _root_.singularValues M (e i) :=
      (e.sum_comp _).symm
    _ = ∑ i : Fin (Fintype.card n), M.toEuclideanLin.singularValues i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [M.toEuclideanLin.singularValues_fin hdim i]
      simp only [_root_.singularValues, Matrix.conjTranspose_conjTranspose,
        Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀,
        e, Equiv.symm_apply_apply, hGram]
    _ = ∑ i ∈ Finset.range (Fintype.card n), M.toEuclideanLin.singularValues i := by
      rw [Fin.sum_univ_eq_sum_range]

end Matrix
