/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm

@[expose] public section

/-!
# Tests for nonzero eigenvalues of a product, in either order

Concrete checks of `MathlibExt.LinearAlgebra.Eigenspace.MulComm` and
`MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm`: a genuine eigenvalue
transferred across a noncommuting matrix product, the sharpness of the
`μ ≠ 0` hypothesis (a rectangular example where `0` is an eigenvalue of
`A * B` but not of `B * A`), and applications of the bounded-operator
theorems.
-/

namespace MathlibExt.LinearAlgebra.Eigenspace.MulCommTest

open Matrix

/-- The first test matrices: `A` is diagonal, `B` is a shear, so `A * B` and
`B * A` do not commute. -/
private abbrev testA : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 1]

/-- The second test matrix. -/
private abbrev testB : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- `2` is an eigenvalue of `testA * testB`, with eigenvector `![1, 0]`. -/
private theorem hasEigenvalue_two_mul :
    Module.End.HasEigenvalue (Matrix.toLin' (testA * testB)) 2 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0]) ?_
  refine Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    fin_cases i <;>
      simp [Matrix.vecHead, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two,
        testA, testB]
  · intro h
    have h0 := congrFun h 0
    simp at h0

/-- The eigenvalue `2` transfers to `testB * testA`, via the product
eigenvalue theorem (it is not computed directly). -/
example : Module.End.HasEigenvalue (Matrix.toLin' (testB * testA)) 2 :=
  (MathlibExt.LinearAlgebra.Eigenspace.MulComm.Matrix.hasEigenvalue_mul_iff
    testA testB (by norm_num)).mp hasEigenvalue_two_mul

/-- The geometric multiplicities of the eigenvalue `2` agree for the two
products. -/
example :
    Module.finrank ℚ (Module.End.eigenspace (Matrix.toLin' (testA * testB)) 2) =
      Module.finrank ℚ (Module.End.eigenspace (Matrix.toLin' (testB * testA)) 2) :=
  MathlibExt.LinearAlgebra.Eigenspace.MulComm.Matrix.finrank_eigenspace_mul_eq
    testA testB (by norm_num)

/-- The generalized multiplicities (at exponent `2`) agree for the two
products. -/
example :
    Module.finrank ℚ
        (Module.End.genEigenspace (Matrix.toLin' (testA * testB)) 2 2) =
      Module.finrank ℚ
        (Module.End.genEigenspace (Matrix.toLin' (testB * testA)) 2 2) :=
  MathlibExt.LinearAlgebra.Eigenspace.MulComm.Matrix.finrank_genEigenspace_mul_eq
    testA testB (by norm_num) 2

/-- A rectangular pair for which `0` is an eigenvalue of `A * B` but not of
`B * A`: `B * A = 1` on `ℚ²`, while `A * B` is the projection onto the first
two coordinates of `ℚ³`. -/
private abbrev rectA : Matrix (Fin 3) (Fin 2) ℚ := !![1, 0; 0, 1; 0, 0]

/-- The left inverse of `rectA`. -/
private abbrev rectB : Matrix (Fin 2) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0]

/-- `0` is an eigenvalue of `rectA * rectB`, with eigenvector `![0, 0, 1]`. -/
private theorem hasEigenvalue_zero_rect_mul :
    Module.End.HasEigenvalue (Matrix.toLin' (rectA * rectB)) 0 := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ![0, 0, 1]) ?_
  refine Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    fin_cases i <;>
      simp [Matrix.vecHead, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two,
        rectA, rectB]
  · intro h
    have h2 := congrFun h 2
    simp at h2

/-- `rectB * rectA` is the identity, so it has no eigenvalue `0`. -/
private theorem not_hasEigenvalue_zero_rect_mul' :
    ¬ Module.End.HasEigenvalue (Matrix.toLin' (rectB * rectA)) 0 := by
  have hBA : rectB * rectA = (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, rectA, rectB]
  rw [hBA, Matrix.toLin'_one]
  intro h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hv0 := hv.apply_eq_smul
  simp at hv0
  exact hv.2 hv0

/-- The `μ ≠ 0` hypothesis is sharp: `0` is an eigenvalue of `rectA * rectB`
but not of `rectB * rectA`. -/
example : Module.End.HasEigenvalue (Matrix.toLin' (rectA * rectB)) 0 ∧
    ¬ Module.End.HasEigenvalue (Matrix.toLin' (rectB * rectA)) 0 :=
  ⟨hasEigenvalue_zero_rect_mul, not_hasEigenvalue_zero_rect_mul'⟩

/-- Bounded operators on `ℝ × ℝ` used to exercise the `ContinuousLinearMap`
versions: `S (a, b) = (2 a, b)` and `T (a, b) = (a + b, b)`. -/
private noncomputable def testS : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod (2 • ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The second bounded test operator. -/
private noncomputable def testT : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Nonzero eigenvalue transfer for the bounded operators `testS * testT` and
`testT * testS`. -/
example : Module.End.HasEigenvalue ((testS * testT : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
      Module.End ℝ (ℝ × ℝ)) 2 ↔
    Module.End.HasEigenvalue ((testT * testS : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
      Module.End ℝ (ℝ × ℝ)) 2 :=
  MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm.ContinuousLinearMap.hasEigenvalue_mul_iff
    testS testT (by norm_num)

/-- Equal geometric multiplicities for the bounded operators. -/
example : Module.finrank ℝ (Module.End.eigenspace
        ((testS * testT : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : Module.End ℝ (ℝ × ℝ)) 2) =
      Module.finrank ℝ (Module.End.eigenspace
        ((testT * testS : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : Module.End ℝ (ℝ × ℝ)) 2) :=
  MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm.ContinuousLinearMap.finrank_eigenspace_mul_eq
    testS testT (by norm_num)

/-- Equal generalized multiplicities for the bounded operators. -/
example : Module.finrank ℝ (Module.End.genEigenspace
        ((testS * testT : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : Module.End ℝ (ℝ × ℝ)) 2 2) =
      Module.finrank ℝ (Module.End.genEigenspace
        ((testT * testS : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : Module.End ℝ (ℝ × ℝ)) 2 2) :=
  MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm.ContinuousLinearMap.finrank_genEigenspace_mul_eq
    testS testT (by norm_num) 2

/-- Bounded operator on `EuclideanSpace ℝ (Fin 2)` for the adjoint corollary:
the shear matrix `!![1, 1; 0, 1]`, made continuous via finite-dimensionality. -/
private noncomputable def testTEucl :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin !![1, 1; 0, 1])

/-- Nonzero eigenvalues of `testTEucl† * testTEucl` vs
`testTEucl * testTEucl†`. -/
example : Module.End.HasEigenvalue
        ((ContinuousLinearMap.adjoint testTEucl * testTEucl :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
          Module.End ℝ (EuclideanSpace ℝ (Fin 2))) 2 ↔
      Module.End.HasEigenvalue
        ((testTEucl * ContinuousLinearMap.adjoint testTEucl :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
          Module.End ℝ (EuclideanSpace ℝ (Fin 2))) 2 :=
  MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm.ContinuousLinearMap.hasEigenvalue_adjoint_mul_self_iff
    testTEucl (by norm_num)

end MathlibExt.LinearAlgebra.Eigenspace.MulCommTest
