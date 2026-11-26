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

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

open scoped ComplexOrder InnerProductSpace Matrix
open Matrix Complex

/-!
# Unitary diagonalization of a finite unitary matrix

Let I be a finite index type and U an I×I complex unitary matrix. There exist a unitary V and
diagonal entries d_i of modulus 1 with U=V diag(d) Vᴴ. The Hermitian parts Re_op(U)=(U+Uᴴ)/2
and Im_op(U)=(-i/2)(U-Uᴴ) commute and reconstruct U=Re_op(U)+i Im_op(U).
-/

namespace Matrix

variable {n : Type*}

/-- **Hermitian real part of a complex matrix.**

For any square complex matrix U, unitaryRealPart U=(U+Uᴴ)/2, the Hermitian real part in the
operator sense.
-/
private noncomputable def unitaryRealPart (U : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (U + Uᴴ)

/-- **Hermitian imaginary part of a complex matrix.**

For any square complex matrix U, unitaryImagPart U=(-i/2)(U-Uᴴ), the Hermitian imaginary part,
with U=Re_op(U)+i Im_op(U).
-/
private noncomputable def unitaryImagPart (U : Matrix n n ℂ) : Matrix n n ℂ :=
  ((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ)

private theorem unitaryRealPart_isHermitian (U : Matrix n n ℂ) :
    (unitaryRealPart U).IsHermitian := by
  unfold unitaryRealPart
  rw [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
  have hstar : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_inv]
    have h : (2 : ℂ) = Complex.ofReal (2 : ℝ) := by norm_cast
    rw [h, Complex.conj_ofReal]
  rw [hstar, add_comm]

private theorem unitaryImagPart_isHermitian (U : Matrix n n ℂ) :
    (unitaryImagPart U).IsHermitian := by
  unfold unitaryImagPart
  rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
  have hstar_inv2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [Complex.star_def, Complex.conj_inv]
    have h : (2 : ℂ) = Complex.ofReal (2 : ℝ) := by norm_cast
    rw [h, Complex.conj_ofReal]
  have hstar : star ((2 : ℂ)⁻¹ * (-Complex.I)) = -((2 : ℂ)⁻¹ * (-Complex.I)) := by
    calc star ((2 : ℂ)⁻¹ * (-Complex.I))
        = star (-Complex.I) * star ((2 : ℂ)⁻¹) := by rw [star_mul]
      _ = (- star Complex.I) * star ((2 : ℂ)⁻¹) := by rw [star_neg]
      _ = (- -Complex.I) * star ((2 : ℂ)⁻¹) := by rw [Complex.star_def, Complex.conj_I]
      _ = Complex.I * star ((2 : ℂ)⁻¹) := by rw [neg_neg]
      _ = star ((2 : ℂ)⁻¹) * Complex.I := by rw [mul_comm]
      _ = (2 : ℂ)⁻¹ * Complex.I := by rw [hstar_inv2]
      _ = -((2 : ℂ)⁻¹ * (-Complex.I)) := by ring
  calc star ((2 : ℂ)⁻¹ * (-Complex.I)) • (Uᴴ - U)
      = -((2 : ℂ)⁻¹ * (-Complex.I)) • (Uᴴ - U) := by rw [hstar]
    _ = -(((2 : ℂ)⁻¹ * (-Complex.I)) • (Uᴴ - U)) := by rw [neg_smul]
    _ = ((2 : ℂ)⁻¹ * (-Complex.I)) • (-(Uᴴ - U)) := by rw [← smul_neg]
    _ = ((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ) := by
        have : -(Uᴴ - U) = U - Uᴴ := by abel
        rw [this]

private theorem unitary_eq_realPart_add_I_smul_imagPart (U : Matrix n n ℂ) :
    U = unitaryRealPart U + Complex.I • unitaryImagPart U := by
  unfold unitaryRealPart unitaryImagPart
  have hI : Complex.I * (-Complex.I) = 1 := by
    have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by rw [mul_neg]
      _ = -(-1 : ℂ) := by rw [h]
      _ = 1 := by simp
  have hscalar : Complex.I * ((2 : ℂ)⁻¹ * (-Complex.I)) = (2 : ℂ)⁻¹ := by
    calc Complex.I * ((2 : ℂ)⁻¹ * (-Complex.I))
        = (2 : ℂ)⁻¹ * (Complex.I * (-Complex.I)) := by ring
      _ = (2 : ℂ)⁻¹ * 1 := by rw [hI]
      _ = (2 : ℂ)⁻¹ := by ring
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  calc U = (1 : ℂ) • U := by rw [one_smul]
    _ = ((2 : ℂ)⁻¹ * 2) • U := by rw [inv_mul_cancel₀ h2]
    _ = (2 : ℂ)⁻¹ • ((2 : ℂ) • U) := by rw [smul_smul, mul_comm]
    _ = (2 : ℂ)⁻¹ • (U + U) := by rw [two_smul]
    _ = (2 : ℂ)⁻¹ • ((U + Uᴴ) + (U - Uᴴ)) := by
        have : (U + Uᴴ) + (U - Uᴴ) = U + U := by abel
        rw [this]
    _ = (2 : ℂ)⁻¹ • (U + Uᴴ) + (2 : ℂ)⁻¹ • (U - Uᴴ) := by rw [smul_add]
    _ = (2 : ℂ)⁻¹ • (U + Uᴴ) + Complex.I • (((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ)) := by
        rw [smul_smul, hscalar]
    _ = unitaryRealPart U + Complex.I • unitaryImagPart U := rfl

section Commuting

variable [Fintype n] [DecidableEq n]

private theorem unitaryRealPart_mul_unitaryImagPart_comm
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    unitaryRealPart U * unitaryImagPart U =
      unitaryImagPart U * unitaryRealPart U := by
  have hU_star : U * star U = 1 := (mem_unitaryGroup_iff.mp hU)
  have hU_star' : star U * U = 1 := (mem_unitaryGroup_iff'.mp hU)
  have h1 : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact hU_star
  have h2 : Uᴴ * U = 1 := by rw [← star_eq_conjTranspose]; exact hU_star'
  have hLeft : (U + Uᴴ) * (U - Uᴴ) = U * U - Uᴴ * Uᴴ := by
    calc (U + Uᴴ) * (U - Uᴴ)
        = U * U - U * Uᴴ + Uᴴ * U - Uᴴ * Uᴴ := by
          rw [mul_sub, add_mul, add_mul]; abel
      _ = U * U - 1 + 1 - Uᴴ * Uᴴ := by rw [h1, h2]
      _ = U * U - Uᴴ * Uᴴ := by abel
  have hRight : (U - Uᴴ) * (U + Uᴴ) = U * U - Uᴴ * Uᴴ := by
    calc (U - Uᴴ) * (U + Uᴴ)
        = U * U + U * Uᴴ - Uᴴ * U - Uᴴ * Uᴴ := by
          rw [sub_mul, mul_add, mul_add]; abel
      _ = U * U + 1 - 1 - Uᴴ * Uᴴ := by rw [h1, h2]
      _ = U * U - Uᴴ * Uᴴ := by abel
  have hComm : (U + Uᴴ) * (U - Uᴴ) = (U - Uᴴ) * (U + Uᴴ) := by
    rw [hLeft, hRight]
  calc ((2 : ℂ)⁻¹ • (U + Uᴴ)) * (((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ))
      = (2 : ℂ)⁻¹ • ((U + Uᴴ) * (((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ))) := by
        rw [Matrix.smul_mul]
    _ = (2 : ℂ)⁻¹ • (((2 : ℂ)⁻¹ * (-Complex.I)) • ((U + Uᴴ) * (U - Uᴴ))) := by
        rw [Matrix.mul_smul]
    _ = ((2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (-Complex.I))) • ((U + Uᴴ) * (U - Uᴴ)) := by
        rw [smul_smul]
    _ = (((2 : ℂ)⁻¹ * (-Complex.I)) * (2 : ℂ)⁻¹) • ((U + Uᴴ) * (U - Uᴴ)) := by
        rw [mul_comm]
    _ = (((2 : ℂ)⁻¹ * (-Complex.I)) * (2 : ℂ)⁻¹) • ((U - Uᴴ) * (U + Uᴴ)) := by
        rw [hComm]
    _ = ((2 : ℂ)⁻¹ * (-Complex.I)) • ((2 : ℂ)⁻¹ • ((U - Uᴴ) * (U + Uᴴ))) := by
        rw [← smul_smul, mul_comm]
    _ = ((2 : ℂ)⁻¹ * (-Complex.I)) • ((U - Uᴴ) * ((2 : ℂ)⁻¹ • (U + Uᴴ))) := by
        rw [Matrix.mul_smul]
    _ = (((2 : ℂ)⁻¹ * (-Complex.I)) • (U - Uᴴ)) * ((2 : ℂ)⁻¹ • (U + Uᴴ)) := by
        rw [Matrix.smul_mul]

private noncomputable def unitaryRealLin (U : Matrix n n ℂ) :
    EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanLin (unitaryRealPart U)

private noncomputable def unitaryImagLin (U : Matrix n n ℂ) :
    EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanLin (unitaryImagPart U)

private theorem unitaryRealLin_isSymmetric (U : Matrix n n ℂ) :
    (unitaryRealLin U).IsSymmetric := by
  unfold unitaryRealLin
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  exact unitaryRealPart_isHermitian U

private theorem unitaryImagLin_isSymmetric (U : Matrix n n ℂ) :
    (unitaryImagLin U).IsSymmetric := by
  unfold unitaryImagLin
  rw [Matrix.isSymmetric_toEuclideanLin_iff]
  exact unitaryImagPart_isHermitian U

private theorem unitaryRealLin_comm_unitaryImagLin
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    unitaryRealLin U * unitaryImagLin U =
      unitaryImagLin U * unitaryRealLin U := by
  unfold unitaryRealLin unitaryImagLin
  have hMat := unitaryRealPart_mul_unitaryImagPart_comm U hU
  have hMulRealImag :
      Matrix.toEuclideanLin (unitaryRealPart U * unitaryImagPart U) =
        Matrix.toEuclideanLin (unitaryRealPart U) * Matrix.toEuclideanLin (unitaryImagPart U) := by
    calc Matrix.toEuclideanLin (unitaryRealPart U * unitaryImagPart U)
        = Matrix.toEuclideanLin (unitaryRealPart U) ∘ₗ
            Matrix.toEuclideanLin (unitaryImagPart U) := by
          rw [Matrix.toLpLin_mul_same (p := 2)]
      _ = Matrix.toEuclideanLin (unitaryRealPart U) *
            Matrix.toEuclideanLin (unitaryImagPart U) := by
          rw [← Module.End.mul_eq_comp]
  have hMulImagReal :
      Matrix.toEuclideanLin (unitaryImagPart U * unitaryRealPart U) =
        Matrix.toEuclideanLin (unitaryImagPart U) * Matrix.toEuclideanLin (unitaryRealPart U) := by
    calc Matrix.toEuclideanLin (unitaryImagPart U * unitaryRealPart U)
        = Matrix.toEuclideanLin (unitaryImagPart U) ∘ₗ
            Matrix.toEuclideanLin (unitaryRealPart U) := by
          rw [Matrix.toLpLin_mul_same (p := 2)]
      _ = Matrix.toEuclideanLin (unitaryImagPart U) *
            Matrix.toEuclideanLin (unitaryRealPart U) := by
          rw [← Module.End.mul_eq_comp]
  calc Matrix.toEuclideanLin (unitaryRealPart U) *
        Matrix.toEuclideanLin (unitaryImagPart U)
      = Matrix.toEuclideanLin (unitaryRealPart U * unitaryImagPart U) := by
        rw [← hMulRealImag]
    _ = Matrix.toEuclideanLin (unitaryImagPart U * unitaryRealPart U) := by
        rw [hMat]
    _ = Matrix.toEuclideanLin (unitaryImagPart U) *
        Matrix.toEuclideanLin (unitaryRealPart U) := by
        rw [hMulImagReal]

private noncomputable instance instEigenspaceSeminormed
    (U : Matrix n n ℂ) (μ : ℂ) :
    SeminormedAddCommGroup
      ↥(Module.End.eigenspace (unitaryRealLin U) μ) :=
  Submodule.seminormedAddCommGroup _

private noncomputable instance instEigenspaceNormed
    (U : Matrix n n ℂ) (μ : ℂ) :
    NormedAddCommGroup
      ↥(Module.End.eigenspace (unitaryRealLin U) μ) :=
  Submodule.normedAddCommGroup _

private noncomputable instance instEigenspaceInner
    (U : Matrix n n ℂ) (μ : ℂ) :
    InnerProductSpace ℂ
      ↥(Module.End.eigenspace (unitaryRealLin U) μ) :=
  Submodule.innerProductSpace _

private theorem unitaryImagLin_mapsTo_realEigenspace
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (μ : ℂ) :
    Set.MapsTo (unitaryImagLin U)
      (Module.End.eigenspace (unitaryRealLin U) μ)
      (Module.End.eigenspace (unitaryRealLin U) μ) := by
  have hComm : Commute (unitaryRealLin U) (unitaryImagLin U) :=
    unitaryRealLin_comm_unitaryImagLin U hU
  exact Module.End.mapsTo_genEigenspace_of_comm hComm μ 1

private noncomputable def unitaryImagLinRestrict
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (μ : Module.End.Eigenvalues (unitaryRealLin U)) :
    Module.End.eigenspace (unitaryRealLin U) (μ : ℂ) →ₗ[ℂ]
      Module.End.eigenspace (unitaryRealLin U) (μ : ℂ) :=
  (unitaryImagLin U).restrict
    (unitaryImagLin_mapsTo_realEigenspace U hU (μ : ℂ))

private theorem unitaryImagLinRestrict_isSymmetric
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (μ : Module.End.Eigenvalues (unitaryRealLin U)) :
    (unitaryImagLinRestrict U hU μ).IsSymmetric := by
  have hSym : (unitaryImagLin U).IsSymmetric :=
    unitaryImagLin_isSymmetric U
  exact hSym.restrict_invariant
    (unitaryImagLin_mapsTo_realEigenspace U hU (μ : ℂ))

private noncomputable def unitaryImagFiberBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (μ : Module.End.Eigenvalues (unitaryRealLin U)) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ
        ↥(Module.End.eigenspace (unitaryRealLin U) (μ : ℂ))))
      ℂ ↥(Module.End.eigenspace (unitaryRealLin U) (μ : ℂ)) :=
  (unitaryImagLinRestrict_isSymmetric U hU μ).eigenvectorBasis rfl

end Commuting

section JointIndex

variable [Fintype n] [DecidableEq n]

private def unitaryJointIndexType (U : Matrix n n ℂ) : Type _ :=
  Σ _μ : Module.End.Eigenvalues (unitaryRealLin U),
    Fin (Module.finrank ℂ ↥(Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ)))

private noncomputable instance instFintypeUnitaryJointIndexType
    (U : Matrix n n ℂ) : Fintype (unitaryJointIndexType U) := by
  unfold unitaryJointIndexType
  infer_instance

private noncomputable def unitaryJointSigmaBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    OrthonormalBasis (unitaryJointIndexType U) ℂ (EuclideanSpace ℂ n) :=
  let hSym := unitaryRealLin_isSymmetric U
  let hInt : DirectSum.IsInternal
      (fun _μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ)) :=
    hSym.direct_sum_isInternal
  let hOrth : OrthogonalFamily ℂ
      (fun _μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ))
      (fun _μ => (Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ)).subtypeₗᵢ) :=
    hSym.orthogonalFamily_eigenspaces'
  hInt.collectedOrthonormalBasis hOrth fun _μ =>
    unitaryImagFiberBasis U hU _μ

private theorem unitaryJointIndex_card
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    Fintype.card (unitaryJointIndexType U) = Fintype.card n := by
  have hB := (unitaryJointSigmaBasis U hU).toBasis
  have h₁ : Module.finrank ℂ (EuclideanSpace ℂ n) =
      Fintype.card (unitaryJointIndexType U) :=
    Module.finrank_eq_card_basis hB
  have h₂ : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n :=
    finrank_euclideanSpace
  exact h₁.symm.trans h₂

private noncomputable def unitaryJointIndexEquiv
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    unitaryJointIndexType U ≃ n :=
  Fintype.equivOfCardEq (unitaryJointIndex_card U hU)

private noncomputable def unitaryJointBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
  (unitaryJointSigmaBasis U hU).reindex (unitaryJointIndexEquiv U hU)

private noncomputable def unitaryJointBasisIndex
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (i : n) :
    Module.End.Eigenvalues (unitaryRealLin U) :=
  ((unitaryJointIndexEquiv U hU).symm i).1

private theorem unitaryJointBasis_mem_realEigenspace
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (i : n) :
    unitaryJointBasis U hU i ∈
      Module.End.eigenspace (unitaryRealLin U)
        (unitaryJointBasisIndex U hU i : ℂ) := by
  have hBasis_eq :
      unitaryJointBasis U hU =
        (unitaryJointSigmaBasis U hU).reindex
          (unitaryJointIndexEquiv U hU) := rfl
  have hEq :
      unitaryJointBasis U hU i =
        unitaryJointSigmaBasis U hU
          ((unitaryJointIndexEquiv U hU).symm i) := by
    calc unitaryJointBasis U hU i
        = ((unitaryJointSigmaBasis U hU).reindex
            (unitaryJointIndexEquiv U hU)) i := by
          rw [← hBasis_eq]
      _ = unitaryJointSigmaBasis U hU
            ((unitaryJointIndexEquiv U hU).symm i) :=
          OrthonormalBasis.reindex_apply _ _ _
  let hSym : (unitaryRealLin U).IsSymmetric :=
    unitaryRealLin_isSymmetric U
  let hInt : DirectSum.IsInternal
      (fun μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (μ : ℂ)) :=
    hSym.direct_sum_isInternal
  let hOrth : OrthogonalFamily ℂ
      (fun μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (μ : ℂ))
      (fun μ =>
        (Module.End.eigenspace (unitaryRealLin U) (μ : ℂ)).subtypeₗᵢ) :=
    hSym.orthogonalFamily_eigenspaces'
  have hSigma_eq :
      unitaryJointSigmaBasis U hU =
        hInt.collectedOrthonormalBasis hOrth
          (fun μ => unitaryImagFiberBasis U hU μ) := rfl
  have hMem :
      unitaryJointSigmaBasis U hU
          ((unitaryJointIndexEquiv U hU).symm i) ∈
        Module.End.eigenspace (unitaryRealLin U)
          (((unitaryJointIndexEquiv U hU).symm i).1 : ℂ) := by
    have h :=
      DirectSum.IsInternal.collectedOrthonormalBasis_mem hInt hOrth
        (fun μ => unitaryImagFiberBasis U hU μ)
        ((unitaryJointIndexEquiv U hU).symm i)
    rw [← hSigma_eq] at h
    exact h
  rw [unitaryJointBasisIndex, hEq]
  exact hMem

private theorem unitaryRealLin_apply_unitaryJointBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (i : n) :
    unitaryRealLin U (unitaryJointBasis U hU i) =
      (unitaryJointBasisIndex U hU i : ℂ) •
        unitaryJointBasis U hU i := by
  have hMem :=
    unitaryJointBasis_mem_realEigenspace U hU i
  rw [Module.End.mem_eigenspace_iff] at hMem
  exact hMem

private theorem unitaryJointSigmaBasis_eq_fiber
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (s : unitaryJointIndexType U) :
    unitaryJointSigmaBasis U hU s =
      (unitaryImagFiberBasis U hU s.1 s.2 : EuclideanSpace ℂ n) := by
  let hSym := unitaryRealLin_isSymmetric U
  let hInt : DirectSum.IsInternal
      (fun _μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ)) :=
    hSym.direct_sum_isInternal
  let hOrth : OrthogonalFamily ℂ
      (fun _μ : Module.End.Eigenvalues (unitaryRealLin U) =>
        Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ))
      (fun _μ => (Module.End.eigenspace (unitaryRealLin U) (_μ : ℂ)).subtypeₗᵢ) :=
    hSym.orthogonalFamily_eigenspaces'
  have hToBasis :
      (hInt.collectedOrthonormalBasis hOrth
          (fun _μ => unitaryImagFiberBasis U hU _μ)).toBasis =
        hInt.collectedBasis
          (fun _μ => (unitaryImagFiberBasis U hU _μ).toBasis) := by
    unfold DirectSum.IsInternal.collectedOrthonormalBasis
    simp
  have h1 : unitaryJointSigmaBasis U hU s =
      (hInt.collectedOrthonormalBasis hOrth
        (fun _μ => unitaryImagFiberBasis U hU _μ)) s := rfl
  have h2 : (hInt.collectedOrthonormalBasis hOrth
      (fun _μ => unitaryImagFiberBasis U hU _μ)) s =
      (hInt.collectedOrthonormalBasis hOrth
        (fun _μ => unitaryImagFiberBasis U hU _μ)).toBasis s := by
    have hEq := OrthonormalBasis.coe_toBasis
      (hInt.collectedOrthonormalBasis hOrth
        (fun _μ => unitaryImagFiberBasis U hU _μ))
    exact (congrFun hEq.symm s)
  have h3 : (hInt.collectedOrthonormalBasis hOrth
      (fun _μ => unitaryImagFiberBasis U hU _μ)).toBasis s =
      (hInt.collectedBasis
        (fun _μ => (unitaryImagFiberBasis U hU _μ).toBasis)) s := by
    rw [hToBasis]
  have h4 : (hInt.collectedBasis
      (fun _μ => (unitaryImagFiberBasis U hU _μ).toBasis)) s =
      ((unitaryImagFiberBasis U hU s.1).toBasis s.2 :
        EuclideanSpace ℂ n) := by
    have hEq := DirectSum.IsInternal.collectedBasis_coe hInt
      (fun _μ => (unitaryImagFiberBasis U hU _μ).toBasis)
    exact congrFun hEq s
  have h5 : ((unitaryImagFiberBasis U hU s.1).toBasis s.2 :
      EuclideanSpace ℂ n) =
      (unitaryImagFiberBasis U hU s.1 s.2 :
        EuclideanSpace ℂ n) := by
    have hEq := OrthonormalBasis.coe_toBasis
      (unitaryImagFiberBasis U hU s.1)
    have hSub : (unitaryImagFiberBasis U hU s.1).toBasis s.2 =
        unitaryImagFiberBasis U hU s.1 s.2 :=
      congrFun hEq s.2
    rw [hSub]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

private theorem unitaryImagLin_apply_unitaryJointBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (i : n) :
    unitaryImagLin U (unitaryJointBasis U hU i) =
      ((unitaryImagLinRestrict_isSymmetric U hU
        (unitaryJointBasisIndex U hU i)).eigenvalues rfl
        ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ) •
        unitaryJointBasis U hU i := by
  let e := unitaryJointIndexEquiv U hU
  let s : unitaryJointIndexType U := e.symm i
  let μ : Module.End.Eigenvalues (unitaryRealLin U) := s.1
  let j : Fin (Module.finrank ℂ
      ↥(Module.End.eigenspace (unitaryRealLin U) (μ : ℂ))) := s.2
  have hIdx : unitaryJointBasisIndex U hU i = μ := rfl
  have hInner :
      ((unitaryJointIndexEquiv U hU).symm i).2 = j := rfl
  have hReindex :
      unitaryJointBasis U hU i =
        unitaryJointSigmaBasis U hU s := by
    calc unitaryJointBasis U hU i
        = ((unitaryJointSigmaBasis U hU).reindex e) i := rfl
      _ = unitaryJointSigmaBasis U hU (e.symm i) :=
          OrthonormalBasis.reindex_apply _ _ _
  have hFiber :
      unitaryJointSigmaBasis U hU s =
        (unitaryImagFiberBasis U hU s.1 s.2 :
          EuclideanSpace ℂ n) :=
    unitaryJointSigmaBasis_eq_fiber U hU s
  have hJointFiber :
      unitaryJointBasis U hU i =
        (unitaryImagFiberBasis U hU μ j :
          EuclideanSpace ℂ n) := by
    calc unitaryJointBasis U hU i
        = unitaryJointSigmaBasis U hU s := hReindex
      _ = (unitaryImagFiberBasis U hU s.1 s.2 :
          EuclideanSpace ℂ n) := hFiber
      _ = (unitaryImagFiberBasis U hU μ j :
          EuclideanSpace ℂ n) := rfl
  have hMem :=
    unitaryJointBasis_mem_realEigenspace U hU i
  let bv : ↥(Module.End.eigenspace (unitaryRealLin U)
      (μ : ℂ)) :=
    unitaryImagFiberBasis U hU μ j
  have hBvVal :
      (bv : EuclideanSpace ℂ n) =
        unitaryJointBasis U hU i := by
    calc (bv : EuclideanSpace ℂ n)
        = (unitaryImagFiberBasis U hU μ j :
          EuclideanSpace ℂ n) := rfl
      _ = unitaryJointBasis U hU i := hJointFiber.symm
  let z : ↥(Module.End.eigenspace (unitaryRealLin U)
      (μ : ℂ)) :=
    ⟨unitaryJointBasis U hU i, hMem⟩
  have hZeq : z = bv := by
    apply Subtype.ext
    calc (z : EuclideanSpace ℂ n)
        = unitaryJointBasis U hU i := rfl
      _ = (bv : EuclideanSpace ℂ n) := hBvVal.symm
  let hSym := unitaryImagLinRestrict_isSymmetric U hU μ
  have hApply :
      unitaryImagLinRestrict U hU μ bv =
        (hSym.eigenvalues rfl j : ℂ) • bv :=
    hSym.apply_eigenvectorBasis rfl j
  have hCoeRestrict :
      (unitaryImagLinRestrict U hU μ bv :
        EuclideanSpace ℂ n) =
        unitaryImagLin U (bv : EuclideanSpace ℂ n) := rfl
  have hCoeSmul :
      (↑((hSym.eigenvalues rfl j : ℂ) • bv) :
        EuclideanSpace ℂ n) =
        (hSym.eigenvalues rfl j : ℂ) •
          (bv : EuclideanSpace ℂ n) := rfl
  calc unitaryImagLin U (unitaryJointBasis U hU i)
      = unitaryImagLin U (bv : EuclideanSpace ℂ n) := by
        rw [hBvVal]
    _ = (unitaryImagLinRestrict U hU μ bv :
          EuclideanSpace ℂ n) := hCoeRestrict.symm
    _ = (↑((hSym.eigenvalues rfl j : ℂ) • bv) :
          EuclideanSpace ℂ n) := by
        rw [hApply]
    _ = (hSym.eigenvalues rfl j : ℂ) •
        (bv : EuclideanSpace ℂ n) := hCoeSmul
    _ = (hSym.eigenvalues rfl j : ℂ) •
        unitaryJointBasis U hU i := by
          rw [hBvVal]
    _ = ((unitaryImagLinRestrict_isSymmetric U hU
          (unitaryJointBasisIndex U hU i)).eigenvalues rfl
          ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ) •
        unitaryJointBasis U hU i := rfl

private noncomputable def unitaryJointPhase (U : Matrix n n ℂ)
    (hU : U ∈ unitaryGroup n ℂ) (i : n) : ℂ :=
  (unitaryJointBasisIndex U hU i : ℂ) +
    Complex.I *
      ((unitaryImagLinRestrict_isSymmetric U hU
          (unitaryJointBasisIndex U hU i)).eigenvalues rfl
        ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ)

private theorem unitaryLin_apply_unitaryJointBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (i : n) :
    Matrix.toEuclideanLin U (unitaryJointBasis U hU i) =
      unitaryJointPhase U hU i • unitaryJointBasis U hU i := by
  have hU_eq :
      U = unitaryRealPart U + Complex.I • unitaryImagPart U :=
    unitary_eq_realPart_add_I_smul_imagPart U
  have hLin :
      Matrix.toEuclideanLin U =
        unitaryRealLin U + Complex.I • unitaryImagLin U := by
    calc Matrix.toEuclideanLin U
        = Matrix.toEuclideanLin
            (unitaryRealPart U + Complex.I • unitaryImagPart U) := by
          rw [← hU_eq]
      _ = Matrix.toEuclideanLin (unitaryRealPart U) +
            Matrix.toEuclideanLin
              (Complex.I • unitaryImagPart U) := by
          rw [map_add]
      _ = Matrix.toEuclideanLin (unitaryRealPart U) +
            Complex.I • Matrix.toEuclideanLin (unitaryImagPart U) := by
          rw [LinearEquiv.map_smul]
      _ = unitaryRealLin U + Complex.I • unitaryImagLin U := rfl
  calc Matrix.toEuclideanLin U (unitaryJointBasis U hU i)
      = (unitaryRealLin U + Complex.I • unitaryImagLin U)
          (unitaryJointBasis U hU i) := by
        rw [hLin]
    _ = unitaryRealLin U (unitaryJointBasis U hU i) +
          Complex.I • unitaryImagLin U (unitaryJointBasis U hU i) := by
        rw [LinearMap.add_apply, LinearMap.smul_apply]
    _ = (unitaryJointBasisIndex U hU i : ℂ) •
            unitaryJointBasis U hU i +
          Complex.I •
            (((unitaryImagLinRestrict_isSymmetric U hU
              (unitaryJointBasisIndex U hU i)).eigenvalues rfl
                ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ) •
              unitaryJointBasis U hU i) := by
        rw [unitaryRealLin_apply_unitaryJointBasis,
          unitaryImagLin_apply_unitaryJointBasis]
    _ = (unitaryJointBasisIndex U hU i : ℂ) •
            unitaryJointBasis U hU i +
          (Complex.I *
              ((unitaryImagLinRestrict_isSymmetric U hU
                (unitaryJointBasisIndex U hU i)).eigenvalues rfl
                ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ)) •
            unitaryJointBasis U hU i := by
        rw [smul_smul]
    _ = ((unitaryJointBasisIndex U hU i : ℂ) +
            Complex.I *
              ((unitaryImagLinRestrict_isSymmetric U hU
                (unitaryJointBasisIndex U hU i)).eigenvalues rfl
                ((unitaryJointIndexEquiv U hU).symm i).2 : ℂ)) •
          unitaryJointBasis U hU i := by
        rw [add_smul]
    _ = unitaryJointPhase U hU i • unitaryJointBasis U hU i := rfl

end JointIndex

section NormPreservation

variable [Fintype n] [DecidableEq n]

private theorem unitaryLin_norm
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin U x‖ = ‖x‖ := by
  have hCU : Matrix.conjTranspose U * U = 1 := by
    have hStar : star U * U = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hU
    rw [Matrix.star_eq_conjTranspose] at hStar
    exact hStar
  have hAdj : (Matrix.toEuclideanLin U).adjoint =
      Matrix.toEuclideanLin (Matrix.conjTranspose U) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hMul : Matrix.toEuclideanLin (Matrix.conjTranspose U * U) =
      Matrix.toEuclideanLin (Matrix.conjTranspose U) *
        Matrix.toEuclideanLin U := by
    calc Matrix.toEuclideanLin (Matrix.conjTranspose U * U)
        = Matrix.toLpLin 2 2 (Matrix.conjTranspose U * U) := rfl
      _ = Matrix.toLpLin 2 2 (Matrix.conjTranspose U) ∘ₗ
            Matrix.toLpLin 2 2 U := by
          rw [Matrix.toLpLin_mul_same]
      _ = Matrix.toEuclideanLin (Matrix.conjTranspose U) *
            Matrix.toEuclideanLin U := by
          rw [← Module.End.mul_eq_comp]
  have hAdjMul :
      (Matrix.toEuclideanLin U).adjoint * Matrix.toEuclideanLin U = 1 := by
    calc (Matrix.toEuclideanLin U).adjoint * Matrix.toEuclideanLin U
        = Matrix.toEuclideanLin (Matrix.conjTranspose U) *
            Matrix.toEuclideanLin U := by
          rw [hAdj]
      _ = Matrix.toEuclideanLin (Matrix.conjTranspose U * U) := by
          rw [← hMul]
      _ = Matrix.toEuclideanLin (1 : Matrix n n ℂ) := by
          rw [hCU]
      _ = LinearMap.id := by
          simp
      _ = 1 := rfl
  have hInner : ∀ y z : EuclideanSpace ℂ n,
      ⟪Matrix.toEuclideanLin U y, Matrix.toEuclideanLin U z⟫_ℂ =
        ⟪y, z⟫_ℂ := by
    intro y z
    have hPoint :
        (Matrix.toEuclideanLin U).adjoint
          ((Matrix.toEuclideanLin U) y) = y := by
      have h1 : (Matrix.toEuclideanLin U).adjoint
          ((Matrix.toEuclideanLin U) y) =
          ((Matrix.toEuclideanLin U).adjoint *
            Matrix.toEuclideanLin U) y := by
        rw [Module.End.mul_apply]
      calc (Matrix.toEuclideanLin U).adjoint ((Matrix.toEuclideanLin U) y)
          = ((Matrix.toEuclideanLin U).adjoint *
              Matrix.toEuclideanLin U) y := h1
        _ = (1 : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) y := by
            rw [hAdjMul]
        _ = y := rfl
    calc ⟪Matrix.toEuclideanLin U y, Matrix.toEuclideanLin U z⟫_ℂ
        = ⟪(Matrix.toEuclideanLin U).adjoint ((Matrix.toEuclideanLin U) y), z⟫_ℂ := by
          rw [← LinearMap.adjoint_inner_left]
      _ = ⟪y, z⟫_ℂ := by
          rw [hPoint]
  have hNorm : ∀ w : EuclideanSpace ℂ n,
      ‖Matrix.toEuclideanLin U w‖ = ‖w‖ := by
    have hIff :=
      LinearMap.norm_map_iff_inner_map_map
        (𝕜 := ℂ) (Matrix.toEuclideanLin U)
    rw [hIff]
    exact hInner
  exact hNorm x

private theorem unitaryJointPhase_norm
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) (i : n) :
    ‖unitaryJointPhase U hU i‖ = 1 := by
  have hBasisOne : ‖unitaryJointBasis U hU i‖ = 1 :=
    (unitaryJointBasis U hU).norm_eq_one i
  calc ‖unitaryJointPhase U hU i‖
      = ‖unitaryJointPhase U hU i‖ * ‖unitaryJointBasis U hU i‖ := by
        rw [hBasisOne, mul_one]
    _ = ‖unitaryJointPhase U hU i • unitaryJointBasis U hU i‖ := by
        rw [norm_smul]
    _ = ‖Matrix.toEuclideanLin U (unitaryJointBasis U hU i)‖ := by
        rw [unitaryLin_apply_unitaryJointBasis]
    _ = ‖unitaryJointBasis U hU i‖ := unitaryLin_norm U hU _
    _ = 1 := hBasisOne

private noncomputable def unitaryJointMatrix
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) : Matrix n n ℂ :=
  (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix
    (unitaryJointBasis U hU).toBasis

private theorem unitaryJointMatrix_mem_unitaryGroup
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    unitaryJointMatrix U hU ∈ Matrix.unitaryGroup n ℂ :=
  OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun n ℂ) (unitaryJointBasis U hU)

private theorem unitaryJointMatrix_col_eq
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (j : n) :
    Matrix.col (unitaryJointMatrix U hU) j =
      ⇑(unitaryJointBasis U hU j) :=
  rfl

private theorem unitary_mulVec_unitaryJointBasis
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) (j : n) :
    U *ᵥ ⇑(unitaryJointBasis U hU j) =
      unitaryJointPhase U hU j • ⇑(unitaryJointBasis U hU j) := by
  have h := unitaryLin_apply_unitaryJointBasis U hU j
  have h' := congrArg WithLp.ofLp h
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_smul] at h'
  exact h'

private theorem unitary_mul_unitaryJointMatrix
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    U * unitaryJointMatrix U hU =
      unitaryJointMatrix U hU * diagonal (unitaryJointPhase U hU) := by
  ext i j
  have hCol : (unitaryJointMatrix U hU).col j = ⇑(unitaryJointBasis U hU j) :=
    unitaryJointMatrix_col_eq U hU j
  have hMul : U *ᵥ ⇑(unitaryJointBasis U hU j) =
      unitaryJointPhase U hU j • ⇑(unitaryJointBasis U hU j) :=
    unitary_mulVec_unitaryJointBasis U hU j
  have hColEq : (unitaryJointMatrix U hU).col j i =
      ((unitaryJointBasis U hU j : EuclideanSpace ℂ n) i) := by
    rw [hCol]
  have hColApply : (unitaryJointMatrix U hU).col j i =
      unitaryJointMatrix U hU i j := by
    rw [Matrix.col_apply]
  calc (U * unitaryJointMatrix U hU) i j
      = (U *ᵥ (unitaryJointMatrix U hU).col j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Matrix.col_apply]
      _ = (U *ᵥ ⇑(unitaryJointBasis U hU j)) i := by
        rw [hCol]
      _ = (unitaryJointPhase U hU j • ⇑(unitaryJointBasis U hU j)) i := by
        rw [hMul]
      _ = unitaryJointPhase U hU j * ((unitaryJointBasis U hU j : EuclideanSpace ℂ n) i) := by
        simp [Pi.smul_apply, smul_eq_mul]
      _ = ((unitaryJointBasis U hU j : EuclideanSpace ℂ n) i) *
          unitaryJointPhase U hU j := by
        rw [mul_comm]
      _ = (unitaryJointMatrix U hU i j) * unitaryJointPhase U hU j := by
        rw [← hColEq, hColApply]
      _ = (unitaryJointMatrix U hU * diagonal (unitaryJointPhase U hU)) i j := by
        rw [Matrix.mul_diagonal]

private theorem unitary_eq_unitaryJointMatrix_diagonalization
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    U = unitaryJointMatrix U hU * diagonal (unitaryJointPhase U hU) *
      (unitaryJointMatrix U hU)ᴴ := by
  let V := unitaryJointMatrix U hU
  have hV : V ∈ unitaryGroup n ℂ := unitaryJointMatrix_mem_unitaryGroup U hU
  have hV_mul_star : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hUV : U * V = V * diagonal (unitaryJointPhase U hU) :=
    unitary_mul_unitaryJointMatrix U hU
  have hStar : star V = Vᴴ := by
    rw [Matrix.star_eq_conjTranspose]
  calc U = U * 1 := by rw [Matrix.mul_one]
    _ = U * (V * star V) := by rw [← hV_mul_star]
    _ = U * V * star V := by rw [← Matrix.mul_assoc]
    _ = V * diagonal (unitaryJointPhase U hU) * star V := by rw [hUV]
    _ = V * diagonal (unitaryJointPhase U hU) * Vᴴ := by rw [hStar]

public theorem exists_unitary_diagonalization_of_mem_unitaryGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    ∃ V : Matrix n n ℂ, V ∈ unitaryGroup n ℂ ∧
      ∃ d : n → ℂ, (∀ i, ‖d i‖ = 1) ∧ U = V * diagonal d * Vᴴ := by
  refine ⟨unitaryJointMatrix U hU, unitaryJointMatrix_mem_unitaryGroup U hU,
    unitaryJointPhase U hU, ?_, ?_⟩
  · intro i
    exact unitaryJointPhase_norm U hU i
  · exact unitary_eq_unitaryJointMatrix_diagonalization U hU

end NormPreservation

end Matrix
