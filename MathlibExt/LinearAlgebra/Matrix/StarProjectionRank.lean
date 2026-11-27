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

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank classification of complex star projections

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. The
columns satisfy E_PᴴE_P=I_r. If P=Pᴴ=P², they reconstruct P=E_PE_Pᴴ. Two square complex star
projections in different sizes are rectangularly equivalent by P=UᴴU,Q=UUᴴ precisely when
rank(P)=rank(Q).
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace Matrix

namespace Matrix

noncomputable section

variable {n m : ℕ}

private theorem cStarMatrix_mul_assoc
    {l m n k : Type*} [Fintype m] [Fintype n]
    (A : CStarMatrix l m ℂ) (B : CStarMatrix m n ℂ)
    (C : CStarMatrix n k ℂ) :
    (A * B) * C = A * (B * C) :=
  Matrix.mul_assoc A B C

private theorem cStarMatrix_one_mul
    {l m : Type*} [Fintype l] [DecidableEq l]
    (A : CStarMatrix l m ℂ) :
    (1 : CStarMatrix l l ℂ) * A = A := by
  apply CStarMatrix.ext
  intro i j
  simp [CStarMatrix.mul_apply, CStarMatrix.one_apply]

/-- **Rank-indexed orthonormal basis of a matrix range.**

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. The
value starProjectionRangeBasis P is an orthonormal basis of range(P:ℂ^n→ℂ^n), indexed by Fin
r.
-/
noncomputable def starProjectionRangeBasis
    (P : CStarMatrix (Fin n) (Fin n) ℂ) :
    OrthonormalBasis
      (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) ℂ
      (LinearMap.range
        (Matrix.toLin
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (CStarMatrix.ofMatrix.symm P))) := by
  let M : Matrix (Fin n) (Fin n) ℂ := CStarMatrix.ofMatrix.symm P
  let T := Matrix.toLin
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis M
  have hrank :
      Module.finrank ℂ (LinearMap.range T) = Matrix.rank M := by
    symm
    exact (Matrix.rank_eq_finrank_range_toLin M
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
  exact (stdOrthonormalBasis ℂ (LinearMap.range T)).reindex
    (finCongr hrank)

/-- **Isometric inclusion of matrix range coordinates.**

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. The
linear isometry starProjectionRangeIsometry P:ℂ^r→ℂ^n sends the standard coordinate basis to
that orthonormal range basis.
-/
noncomputable def starProjectionRangeIsometry
    (P : CStarMatrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ
        (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n) :=
  (LinearMap.range
      (Matrix.toLin
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (CStarMatrix.ofMatrix.symm P))).subtypeₗᵢ.comp
    (starProjectionRangeBasis P).repr.symm.toLinearIsometry

private theorem starProjectionRangeIsometry_range
    (P : CStarMatrix (Fin n) (Fin n) ℂ) :
    LinearMap.range (starProjectionRangeIsometry P).toLinearMap =
      LinearMap.range
        (Matrix.toLin
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (CStarMatrix.ofMatrix.symm P)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ((starProjectionRangeBasis P).repr.symm x).property
  · intro y hy
    refine ⟨(starProjectionRangeBasis P).repr ⟨y, hy⟩, ?_⟩
    change
      (((starProjectionRangeBasis P).repr.symm
        ((starProjectionRangeBasis P).repr ⟨y, hy⟩) :
          LinearMap.range
            (Matrix.toLin
              (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
              (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
              (CStarMatrix.ofMatrix.symm P))) :
        EuclideanSpace ℂ (Fin n)) = y
    rw [(starProjectionRangeBasis P).repr.symm_apply_apply]

/-- **Rectangular orthonormal frame of a matrix range.**

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. The
matrix starProjectionRangeFrame P is E_P, with columns that orthonormal basis of range(P).
-/
noncomputable def starProjectionRangeFrame
    (P : CStarMatrix (Fin n) (Fin n) ℂ) :
    CStarMatrix (Fin n)
      (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) ℂ :=
  CStarMatrix.ofMatrix <|
    LinearMap.toMatrix
      (EuclideanSpace.basisFun
        (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (starProjectionRangeIsometry P).toLinearMap

/-- **Identity Gram matrix of the range frame.**

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. For
every P, starProjectionRangeFrame P satisfies E_PᴴE_P=I_r.
-/
@[simp]
theorem starProjectionRangeFrame_conjTranspose_mul_self
    (P : CStarMatrix (Fin n) (Fin n) ℂ) :
    CStarMatrix.conjTranspose (starProjectionRangeFrame P) *
        starProjectionRangeFrame P = 1 := by
  let br := EuclideanSpace.basisFun
    (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) ℂ
  let bn := EuclideanSpace.basisFun (Fin n) ℂ
  let L := starProjectionRangeIsometry P
  change
    (LinearMap.toMatrix br.toBasis bn.toBasis L.toLinearMap)ᴴ *
        LinearMap.toMatrix br.toBasis bn.toBasis L.toLinearMap = 1
  rw [← LinearMap.toMatrix_adjoint br bn L.toLinearMap]
  rw [← LinearMap.toMatrix_comp br.toBasis bn.toBasis br.toBasis]
  rw [L.adjoint_comp_self']
  exact LinearMap.toMatrix_id br.toBasis

/-- **Range frame reconstructs a star projection.**

Let P be an n×n complex matrix, represented in CStarMatrix, and r=rank(P). Its Euclidean range
has a rank-indexed orthonormal basis; let E_P be the n×r matrix of those basis columns. If P
is a star projection, P=Pᴴ=P², then E_PE_Pᴴ=P.
-/
@[simp]
theorem IsStarProjection.starProjectionRangeFrame_mul_conjTranspose
    {P : CStarMatrix (Fin n) (Fin n) ℂ} (hP : IsStarProjection P) :
    starProjectionRangeFrame P *
        CStarMatrix.conjTranspose (starProjectionRangeFrame P) = P := by
  let M : Matrix (Fin n) (Fin n) ℂ := CStarMatrix.ofMatrix.symm P
  let bn := EuclideanSpace.basisFun (Fin n) ℂ
  let br := EuclideanSpace.basisFun
    (Fin (Matrix.rank M)) ℂ
  let T := Matrix.toLin bn.toBasis bn.toBasis M
  let L := starProjectionRangeIsometry P
  let S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    L.toLinearMap.comp L.toLinearMap.adjoint
  have hM : IsStarProjection M := hP
  have hTstar : IsStarProjection T := by
    change IsStarProjection ((LinearMap.toMatrixOrthonormal bn).symm M)
    exact hM.map (LinearMap.toMatrixOrthonormal bn).symm
  have hT : T.IsSymmetricProjection :=
    LinearMap.isStarProjection_iff_isSymmetricProjection.mp hTstar
  have hS : S.IsSymmetricProjection := {
    isIdempotentElem := by
      rw [IsIdempotentElem]
      apply LinearMap.ext
      intro x
      change L.toLinearMap
          (L.toLinearMap.adjoint
            (L.toLinearMap (L.toLinearMap.adjoint x))) =
        L.toLinearMap (L.toLinearMap.adjoint x)
      have h := DFunLike.congr_fun L.adjoint_comp_self'
        (L.toLinearMap.adjoint x)
      exact congrArg L.toLinearMap h
    isSymmetric := by
      exact LinearMap.isSymmetric_self_comp_adjoint L.toLinearMap }
  have hST : S = T := by
    apply hS.ext hT
    rw [LinearMap.range_self_comp_adjoint]
    exact starProjectionRangeIsometry_range P
  change
    LinearMap.toMatrix br.toBasis bn.toBasis L.toLinearMap *
        (LinearMap.toMatrix br.toBasis bn.toBasis L.toLinearMap)ᴴ = M
  rw [← LinearMap.toMatrix_adjoint br bn L.toLinearMap]
  rw [← LinearMap.toMatrix_comp bn.toBasis br.toBasis bn.toBasis]
  rw [show L.toLinearMap.comp L.toLinearMap.adjoint = T from hST]
  simp [T, M]

/-- **Rectangular frame for a finite star projection.**

Let P∈CStarMatrix(Fin n,Fin n,ℂ) be a star projection and r=rank(P). There exists
E∈CStarMatrix(Fin n,Fin r,ℂ) with EᴴE=I_r and EEᴴ=P.
-/
theorem IsStarProjection.exists_rangeFrame
    {P : CStarMatrix (Fin n) (Fin n) ℂ} (hP : IsStarProjection P) :
    ∃ E : CStarMatrix (Fin n)
        (Fin (Matrix.rank (CStarMatrix.ofMatrix.symm P))) ℂ,
      CStarMatrix.conjTranspose E * E = 1 ∧
        E * CStarMatrix.conjTranspose E = P :=
  ⟨starProjectionRangeFrame P,
    starProjectionRangeFrame_conjTranspose_mul_self P,
    Matrix.IsStarProjection.starProjectionRangeFrame_mul_conjTranspose hP⟩

/-- **Range frame at a prescribed rank-sized index.**

Let P be an n×n complex star projection, r∈ℕ and rank(P)=r. There exists an n×r complex matrix
E with EᴴE=I_r and EEᴴ=P, including r=0.
-/
theorem IsStarProjection.exists_rangeFrame_of_rank_eq
    {P : CStarMatrix (Fin n) (Fin n) ℂ} (hP : IsStarProjection P)
    (r : ℕ) (hr : Matrix.rank (CStarMatrix.ofMatrix.symm P) = r) :
    ∃ E : CStarMatrix (Fin n) (Fin r) ℂ,
      CStarMatrix.conjTranspose E * E = 1 ∧
        E * CStarMatrix.conjTranspose E = P := by
  subst r
  exact Matrix.IsStarProjection.exists_rangeFrame hP

/-- **Ranks of the two rectangular Gram matrices agree.**

Let U be an m×n complex matrix, P=UᴴU and Q=UUᴴ. Then rank(P)=rank(Q); P,Q need not be assumed
projections for this rank identity.
-/
theorem rank_eq_of_rectangular_partialIsometry
    {P : CStarMatrix (Fin n) (Fin n) ℂ}
    {Q : CStarMatrix (Fin m) (Fin m) ℂ}
    {U : CStarMatrix (Fin m) (Fin n) ℂ}
    (hP : P = CStarMatrix.conjTranspose U * U)
    (hQ : Q = U * CStarMatrix.conjTranspose U) :
    Matrix.rank (CStarMatrix.ofMatrix.symm P) =
      Matrix.rank (CStarMatrix.ofMatrix.symm Q) := by
  rw [hP, hQ]
  exact (Matrix.rank_conjTranspose_mul_self
    (CStarMatrix.ofMatrix.symm U)).trans
      (Matrix.rank_self_mul_conjTranspose
        (CStarMatrix.ofMatrix.symm U)).symm

/-- **Rectangular equivalence of star projections is equality of rank.**

Let P,Q be complex star projections of sizes n×n and m×m. Then there exists U:m×n→ℂ with P=UᴴU
and Q=UUᴴ if and only if rank(P)=rank(Q).
-/
theorem isStarProjection_rectangularEquiv_iff_rank_eq
    {P : CStarMatrix (Fin n) (Fin n) ℂ}
    {Q : CStarMatrix (Fin m) (Fin m) ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (∃ U : CStarMatrix (Fin m) (Fin n) ℂ,
        P = CStarMatrix.conjTranspose U * U ∧
          Q = U * CStarMatrix.conjTranspose U) ↔
      Matrix.rank (CStarMatrix.ofMatrix.symm P) =
        Matrix.rank (CStarMatrix.ofMatrix.symm Q) := by
  constructor
  · rintro ⟨U, hPU, hQU⟩
    exact rank_eq_of_rectangular_partialIsometry hPU hQU
  · intro hrank
    obtain ⟨EP, hEPGram, hEPRange⟩ :=
      Matrix.IsStarProjection.exists_rangeFrame hP
    obtain ⟨EQ, hEQGram, hEQRange⟩ :=
      Matrix.IsStarProjection.exists_rangeFrame_of_rank_eq hQ
        (Matrix.rank (CStarMatrix.ofMatrix.symm P)) hrank.symm
    refine ⟨EQ * CStarMatrix.conjTranspose EP, ?_, ?_⟩
    · rw [show CStarMatrix.conjTranspose
          (EQ * CStarMatrix.conjTranspose EP) =
            EP * CStarMatrix.conjTranspose EQ by
        apply CStarMatrix.ext
        intro i j
        simp [CStarMatrix.conjTranspose_apply, CStarMatrix.mul_apply,
          star_sum, star_mul]]
      symm
      calc
        (EP * CStarMatrix.conjTranspose EQ) *
            (EQ * CStarMatrix.conjTranspose EP) =
          EP * (CStarMatrix.conjTranspose EQ *
            (EQ * CStarMatrix.conjTranspose EP)) :=
          cStarMatrix_mul_assoc _ _ _
        _ = EP * ((CStarMatrix.conjTranspose EQ * EQ) *
            CStarMatrix.conjTranspose EP) :=
          congrArg (fun X ↦ EP * X)
            (cStarMatrix_mul_assoc
              (CStarMatrix.conjTranspose EQ) EQ
              (CStarMatrix.conjTranspose EP)).symm
        _ = EP * CStarMatrix.conjTranspose EP := by
          rw [hEQGram, cStarMatrix_one_mul]
        _ = P := hEPRange
    · rw [show CStarMatrix.conjTranspose
          (EQ * CStarMatrix.conjTranspose EP) =
            EP * CStarMatrix.conjTranspose EQ by
        apply CStarMatrix.ext
        intro i j
        simp [CStarMatrix.conjTranspose_apply, CStarMatrix.mul_apply,
          star_sum, star_mul]]
      symm
      calc
        (EQ * CStarMatrix.conjTranspose EP) *
            (EP * CStarMatrix.conjTranspose EQ) =
          EQ * (CStarMatrix.conjTranspose EP *
            (EP * CStarMatrix.conjTranspose EQ)) :=
          cStarMatrix_mul_assoc _ _ _
        _ = EQ * ((CStarMatrix.conjTranspose EP * EP) *
            CStarMatrix.conjTranspose EQ) :=
          congrArg (fun X ↦ EQ * X)
            (cStarMatrix_mul_assoc
              (CStarMatrix.conjTranspose EP) EP
              (CStarMatrix.conjTranspose EQ)).symm
        _ = EQ * CStarMatrix.conjTranspose EQ := by
          rw [hEPGram, cStarMatrix_one_mul]
        _ = Q := hEQRange

end


end Matrix
