/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockSum
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ElementaryConjugation
public import MathlibExt.KTheory.Ring.StableGeneralLinear.StabilizeTo
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
import Mathlib.Tactic.FinCases

/-!
# Actual finite elementary unit conjugators for stable block sum

The existing matrix diagram has a fixed enumeration of the two coefficient
slots. At every finite stage, an explicit permutation takes the ordered
first block to that SAME interleaved first slot. Doubling its permutation
unit as diag(q,q⁻¹) gives an actual stable elementary conjugator. The whole
finite general-linear group, not only a selected loop, satisfies the unit
conjugation equation. No finite-stage matrix choice is an input.
-/

set_option autoImplicit false

noncomputable section

open Matrix CategoryTheory

universe u

namespace AlgebraicKTheory.StableGL

private def blockPairSumEquiv (n : ℕ) :
    Fin n ⊕ Fin n ≃ Fin n × BlockPairIndex.{u} where
  toFun p := match p with
    | Sum.inl i => (i, ULift.up 0)
    | Sum.inr i => (i, ULift.up 1)
  invFun p := if p.2.down = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv p := by
    rcases p with i | i <;> simp
  right_inv p := by
    rcases p with ⟨i, ⟨k⟩⟩
    fin_cases k <;> rfl

private theorem blockPairSumEquiv_inl (n : ℕ) (i : Fin n) :
    blockPairSumEquiv.{u} n (Sum.inl i) = (i, ULift.up 0) := rfl

private theorem blockPairSumEquiv_inr (n : ℕ) (i : Fin n) :
    blockPairSumEquiv.{u} n (Sum.inr i) = (i, ULift.up 1) := rfl

private theorem blockPairSize (n : ℕ) :
    n + n = n * Fintype.card BlockPairIndex.{u} := by
  simp [BlockPairIndex, Nat.mul_two]

private def orderedBlockIndex (n : ℕ) :
    Fin n ⊕ Fin n ≃ Fin (n * Fintype.card BlockPairIndex.{u}) :=
  (finSumFinEquiv (m := n) (n := n)).trans (finCongr (blockPairSize.{u} n))

private def interleavedBlockIndex (n : ℕ) :
    Fin n ⊕ Fin n ≃ Fin (n * Fintype.card BlockPairIndex.{u}) :=
  (blockPairSumEquiv.{u} n).trans
    (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n)

private theorem interleavedBlockIndex_inl (n : ℕ) (i : Fin n) :
    interleavedBlockIndex.{u} n (Sum.inl i) =
      MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, ULift.up 0) := rfl

private theorem interleavedBlockIndex_inr (n : ℕ) (i : Fin n) :
    interleavedBlockIndex.{u} n (Sum.inr i) =
      MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, ULift.up 1) := rfl

private def interleavingPermutation (n : ℕ) :
    Equiv.Perm (Fin (n * Fintype.card BlockPairIndex.{u})) :=
  (orderedBlockIndex.{u} n).symm.trans (interleavedBlockIndex.{u} n)

private theorem orderedBlockIndex_trans_interleaving (n : ℕ) :
    (orderedBlockIndex.{u} n).trans (interleavingPermutation.{u} n) =
      interleavedBlockIndex.{u} n := by
  apply Equiv.ext
  intro p
  change interleavedBlockIndex.{u} n
    ((orderedBlockIndex.{u} n).symm ((orderedBlockIndex.{u} n) p)) =
      interleavedBlockIndex.{u} n p
  exact congrArg (interleavedBlockIndex.{u} n)
    ((orderedBlockIndex.{u} n).symm_apply_apply p)

variable (R : Type u) [Ring R]

private theorem reindex_trans_apply
    {Index₁ Index₂ Index₃ : Type*}
    [DecidableEq Index₁] [DecidableEq Index₂] [DecidableEq Index₃]
    [Fintype Index₁] [Fintype Index₂] [Fintype Index₃]
    (e₁ : Index₁ ≃ Index₂) (e₂ : Index₂ ≃ Index₃)
    (g : Matrix.GeneralLinearGroup Index₁ R) :
    Matrix.GeneralLinearGroup.reindexMulEquiv e₂
        (Matrix.GeneralLinearGroup.reindexMulEquiv e₁ g) =
      Matrix.GeneralLinearGroup.reindexMulEquiv (e₁.trans e₂) g := by
  apply Units.ext
  have h := congrArg (fun e : Matrix Index₁ Index₁ R ≃ Matrix Index₃ Index₃ R =>
    e (g : Matrix Index₁ Index₁ R)) (Matrix.reindex_trans e₁ e₁ e₂ e₂)
  simpa only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
    Equiv.trans_apply] using h

private theorem of_finCongr {m n : ℕ} (h : m = n)
    (g : Matrix.GeneralLinearGroup (Fin m) R) :
    StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr h) g) =
      StableGL.of g :=
  StableGL.of_reindex_finCongr h g

private theorem finiteLeftBlock_eq_interleaved (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteBlockSumHom R n (g, 1) =
      Matrix.GeneralLinearGroup.reindexMulEquiv (interleavedBlockIndex.{u} n)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g) := by
  apply Units.ext
  apply Matrix.ext
  intro x y
  obtain ⟨a, rfl⟩ := (interleavedBlockIndex.{u} n).surjective x
  obtain ⟨b, rfl⟩ := (interleavedBlockIndex.{u} n).surjective y
  rw [Matrix.GeneralLinearGroup.coe_reindexMulEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.GeneralLinearGroup.coe_blockDiagonalOne]
  rcases a with i | i <;> rcases b with j | j
  · have h := finiteBlockSumHom_coefficients R n g 1 i j
      (ULift.up 0) (ULift.up 0)
    simpa only [interleavedBlockIndex_inl, Matrix.fromBlocks_apply₁₁,
      ite_eq_left rfl, ite_true] using h
  · have h := finiteBlockSumHom_coefficients R n g 1 i j
      (ULift.up 0) (ULift.up 1)
    simpa [interleavedBlockIndex_inl, interleavedBlockIndex_inr,
      Matrix.fromBlocks_apply₁₂] using h
  · have h := finiteBlockSumHom_coefficients R n g 1 i j
      (ULift.up 1) (ULift.up 0)
    simpa [interleavedBlockIndex_inl, interleavedBlockIndex_inr,
      Matrix.fromBlocks_apply₂₁] using h
  · have h := finiteBlockSumHom_coefficients R n g 1 i j
      (ULift.up 1) (ULift.up 1)
    simpa [interleavedBlockIndex_inr, Matrix.fromBlocks_apply₂₂] using h

private theorem orderedPrefix_stable (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv (orderedBlockIndex.{u} n)
      (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g)) =
      StableGL.of g := by
  rw [orderedBlockIndex, ← reindex_trans_apply R]
  change StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv
    (finCongr (blockPairSize.{u} n))
    (Matrix.GeneralLinearGroup.blockStabilization n n R g)) = StableGL.of g
  exact (of_finCongr R _ _).trans (StableGL.of_blockStabilization g)

private def leftInterleavingUnit (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin (n * Fintype.card BlockPairIndex.{u})) R :=
  Matrix.GeneralLinearGroup.permutationUnitsHom R _ (interleavingPermutation.{u} n)

private theorem leftInterleavingUnit_conjugates (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    leftInterleavingUnit R n *
        Matrix.GeneralLinearGroup.reindexMulEquiv (orderedBlockIndex.{u} n)
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g) *
        (leftInterleavingUnit R n)⁻¹ = finiteBlockSumHom R n (g, 1) := by
  rw [leftInterleavingUnit, Matrix.GeneralLinearGroup.permutationUnitsHom_conjugate,
    reindex_trans_apply R, orderedBlockIndex_trans_interleaving]
  exact (finiteLeftBlock_eq_interleaved R n g).symm

private theorem blockSumLeftHom_of (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    blockSumLeftHom R (StableGL.of g) = StableGL.of (finiteBlockSumHom R n (g, 1)) := by
  rw [blockSumLeftHom_apply]
  exact (congrArg (fun h : StableGL R => blockSumHom R (StableGL.of g, h))
    (StableGL.of_one (n := n) (R := R)).symm).trans
      (blockSumHom_of_pair R g 1)

/-- The original finite permutation swaps the two coefficient slots
through the actual matrix-flattening index. -/
public def swapBlockPermutation (n : ℕ) :
    Equiv.Perm (Fin (n * Fintype.card BlockPairIndex.{u})) :=
  (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n).symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin n))
      (Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)))).trans
        (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n))

/-- The original block swap exchanges the two complete coefficient slots
through the unchanged matrix-flattening index. -/
public theorem swapBlockPermutation_apply (n : ℕ) (i : Fin n)
    (k : BlockPairIndex.{u}) :
    swapBlockPermutation.{u} n
      (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, k)) =
      MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n
        (i, Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) k) := by
  simp [swapBlockPermutation]

private theorem swapBlockPermutation_symm_flat (n : ℕ) (i : Fin n)
    (k : BlockPairIndex.{u}) :
    (swapBlockPermutation.{u} n).symm
        (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, k)) =
      MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n
        (i, Equiv.swap (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) k) := by
  simp [swapBlockPermutation]

private def swapBlockUnit (n : ℕ) :
    Matrix.GeneralLinearGroup (Fin (n * Fintype.card BlockPairIndex.{u})) R :=
  Matrix.GeneralLinearGroup.permutationUnitsHom R _ (swapBlockPermutation.{u} n)

private theorem swapBlockUnit_conjugates (n : ℕ)
    (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    swapBlockUnit R n * finiteBlockSumHom R n (g, h) * (swapBlockUnit R n)⁻¹ =
      finiteBlockSumHom R n (h, g) := by
  rw [swapBlockUnit, Matrix.GeneralLinearGroup.permutationUnitsHom_conjugate]
  apply Units.ext
  apply Matrix.ext
  intro x y
  obtain ⟨⟨i, k⟩, rfl⟩ :=
    (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n).surjective x
  obtain ⟨⟨j, l⟩, rfl⟩ :=
    (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n).surjective y
  rw [Matrix.GeneralLinearGroup.coe_reindexMulEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, swapBlockPermutation_symm_flat, swapBlockPermutation_symm_flat,
    finiteBlockSumHom_coefficients, finiteBlockSumHom_coefficients]
  rcases k with ⟨k⟩
  rcases l with ⟨l⟩
  fin_cases k <;> fin_cases l <;> simp

/-- A computed elementary conjugator for exchanging both entire finite
input blocks of the actual stable block-sum homomorphism. -/
public def swapBlockElementaryConjugator (n : ℕ) : StableE R :=
  ⟨elementaryConjugator (swapBlockUnit R n),
    elementaryConjugator_mem (swapBlockUnit R n)⟩

/-- The computed elementary conjugator exchanges the WHOLE pair of
finite general-linear inputs, not only their quotient classes. -/
public theorem swapBlockElementaryConjugator_conjugates (n : ℕ)
    (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    (swapBlockElementaryConjugator R n : StableGL R) *
        StableGL.of (finiteBlockSumHom R n (g, h)) *
        (swapBlockElementaryConjugator R n : StableGL R)⁻¹ =
      StableGL.of (finiteBlockSumHom R n (h, g)) := by
  change elementaryConjugator (swapBlockUnit R n) *
      StableGL.of (finiteBlockSumHom R n (g, h)) *
      (elementaryConjugator (swapBlockUnit R n))⁻¹ = _
  have hq := elementaryConjugator_conjugates (swapBlockUnit R n)
    (finiteBlockSumHom R n (g, h))
  rw [swapBlockUnit_conjugates R n g h] at hq
  exact hq

/-- A computed stable elementary matrix that compares the original finite
inclusion with the actual interleaved first block of stable block sum. -/
public def leftBlockElementaryConjugator (n : ℕ) : StableE R :=
  ⟨elementaryConjugator (leftInterleavingUnit R n),
    elementaryConjugator_mem (leftInterleavingUnit R n)⟩

/-- The actual finite doubled permutation for the first block comparison. -/
public def leftBlockDoubledPermutation (n : ℕ) :
    Equiv.Perm (Fin (n * Fintype.card BlockPairIndex.{u} +
      n * Fintype.card BlockPairIndex.{u})) :=
  doubledFinitePermutation (interleavingPermutation.{u} n)

/-- Its sign is literally one; this supplies the finite inactive factor
after taking consecutive stabilization differences. -/
public theorem leftBlockDoubledPermutation_sign (n : ℕ) :
    Equiv.Perm.sign (leftBlockDoubledPermutation.{u} n) = 1 :=
  doubledFinitePermutation_sign (interleavingPermutation.{u} n)

/-- The computed elementary conjugator retains the actual finite even
permutation matrix, not only its stable elementary membership. -/
public theorem leftBlockElementaryConjugator_matrix (n : ℕ) :
    (leftBlockElementaryConjugator R n : StableGL R) =
      StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
        (leftBlockDoubledPermutation.{u} n)) :=
  elementaryConjugator_permutation (interleavingPermutation.{u} n)

/-- The ORIGINAL zero-stage conjugator is the literal stable identity.
Its doubled finite permutation has an empty domain, so no unit loop is
silently discarded at the marked zero-stage point. -/
public theorem leftBlockElementaryConjugator_zero :
    (leftBlockElementaryConjugator R 0 : StableGL R) = 1 := by
  have hp : leftBlockDoubledPermutation.{u} 0 = 1 := by
    apply Equiv.ext
    intro x
    have hx : x.val < 0 := by
      simpa only [Nat.zero_mul, Nat.zero_add] using x.isLt
    omega
  rw [leftBlockElementaryConjugator_matrix, hp, MonoidHom.map_one, StableGL.of_one]

/-- The original finite coordinates inside the doubled matrix rank. -/
public def leftBlockActiveIndex (n : ℕ) (i : Fin n) :
    Fin (n * Fintype.card BlockPairIndex.{u} + n * Fintype.card BlockPairIndex.{u}) :=
  finSumFinEquiv (m := n * Fintype.card BlockPairIndex.{u})
    (n := n * Fintype.card BlockPairIndex.{u})
    (Sum.inl (orderedBlockIndex.{u} n (Sum.inl i)))

private theorem leftBlockActiveIndex_val_computed (n : ℕ) (i : Fin n) :
    (leftBlockActiveIndex.{u} n i).val = i.val := rfl

/-- Its numerical coordinate is the original finite coordinate. -/
public theorem leftBlockActiveIndex_val (n : ℕ) (i : Fin n) :
    (leftBlockActiveIndex.{u} n i).val = i.val :=
  leftBlockActiveIndex_val_computed.{u} n i

/-- The actual doubled permutation sends each original active coordinate
to the original interleaved first-slot coordinate, in its first half. -/
public theorem leftBlockDoubledPermutation_active (n : ℕ) (i : Fin n) :
    leftBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n i) =
      finSumFinEquiv (m := n * Fintype.card BlockPairIndex.{u})
        (n := n * Fintype.card BlockPairIndex.{u})
        (Sum.inl
          (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, ULift.up 0))) := by
  rw [leftBlockDoubledPermutation, leftBlockActiveIndex,
    doubledFinitePermutation_apply]
  change finSumFinEquiv (m := n * Fintype.card BlockPairIndex.{u})
    (n := n * Fintype.card BlockPairIndex.{u})
    (Sum.inl (interleavedBlockIndex.{u} n
      ((orderedBlockIndex.{u} n).symm ((orderedBlockIndex.{u} n) (Sum.inl i))))) = _
  rw [Equiv.symm_apply_apply, interleavedBlockIndex_inl]

/-- The first-slot value formula is independent of the stage number.
It is the actual chosen matrix enumeration, not an identity calibration. -/
public theorem leftBlockDoubledPermutation_active_val (n : ℕ) (i : Fin n) :
    (leftBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n i)).val =
      (MatrixDiagram.equivFinMatrix (ι := BlockPairIndex.{u}) (ULift.up (0 : Fin 2))).val +
        Fintype.card BlockPairIndex.{u} * i.val := by
  rw [leftBlockDoubledPermutation_active]
  exact MatrixDiagram.finProdMatrixEquiv_val n i (ULift.up 0)

/-- The SAME computed elementary matrix conjugates the WHOLE original
finite general-linear group into the actual first stable block. -/
public theorem leftBlockElementaryConjugator_conjugates (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (leftBlockElementaryConjugator R n : StableGL R) * StableGL.of g *
        (leftBlockElementaryConjugator R n : StableGL R)⁻¹ =
      blockSumLeftHom R (StableGL.of g) := by
  change elementaryConjugator (leftInterleavingUnit R n) * StableGL.of g *
    (elementaryConjugator (leftInterleavingUnit R n))⁻¹ = _
  let a := Matrix.GeneralLinearGroup.reindexMulEquiv (orderedBlockIndex.{u} n)
    (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin n) (Fin n) R g)
  have ha : StableGL.of a = StableGL.of g := orderedPrefix_stable R n g
  have h := elementaryConjugator_conjugates (leftInterleavingUnit R n) a
  rw [ha, leftInterleavingUnit_conjugates R n g] at h
  exact h.trans (blockSumLeftHom_of R n g).symm

private theorem blockSumRightHom_of (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    blockSumRightHom R (StableGL.of g) = StableGL.of (finiteBlockSumHom R n (1, g)) := by
  rw [blockSumRightHom_apply]
  exact (congrArg (fun h : StableGL R => blockSumHom R (h, StableGL.of g))
    (StableGL.of_one (n := n) (R := R)).symm).trans
      (blockSumHom_of_pair R 1 g)

/-- The original second unit block is compared by the two computed
elementary matrices, without choosing a new conjugation witness. -/
public def rightBlockElementaryConjugator (n : ℕ) : StableE R :=
  swapBlockElementaryConjugator R n * leftBlockElementaryConjugator R n

/-- The actual second block contains the entire original finite group
up to the computed elementary conjugation. -/
public theorem rightBlockElementaryConjugator_conjugates (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (rightBlockElementaryConjugator R n : StableGL R) * StableGL.of g *
        (rightBlockElementaryConjugator R n : StableGL R)⁻¹ =
      blockSumRightHom R (StableGL.of g) := by
  let v : StableGL R := (swapBlockElementaryConjugator R n : StableGL R)
  let w : StableGL R := (leftBlockElementaryConjugator R n : StableGL R)
  change (v * w) * StableGL.of g * (v * w)⁻¹ = _
  calc
    (v * w) * StableGL.of g * (v * w)⁻¹ =
        v * (w * StableGL.of g * w⁻¹) * v⁻¹ := by
      rw [_root_.mul_inv_rev]
      simp only [mul_assoc]
    _ = v * blockSumLeftHom R (StableGL.of g) * v⁻¹ := by
      rw [leftBlockElementaryConjugator_conjugates R n g]
    _ = v * StableGL.of (finiteBlockSumHom R n (g, 1)) * v⁻¹ := by
      rw [blockSumLeftHom_of R n g]
    _ = StableGL.of (finiteBlockSumHom R n (1, g)) :=
      swapBlockElementaryConjugator_conjugates R n g 1
    _ = blockSumRightHom R (StableGL.of g) := (blockSumRightHom_of R n g).symm

/-- The actual doubled even permutation of the original finite block swap. -/
public abbrev swapBlockDoubledPermutation (n : ℕ) :
    Equiv.Perm (Fin (n * Fintype.card BlockPairIndex.{u} +
      n * Fintype.card BlockPairIndex.{u})) :=
  doubledFinitePermutation (swapBlockPermutation.{u} n)

/-- The original swap conjugator retains its actual doubled permutation matrix. -/
public theorem swapBlockElementaryConjugator_matrix (n : ℕ) :
    (swapBlockElementaryConjugator R n : StableGL R) =
      StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
        (swapBlockDoubledPermutation.{u} n)) := by
  change elementaryConjugator (swapBlockUnit R n) = _
  simpa only [swapBlockUnit, swapBlockDoubledPermutation] using
    (elementaryConjugator_permutation (R := R) (swapBlockPermutation.{u} n))

/-- The actual product of the two doubled permutations defining the right unit. -/
public abbrev rightBlockDoubledPermutation (n : ℕ) :
    Equiv.Perm (Fin (n * Fintype.card BlockPairIndex.{u} +
      n * Fintype.card BlockPairIndex.{u})) :=
  swapBlockDoubledPermutation.{u} n * leftBlockDoubledPermutation.{u} n

/-- This SAME right-unit permutation is even, by its two doubled factors. -/
public theorem rightBlockDoubledPermutation_sign (n : ℕ) :
    Equiv.Perm.sign (rightBlockDoubledPermutation.{u} n) = 1 := by
  rw [map_mul, doubledFinitePermutation_sign, leftBlockDoubledPermutation_sign, one_mul]

/-- Its original ambient matrix is exactly the existing computed right-unit conjugator. -/
public theorem rightBlockElementaryConjugator_matrix (n : ℕ) :
    (rightBlockElementaryConjugator R n : StableGL R) =
      StableGL.of (Matrix.GeneralLinearGroup.permutationUnitsHom R _
        (rightBlockDoubledPermutation.{u} n)) := by
  change (swapBlockElementaryConjugator R n : StableGL R) *
    (leftBlockElementaryConjugator R n : StableGL R) = _
  rw [swapBlockElementaryConjugator_matrix, leftBlockElementaryConjugator_matrix,
    ← StableGL.of_mul, ← MonoidHom.map_mul]

/-- The actual right-unit permutation takes EVERY original active
coordinate to the original second interleaved slot, in the first half. -/
public theorem rightBlockDoubledPermutation_active (n : ℕ) (i : Fin n) :
    rightBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n i) =
      finSumFinEquiv (m := n * Fintype.card BlockPairIndex.{u})
        (n := n * Fintype.card BlockPairIndex.{u})
        (Sum.inl
          (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, ULift.up 1))) := by
  change swapBlockDoubledPermutation.{u} n
    (leftBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n i)) = _
  rw [leftBlockDoubledPermutation_active]
  let e := finSumFinEquiv (m := n * Fintype.card BlockPairIndex.{u})
    (n := n * Fintype.card BlockPairIndex.{u})
  rw [swapBlockDoubledPermutation, doubledFinitePermutation_apply]
  apply congrArg e
  apply congrArg Sum.inl
  simp [swapBlockPermutation]

/-- The numerical second-slot formula is independent of the stage rank.
It uses the ORIGINAL coefficient-slot enumeration, rather than a chosen identity. -/
public theorem rightBlockDoubledPermutation_active_val (n : ℕ) (i : Fin n) :
    (rightBlockDoubledPermutation.{u} n (leftBlockActiveIndex.{u} n i)).val =
      (MatrixDiagram.equivFinMatrix (ι := BlockPairIndex.{u}) (ULift.up (1 : Fin 2))).val +
        Fintype.card BlockPairIndex.{u} * i.val := by
  rw [rightBlockDoubledPermutation_active]
  exact MatrixDiagram.finProdMatrixEquiv_val n i (ULift.up 1)

/-- The original zero-stage right-unit conjugator is the literal identity. -/
public theorem rightBlockElementaryConjugator_zero :
    (rightBlockElementaryConjugator R 0 : StableGL R) = 1 := by
  have hp : rightBlockDoubledPermutation.{u} 0 = 1 := by
    apply Equiv.ext
    intro x
    have hx : x.val < 0 := by
      simpa only [Nat.zero_mul, Nat.zero_add] using x.isLt
    omega
  rw [rightBlockElementaryConjugator_matrix, hp, MonoidHom.map_one, StableGL.of_one]

end AlgebraicKTheory.StableGL

end
