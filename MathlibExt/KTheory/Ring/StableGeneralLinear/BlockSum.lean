/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Product
public import MathlibExt.KTheory.Ring.StableGeneralLinear.MatrixEquiv
public import Mathlib.Data.Matrix.Basic

/-!
# The actual stable finite block-sum homomorphism

The two stable factors are first identified with the stable group over the
product ring. The unital diagonal coefficient map and existing matrix
invariance then give one compatible stable block sum. Its finite formula is
the corresponding interleaved block diagonal, so no choices of finite
representatives enter its definition. This is algebraic data for the
independent BGL-plus multiplication requested in Weibel Exercise IV.1.11;
the plus extension and coherence homotopies are separate proof steps.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicKTheory

universe u

namespace AlgebraicKTheory.StableGL

/-- The two finite coefficient slots have the ring's universe. Only the
finite index is lifted; the coefficient ring itself remains the original R. -/
public abbrev BlockPairIndex : Type u := ULift.{u} (Fin 2)

variable (R : Type u) [Semiring R]

/-- The actual two coefficients, as a unital map to the two-slot product ring. -/
public def blockPairCoefficientHom : (R × R) →+* (BlockPairIndex.{u} → R) where
  toFun p k := if k.down = 0 then p.1 else p.2
  map_one' := by
    funext k
    split_ifs <;> rfl
  map_mul' p q := by
    funext k
    simp only [Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    split_ifs <;> rfl
  map_zero' := by
    funext k
    split_ifs <;> rfl
  map_add' p q := by
    funext k
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
    split_ifs <;> rfl

/-- The actual unital two-block diagonal coefficient map. -/
public def blockPairDiagonalHom : (R × R) →+*
    Matrix BlockPairIndex.{u} BlockPairIndex.{u} R :=
  (Matrix.diagonalRingHom (n := BlockPairIndex.{u}) (α := R)).comp
    (blockPairCoefficientHom R)

private theorem blockPairDiagonalHom_apply_computed (p : R × R)
    (k l : BlockPairIndex.{u}) :
    blockPairDiagonalHom R p k l =
      if k = l then (if k.down = 0 then p.1 else p.2) else 0 := by
  rfl

/-- Its entries are the original two coefficients and zero off the diagonal. -/
public theorem blockPairDiagonalHom_apply (p : R × R)
    (k l : BlockPairIndex.{u}) :
    blockPairDiagonalHom R p k l =
      if k = l then (if k.down = 0 then p.1 else p.2) else 0 :=
  blockPairDiagonalHom_apply_computed R p k l

/-- Finite block sum, with the original coefficients and existing flattening. -/
public def finiteBlockSumHom (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R × Matrix.GeneralLinearGroup (Fin n) R) →*
      Matrix.GeneralLinearGroup (Fin (n * Fintype.card BlockPairIndex.{u})) R :=
  (MatrixDiagram.matrixGLMulEquiv (R := R) (ι := BlockPairIndex.{u}) n).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.mapRingHom (blockPairDiagonalHom R)).comp
      (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := R) (Fin n)).symm.toMonoidHom)

/-- A compatible stable block sum, defined by existing product and matrix
invariance. There is no selected representative or desired plus map in this definition. -/
public def blockSumHom : (StableGL R × StableGL R) →* StableGL R :=
  (stableGLMatrixMulEquiv (R := R) (ι := BlockPairIndex.{u})).toMonoidHom.comp
    ((StableGL.functor.map (SemiRingCat.ofHom (blockPairDiagonalHom R))).hom.comp
      (prodEquiv R R).symm.toMonoidHom)

/-- The finite map has the original interleaved diagonal coefficients.
The enumeration is the SAME one selected by the existing matrix diagram. -/
public theorem finiteBlockSumHom_coefficients (n : ℕ)
    (A B : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n)
    (k l : BlockPairIndex.{u}) :
    (↑(finiteBlockSumHom R n (A, B)) :
      Matrix (Fin (n * Fintype.card BlockPairIndex.{u}))
        (Fin (n * Fintype.card BlockPairIndex.{u})) R)
      (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (i, k))
      (MatrixDiagram.finProdMatrixEquiv (ι := BlockPairIndex.{u}) n (j, l)) =
        if k = l then
          (if k.down = 0 then (A : Matrix (Fin n) (Fin n) R) i j
            else (B : Matrix (Fin n) (Fin n) R) i j)
          else 0 := by
  let Z := Matrix.GeneralLinearGroup.mapRingHom (blockPairDiagonalHom R)
    ((Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := R) (Fin n)).symm (A, B))
  let e₁ := MatrixDiagram.prodEquivFin (ι := BlockPairIndex.{u}) n
  let e₂ : Fin n × Fin (Fintype.card BlockPairIndex.{u}) ≃
      Fin (n * Fintype.card BlockPairIndex.{u}) := finProdFinEquiv
  change (↑(Matrix.GeneralLinearGroup.reindexMulEquiv e₂
    (Matrix.GeneralLinearGroup.reindexMulEquiv e₁
      (Matrix.GeneralLinearGroup.compMulEquiv (Fin n) BlockPairIndex.{u} R Z))) :
        Matrix (Fin (n * Fintype.card BlockPairIndex.{u}))
          (Fin (n * Fintype.card BlockPairIndex.{u})) R)
      ((e₁.trans e₂) (i, k)) ((e₁.trans e₂) (j, l)) = _
  simp only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
    Matrix.GeneralLinearGroup.coe_compMulEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
    Matrix.comp_apply]
  simp only [Z, Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply,
    Matrix.GeneralLinearGroup.coe_prodSemiringEquiv_symm_apply]
  exact blockPairDiagonalHom_apply R _ k l

private theorem blockSumHom_apply_computed (x y : StableGL R) :
    blockSumHom R (x, y) =
      stableGLMatrixMulEquiv (R := R) (ι := BlockPairIndex.{u})
        (StableGL.functor.map (SemiRingCat.ofHom (blockPairDiagonalHom R))
          ((prodEquiv R R).symm (x, y))) := rfl

/-- The whole stable hom retains its actual product-ring and flattening recipe. -/
public theorem blockSumHom_apply (x y : StableGL R) :
    blockSumHom R (x, y) =
      stableGLMatrixMulEquiv (R := R) (ι := BlockPairIndex.{u})
        (StableGL.functor.map (SemiRingCat.ofHom (blockPairDiagonalHom R))
          ((prodEquiv R R).symm (x, y))) :=
  blockSumHom_apply_computed R x y

/-- On finite representatives of the same rank, the map is the actual
finite interleaved block sum. Adding identities and taking common ranks is
already handled by the existing stable product and matrix APIs. -/
public theorem blockSumHom_of_pair {n : ℕ}
    (A B : Matrix.GeneralLinearGroup (Fin n) R) :
    blockSumHom R (StableGL.of A, StableGL.of B) =
      StableGL.of (finiteBlockSumHom R n (A, B)) := by
  rw [blockSumHom_apply, prodEquiv_symm_of_pair, StableGL.map_of,
    stableGLMatrixMulEquiv_of]
  rfl

/-- The actual original identity pair maps to the identity. -/
public theorem blockSumHom_one : blockSumHom R (1, 1) = 1 :=
  (blockSumHom R).map_one

/-- The first factor's actual stable block embedding. It is not identified
with the identity map before the later plus/coherence comparison. -/
public def blockSumLeftHom : StableGL R →* StableGL R where
  toFun x := blockSumHom R (x, 1)
  map_one' := blockSumHom_one R
  map_mul' x y := by
    simpa only [Prod.mk_mul_mk, mul_one] using
      (blockSumHom R).map_mul (x, 1) (y, 1)

private theorem blockSumLeftHom_apply_computed (x : StableGL R) :
    blockSumLeftHom R x = blockSumHom R (x, 1) := by
  simp only [blockSumLeftHom, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The original first block hom evaluates by inserting the second identity. -/
public theorem blockSumLeftHom_apply (x : StableGL R) :
    blockSumLeftHom R x = blockSumHom R (x, 1) :=
  blockSumLeftHom_apply_computed R x

/-- The second factor's actual stable block embedding. -/
public def blockSumRightHom : StableGL R →* StableGL R where
  toFun y := blockSumHom R (1, y)
  map_one' := blockSumHom_one R
  map_mul' x y := by
    simpa only [Prod.mk_mul_mk, mul_one] using
      (blockSumHom R).map_mul (1, x) (1, y)

private theorem blockSumRightHom_apply_computed (y : StableGL R) :
    blockSumRightHom R y = blockSumHom R (1, y) := by
  simp only [blockSumRightHom, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The original second block hom evaluates by inserting the first identity. -/
public theorem blockSumRightHom_apply (y : StableGL R) :
    blockSumRightHom R y = blockSumHom R (1, y) :=
  blockSumRightHom_apply_computed R y

/-- The actual block sum is the product of its two factor embeddings. -/
public theorem blockSumHom_eq_left_mul_right (x y : StableGL R) :
    blockSumHom R (x, y) = blockSumLeftHom R x * blockSumRightHom R y := by
  rw [blockSumLeftHom_apply, blockSumRightHom_apply]
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
    (blockSumHom R).map_mul (x, 1) (1, y)

/-- The two factor images strictly commute in the original stable group. -/
public theorem blockSumLeftRight_commute (x y : StableGL R) :
    Commute (blockSumLeftHom R x) (blockSumRightHom R y) := by
  change blockSumLeftHom R x * blockSumRightHom R y =
    blockSumRightHom R y * blockSumLeftHom R x
  have hl : blockSumHom R (x, y) = blockSumLeftHom R x * blockSumRightHom R y :=
    blockSumHom_eq_left_mul_right R x y
  have hr : blockSumHom R (x, y) = blockSumRightHom R y * blockSumLeftHom R x := by
    rw [blockSumRightHom_apply, blockSumLeftHom_apply]
    simpa only [Prod.mk_mul_mk, one_mul, mul_one] using
      (blockSumHom R).map_mul (1, y) (x, 1)
  exact hl.symm.trans hr

end AlgebraicKTheory.StableGL

end
