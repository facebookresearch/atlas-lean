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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Product

@[expose] public section

namespace MathlibExtTest.Matrix.GeneralLinearGroup.Product

universe uI uR uS

private theorem generic_product_coordinates
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (g : Matrix.GeneralLinearGroup ι (R × S)) :
    (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) ι g).1 =
        Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst R S) g ∧
      (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) ι g).2 =
        Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd R S) g :=
  ⟨Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_fst ι g,
    Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_snd ι g⟩

private theorem generic_product_roundtrip
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (g : Matrix.GeneralLinearGroup ι (R × S)) :
    (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) ι).symm
        (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) ι g) = g :=
  (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) ι).symm_apply_apply g

private abbrev ZeroSemiring := Fin 0 → ℕ

private theorem empty_zero_product_roundtrip :
    (Matrix.GeneralLinearGroup.prodSemiringEquiv
      (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0)).symm
        (Matrix.GeneralLinearGroup.prodSemiringEquiv
          (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0) 1) = 1 :=
  (Matrix.GeneralLinearGroup.prodSemiringEquiv
    (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0)).symm_apply_apply 1

private abbrev MatrixInt := Matrix (Fin 2) (Fin 2) ℤ

private def negBlock : Matrix.GeneralLinearGroup (Fin 2) MatrixInt :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : MatrixIntˣ)

private def productWitness : Matrix.GeneralLinearGroup (Fin 2) (MatrixInt × ℤ) :=
  (Matrix.GeneralLinearGroup.prodSemiringEquiv (Fin 2)).symm (negBlock, 1)

/-- A nonempty product whose two projections differ, with an explicit original entry. -/
example :
    Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst MatrixInt ℤ) productWitness = negBlock ∧
    Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd MatrixInt ℤ) productWitness = 1 ∧
    productWitness.val 0 0 = (-1, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_fst]
    simp [productWitness]
  · rw [← Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_snd]
    simp [productWitness]
  · calc
      productWitness.val 0 0 = ((negBlock.val 0 0), (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :=
        Matrix.GeneralLinearGroup.coe_prodSemiringEquiv_symm_apply (Fin 2) (negBlock, 1) 0 0
      _ = (-1, 1) := by simp [negBlock, Matrix.GeneralLinearGroup.scalar]

#print axioms generic_product_coordinates
#print axioms generic_product_roundtrip
#print axioms empty_zero_product_roundtrip

end MathlibExtTest.Matrix.GeneralLinearGroup.Product
