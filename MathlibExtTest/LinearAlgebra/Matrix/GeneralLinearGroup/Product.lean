/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
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
    (Matrix.GeneralLinearGroup.prodEquiv (R := R) (S := S) ι g).1 =
        Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst R S) g ∧
      (Matrix.GeneralLinearGroup.prodEquiv (R := R) (S := S) ι g).2 =
        Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd R S) g :=
  ⟨Matrix.GeneralLinearGroup.prodEquiv_apply_fst ι g,
    Matrix.GeneralLinearGroup.prodEquiv_apply_snd ι g⟩

private theorem generic_product_roundtrip
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (g : Matrix.GeneralLinearGroup ι (R × S)) :
    (Matrix.GeneralLinearGroup.prodEquiv (R := R) (S := S) ι).symm
        (Matrix.GeneralLinearGroup.prodEquiv (R := R) (S := S) ι g) = g :=
  (Matrix.GeneralLinearGroup.prodEquiv (R := R) (S := S) ι).symm_apply_apply g

private abbrev ZeroSemiring := Fin 0 → ℕ

private theorem empty_zero_product_roundtrip :
    (Matrix.GeneralLinearGroup.prodEquiv
      (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0)).symm
        (Matrix.GeneralLinearGroup.prodEquiv
          (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0) 1) = 1 :=
  (Matrix.GeneralLinearGroup.prodEquiv
    (R := ZeroSemiring) (S := ZeroSemiring) (Fin 0)).symm_apply_apply 1

#print axioms generic_product_coordinates
#print axioms generic_product_roundtrip
#print axioms empty_zero_product_roundtrip

end MathlibExtTest.Matrix.GeneralLinearGroup.Product
