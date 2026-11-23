/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationPageScalars

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.SInverseS HomologicalComplex₂
open scoped BigOperators

noncomputable section
set_option autoImplicit false

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

example (W : C)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page 1 (by omega)).X (0, 0)) :
    (secondTranslationBKModulePageForgetIso (C := C) R 1 (by omega)).hom.f (0, 0)
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (-1 : ℤ) • x) =
      - (horizontalPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) 1 (by omega)).f (0, 0)
        ((secondTranslationBKModulePageForgetIso (C := C) R 1 (by omega)).hom.f (0, 0) x) := by
  simpa only [neg_one_zsmul] using secondTranslationBKModulePageForgetIso_single_apply R 1 (by omega) 0 0 W (-1) x

example (W : C)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page 3 (by omega)).X (0, 2)) :
    (secondTranslationBKModulePageForgetIso (C := C) R 3 (by omega)).hom.f (0, 2)
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (2 : ℤ) • x) =
      (2 : ℤ) • (horizontalPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) 3 (by omega)).f (0, 2)
        ((secondTranslationBKModulePageForgetIso (C := C) R 3 (by omega)).hom.f (0, 2) x) := by
  exact secondTranslationBKModulePageForgetIso_single_apply R 3 (by omega) 0 2 W 2 x

example (r : ℤ) (hr : 1 ≤ r) (p q : ℕ) (a : MonoidAlgebra ℤ (Multiplicative (Skeleton C)))
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).X (p, q)) :
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) (a • x) =
      ∑ m ∈ a.coeff.support, (a.coeff m) • (horizontalPageMapOfBicomplex
        (secondTranslationBKBicomplexMap R m.toAdd.out) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) := by
  exact secondTranslationBKModulePageForgetIso_smul_apply R r hr p q a x

example (r : ℤ) (hr : 1 ≤ r) (p q : ℕ) (W V : C)
    (x : ((secondTranslationBKModuleSpectralSequence (C := C) R).page r hr).X (p, q)) :
    (secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q)
        ((MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (2 : ℤ) +
          MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton V)) (-1 : ℤ)) • x) =
      (2 : ℤ) • (horizontalPageMapOfBicomplex (secondTranslationBKBicomplexMap R W) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) -
      (horizontalPageMapOfBicomplex (secondTranslationBKBicomplexMap R V) r hr).f (p, q)
        ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q) x) := by
  rw [add_smul]
  change ((secondTranslationBKModulePageForgetIso (C := C) R r hr).hom.f (p, q)).hom (_ + _) = _
  rw [map_add]
  simpa only [neg_one_zsmul, sub_eq_add_neg] using congrArg₂ (fun a b => a + b)
    (secondTranslationBKModulePageForgetIso_single_apply R r hr p q W 2 x)
    (secondTranslationBKModulePageForgetIso_single_apply R r hr p q V (-1) x)


end
