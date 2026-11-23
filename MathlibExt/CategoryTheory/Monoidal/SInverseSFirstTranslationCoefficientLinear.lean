/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientCommutation

/-!
# Linear lift of conjugated first-coordinate translation

The conjugated first-coordinate coefficient map commutes with every skeleton
monomial.  The monoid-algebra equivariance constructor therefore promotes its
underlying integer-linear map to a morphism of core translation modules.

This file only packages that linear and `ModuleCat` lift.  It performs no
localization and makes no identity claim.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The conjugated first-coordinate coefficient map as a linear endomorphism
of the core translation module. -/
noncomputable def conjugatedFirstTranslationCoefficientLinearMap
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    coreTranslationHomologyModule C R q →ₗ[coreTranslationRing C]
      coreTranslationHomologyModule C R q := by
  let f : coreTranslationHomologyModule C R q →ₗ[ℤ]
      coreTranslationHomologyModule C R q :=
    (conjugatedFirstTranslationCoefficientMap C R q A B).hom.toIntLinearMap
  exact MonoidAlgebra.equivariantOfLinearOfComm f
    (fun g z => by
      have h := ConcreteCategory.congr_hom
        (conjugatedFirstTranslationCoefficientMap_comm_monomial
          C R q A B g.toAdd) z
      simp only [CategoryTheory.comp_apply] at h
      change
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
            (Multiplicative.ofAdd g.toAdd)) •
              f z =
          f
            ((MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
              (Multiplicative.ofAdd g.toAdd)) • z) at h
      simpa only [MonoidAlgebra.of_apply, ofAdd_toAdd,
        AddMonoidHom.coe_toIntLinearMap] using h.symm)

@[simp]
theorem conjugatedFirstTranslationCoefficientLinearMap_apply
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C)
    (z : coreTranslationHomologyModule C R q) :
    conjugatedFirstTranslationCoefficientLinearMap C R q A B z =
      conjugatedFirstTranslationCoefficientMap C R q A B z :=
  rfl

/-- The conjugated first-coordinate coefficient map as a morphism in the
core translation module category. -/
noncomputable def conjugatedFirstTranslationCoefficientModuleMap
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    coreTranslationHomologyModuleCat C R q ⟶
      coreTranslationHomologyModuleCat C R q :=
  ModuleCat.ofHom
    (conjugatedFirstTranslationCoefficientLinearMap C R q A B)

/-- Forgetting the module structure recovers the original conjugated
additive-group map. -/
@[simp↓]
theorem conjugatedFirstTranslationCoefficientModuleMap_forget
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
        (conjugatedFirstTranslationCoefficientModuleMap C R q A B) =
      conjugatedFirstTranslationCoefficientMap C R q A B := by
  apply ConcreteCategory.hom_ext
  intro z
  rfl

end SInverseS
end CategoryTheory

end
