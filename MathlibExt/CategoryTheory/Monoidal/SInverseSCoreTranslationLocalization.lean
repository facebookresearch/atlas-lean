/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Localization.Module
public import MathlibExt.Algebra.Monoid.CofinalElementLocalization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationAction

/-!
# Localization of the skeleton action on core homology

Localize the monoid-algebra module on core homology at all skeleton
monomials.  Every monomial then acts through a canonical linear equivalence,
and this equivalence extends the corresponding core-translation homology
map across the localization map.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The additive monoid algebra of the skeleton. -/
abbrev coreTranslationRing :=
  MonoidAlgebra ℤ (Multiplicative (Skeleton C))

/-- The submonoid of skeleton monomials. -/
abbrev coreTranslationDenominators :
    Submonoid (coreTranslationRing C) :=
  MonoidHom.mrange (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C)))

/-- Core homology localized at every skeleton monomial. -/
noncomputable abbrev localizedCoreTranslationHomology
    (R : AddCommGrpCat.{u}) (n : ℕ) :=
  LocalizedModule (coreTranslationDenominators C)
    (coreTranslationHomologyModule C R n)

/-- A skeleton monomial as an element of the localization denominator
submonoid. -/
noncomputable def coreTranslationDenominator (x : Skeleton C) :
    coreTranslationDenominators C :=
  ⟨MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
      (Multiplicative.ofAdd x),
    MonoidHom.mem_mrange.mpr ⟨Multiplicative.ofAdd x, rfl⟩⟩

/-- The image of a skeleton monomial is a unit in the localized coefficient
ring. -/
noncomputable def localizedCoreTranslationMonomialUnit
    (x : Skeleton C) :
    Units (Localization (coreTranslationDenominators C)) :=
  (IsLocalization.map_units
    (Localization (coreTranslationDenominators C))
    (coreTranslationDenominator C x)).unit

@[simp]
theorem localizedCoreTranslationMonomialUnit_val
    (x : Skeleton C) :
    (localizedCoreTranslationMonomialUnit C x :
        Localization (coreTranslationDenominators C)) =
      algebraMap (coreTranslationRing C)
        (Localization (coreTranslationDenominators C))
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x)) :=
  IsUnit.unit_spec (IsLocalization.map_units
    (Localization (coreTranslationDenominators C))
    (coreTranslationDenominator C x))

/-- In localized core homology, multiplication by any skeleton monomial is
a linear equivalence. -/
noncomputable def localizedCoreTranslationEquiv
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C) :
    localizedCoreTranslationHomology C R n ≃ₗ[
      Localization (coreTranslationDenominators C)]
      localizedCoreTranslationHomology C R n :=
  LinearEquiv.smulOfUnit (localizedCoreTranslationMonomialUnit C x)

@[simp]
theorem localizedCoreTranslationEquiv_apply
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C)
    (z : localizedCoreTranslationHomology C R n) :
    localizedCoreTranslationEquiv C R n x z =
      algebraMap (coreTranslationRing C)
          (Localization (coreTranslationDenominators C))
          (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
            (Multiplicative.ofAdd x)) • z := by
  change (localizedCoreTranslationMonomialUnit C x :
      Localization (coreTranslationDenominators C)) • z = _
  rw [localizedCoreTranslationMonomialUnit_val]

/-- The localized monomial equivalence extends monomial action on the
original core-homology module. -/
theorem localizedCoreTranslationEquiv_mk
    (R : AddCommGrpCat.{u}) (n : ℕ) (x : Skeleton C)
    (z : coreTranslationHomologyModule C R n) :
    localizedCoreTranslationEquiv C R n x
        (LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R n) z) =
      LocalizedModule.mkLinearMap
        (coreTranslationDenominators C)
        (coreTranslationHomologyModule C R n)
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) := by
  rw [localizedCoreTranslationEquiv_apply]
  rw [IsScalarTower.algebraMap_smul]
  exact ((LocalizedModule.mkLinearMap
    (coreTranslationDenominators C)
    (coreTranslationHomologyModule C R n)).map_smul
      (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x)) z).symm

end SInverseS
end CategoryTheory

end
