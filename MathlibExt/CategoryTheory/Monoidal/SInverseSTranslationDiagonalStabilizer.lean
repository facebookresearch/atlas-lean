/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBaseAction

/-!
# Stabilizer class of the canonical translation arrow

The chosen raw representative of a quotient translation arrow need not be
the raw arrow used to construct its quotient class.  For the canonical arrow
`B ⟶ A ⊞ B`, quotient exactness nevertheless gives an isomorphism from
the chosen stabilizer to `A`.  Thus its skeleton class is `[A]`, and its map
in the core-homology coefficient system is the corresponding monomial action.

No equality of chosen representatives, localization, spectral-sequence,
realization, or CGWH claim is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The selected representative of the canonical translation arrow has
skeleton stabilizer class `[A]`. -/
theorem translationStabilizerClass_diagonalAdd
    (A : C) (B : Translation C) :
    translationStabilizerClass C
        ((Translation.diagonalAddNatTrans A).app B) =
      toSkeleton A := by
  let f := (Translation.diagonalAddNatTrans A).app B
  have hq : Translation.Hom.mk (Translation.representative f) =
      Translation.Hom.mk (Translation.RawHom.diagonalAdd A B) := by
    calc
      _ = f := Translation.mk_representative f
      _ = _ := rfl
  obtain ⟨e, _⟩ := Quotient.exact hq
  simpa only [translationStabilizerClass_out, Translation.representative,
    Translation.RawHom.diagonalAdd, f] using congr_toSkeleton_of_iso e

/-- The canonical translation arrow acts on the core-homology coefficient
module by the monomial of `[A]`. -/
theorem coreTranslationCoefficientFunctor_map_diagonalAdd
    (R : AddCommGrpCat.{u}) (n : ℕ) (A : C) (B : Translation C) :
    (coreTranslationCoefficientFunctor C R n).map
        ((Translation.diagonalAddNatTrans A).app B) =
      coreTranslationCoefficientMap C R n (toSkeleton A) := by
  rw [coreTranslationCoefficientFunctor_map,
    translationStabilizerClass_diagonalAdd]

end SInverseS
end CategoryTheory

end
