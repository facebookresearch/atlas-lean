/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedSecondPage

/-!
# Concentration of the actual localized BK second page

The native second page of the actual localized BK module spectral object
vanishes in every positive horizontal degree. Its zero column is canonically
localized whole-core homology, using the actual page comparison followed by
the canonical coefficient-refinement zero-column comparison.

Both conclusions use the constructed native category and coefficient group.
The original complete cuts, signed degrees and page recipe are retained by
the actual localized spectral model.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{u})

local notation "PB" => secondTranslationBKLocalizedModuleSpectralSequence (C := C) R

/-- The actual localized second page vanishes in every positive horizontal
degree, for every native category, coefficient group and vertical degree. -/
theorem isZero_secondTranslationBKLocalizedModuleSecondPage
    (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (((PB).page 2 (by omega)).X (p,q)) :=
  IsZero.of_iso
    (isZero_localizedCoreTranslationActionCoefficientRefinement C R p q hp)
    (secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R p q)

/-- The actual localized zero column is localized whole-core homology through
the canonical actual-page and coefficient-refinement comparisons. -/
def secondTranslationBKLocalizedModuleSecondPageZeroIso (q : ℕ) :
    ((PB).page 2 (by omega)).X (0,q) ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R 0 q ≪≫
    localizedCoreTranslationActionCoefficientRefinementZeroIso C R q

/-- The zero-column forward map is exactly the actual Phi forward map
followed by the canonical coefficient zero-column forward map. -/
theorem secondTranslationBKLocalizedModuleSecondPageZeroIso_hom (q : ℕ) :
    (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).hom =
      (secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R 0 q).hom ≫
        (localizedCoreTranslationActionCoefficientRefinementZeroIso C R q).hom := rfl

/-- The zero-column inverse follows precisely the reverse canonical route. -/
theorem secondTranslationBKLocalizedModuleSecondPageZeroIso_inv (q : ℕ) :
    (secondTranslationBKLocalizedModuleSecondPageZeroIso (C := C) R q).inv =
      (localizedCoreTranslationActionCoefficientRefinementZeroIso C R q).inv ≫
        (secondTranslationBKLocalizedModuleSecondPageCoefficientIso (C := C) R 0 q).inv := rfl

end CategoryTheory.SInverseS

end
