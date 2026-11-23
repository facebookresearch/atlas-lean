/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaHomologyNaturality
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison

/-!
# Right-comma homology versus the core translation coefficient system

For the additive `S⁻¹S` translation projection, the natural comparison from
right-comma homology to strict-fiber homology combines with the inverse of the
core-module/fiber comparison.  The result identifies right-comma homology
naturally with the underlying additive groups of the module-valued core
translation coefficient system.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Right-comma homology is naturally the underlying additive group of the
core translation coefficient module. -/
noncomputable def costructuredCoreTranslationCoefficientNatIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    Functor.IsCofibered.costructuredHomologyFunctor
        (p := translationProjection (C := C)) AddCommGrpCat.{u} R q ≅
      coreTranslationCoefficientFunctor C R q ⋙
        forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u} :=
  Functor.IsCofibered.costructuredFiberHomologyNatIso
      (p := translationProjection (C := C)) AddCommGrpCat.{u} R q ≪≫
    (coreTranslationCoefficientFiberNatIso C R q).symm

/-- The comma/core coefficient comparison component is the comma/fiber
homology comparison followed by the inverse module/fiber comparison. -/
@[simp]
theorem costructuredCoreTranslationCoefficientNatIso_hom_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (B : Translation C) :
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B =
      (Functor.IsCofibered.costructuredFiberHomologyIso
          (p := translationProjection (C := C)) AddCommGrpCat.{u} B R q).hom ≫
        (coreTranslationCoefficientFiberIsoApp C R q B).inv :=
  rfl

end SInverseS
end CategoryTheory

end
