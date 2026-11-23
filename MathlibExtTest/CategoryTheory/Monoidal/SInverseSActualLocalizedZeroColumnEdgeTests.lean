/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSActualLocalizedZeroColumnEdge

/-!
# Ordinary imports of the actual localized zero-column edge

Check the unconditional edge isomorphism and its canonical stage-zero law in
all degrees and at degree zero through the producer's public API.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.ComposableArrows

namespace CategoryTheory.SInverseS

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

example (q : ℕ) :
    IsIso (secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q) :=
  inferInstance

example : IsIso (secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R 0) :=
  inferInstance

local notation "LY" => secondTranslationBKLocalizedModuleSpectralObject (C := C) R
local notation "L" => ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)

example (q : ℕ)
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((secondTranslationBKLocalizedModuleSpectralObject (C := C) R).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))) :
    (LY).nativeZeroColumnStageZeroRepresentative hneg q ≫
        secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R q =
      (secondTranslationBKLocalizedStageModuleIso (C := C) R q
          ((0 : ℤ) : EInt)).hom ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R q
          ((0 : ℤ) : EInt)) := by
  exact secondTranslationBKLocalizedModuleZeroColumnEdge_representation (C := C) R q

example
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((secondTranslationBKLocalizedModuleSpectralObject (C := C) R).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt)))))) :
    (LY).nativeZeroColumnStageZeroRepresentative hneg 0 ≫
        secondTranslationBKLocalizedModuleZeroColumnEdge (C := C) R 0 =
      (secondTranslationBKLocalizedStageModuleIso (C := C) R 0
          ((0 : ℤ) : EInt)).hom ≫
        (L).map (secondTranslationBKStageToTotalModuleMap (C := C) R 0
          ((0 : ℤ) : EInt)) := by
  exact secondTranslationBKLocalizedModuleZeroColumnEdge_representation (C := C) R 0

end CategoryTheory.SInverseS

end
