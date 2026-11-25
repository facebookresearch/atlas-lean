/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctorTransport

/-!
# Exact-functor lift to cofiber-sequence categories

For an additive exact functor `F : C ⥤ D` between Quillen exact categories,
`cofiberSequenceFunctor F` lifts `(forget C) ⋙ F.mapComposableArrows 2`
through `cofiberSequenceProperty D` using the existing
`isCofibrationSequence_map` preservation proof.

Requires `[Preadditive] [HasZeroObject] [HasBinaryBiproducts] [ExactCategory]`
on each of `C`, `D`, plus `[F.Additive] [F.IsExact]`; file-local
`ExactCategory.waldhausenCategory` instances interpret the source/target
`CofiberSequenceCategory` types. No other hypotheses.

Nonclaims: no identity/composition/naturality API, no `WaldhausenCategoryWithoutGluing`
instance on cofiber sequences, and no Stage/additivity/G-theory/spectra/Q-S
content.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]

local instance cofiberExactFunctorWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C
local instance cofiberExactFunctorWaldhausenD : WaldhausenCategoryWithoutGluing D :=
  ExactCategory.waldhausenCategory D

/-- An additive exact functor lifts to cofiber-sequence categories. -/
def cofiberSequenceFunctor (F : C ⥤ D) [F.Additive] [F.IsExact] :
    CofiberSequenceCategory C ⥤ CofiberSequenceCategory D :=
  (cofiberSequenceProperty D).lift
    ((CofiberSequenceCategory.forget C) ⋙ F.mapComposableArrows 2)
    (fun S => isCofibrationSequence_map F _ _ S.property)

end CategoryTheory.Waldhausen.SConstruction
