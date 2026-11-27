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
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Zero object for the cofiber-sequence category

The constant-zero length-two composable arrow satisfies `cofiberSequenceProperty`
via the zero-out-of cofibration and the identity-square pushout. Hence the
property contains zero, and `CofiberSequenceCategory C` receives its zero object
through the existing `ObjectProperty.ContainsZero` full-subcategory transfer.

This file provides no Waldhausen instance on the cofiber category and no
closure, gluing, or additivity claim.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Constant-zero length-two composable arrow. -/
private noncomputable def zeroComposableArrow : ComposableArrows C 2 :=
  (Functor.const (Fin 3)).obj (0 : C)

/-- The constant-zero arrow is a cofiber sequence, reusing the zero-out-of
cofibration and the identity-square pushout. -/
private theorem isCofiber_zeroComposableArrow :
    cofiberSequenceProperty C (zeroComposableArrow C) := by
  have hCof : IsCofibration (C := C) (𝟙 (0 : C)) :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
  have hPush : IsPushout (𝟙 (0 : C)) (𝟙 (0 : C)) (𝟙 (0 : C)) (𝟙 (0 : C)) :=
    IsPushout.of_id_fst
  simpa [zeroComposableArrow, cofiberSequenceProperty] using
    ⟨hCof, 𝟙 (0 : C), 𝟙 (0 : C), hPush⟩

/-- The cofiber-sequence property contains zero; the zero object on the full
subcategory follows from the existing transfer. -/
instance : (cofiberSequenceProperty C).ContainsZero where
  exists_zero :=
    ⟨zeroComposableArrow C,
     Functor.isZero _ fun _ => isZero_zero C,
     isCofiber_zeroComposableArrow C⟩

end CategoryTheory.Waldhausen.SConstruction
