/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Binary coproducts from Waldhausen pushouts

The zero-object and cofibration-pushout axioms of a Waldhausen category imply
the existence of binary coproducts: push out the two unique maps from zero.
This file exposes a `Nonempty` colimit cocone, one noncomputably chosen
cocone, and a named `HasBinaryCoproducts` value.

The named value is intentionally not an instance.  Installing it globally
would compete with user-supplied coproduct choices and alter definitional
behavior in unrelated files.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- A binary coproduct colimit cocone exists, obtained as a pushout of the
two unique maps from the zero object. -/
theorem binaryCoproductColimitCocone_nonempty
    (F : Discrete WalkingPair ⥤ C) :
    Nonempty (ColimitCocone F) := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let i : (0 : C) ⟶ X := (isZero_zero C).to_ X
  let f : (0 : C) ⟶ Y := (isZero_zero C).to_ Y
  have hi : IsCofibration i :=
    WaldhausenCategoryWithoutGluing.zero_isCofibration X i
  obtain ⟨P, inY, inX, hpush, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) i hi Y f
  let c : Cocone F :=
    { pt := P
      ι := Discrete.natTrans fun j =>
        Discrete.casesOn j fun j =>
          WalkingPair.casesOn j inX inY }
  refine ⟨c, ?_⟩
  exact isBinaryCoproductOfIsInitialIsPushout F c
    (isZero_zero C).isInitial i f hpush.flip.isColimit

/-- A chosen binary coproduct colimit cocone. -/
noncomputable def binaryCoproductColimitCocone
    (F : Discrete WalkingPair ⥤ C) :
    ColimitCocone F :=
  Classical.choice (binaryCoproductColimitCocone_nonempty C F)

/-- Named binary-coproduct data derived from the Waldhausen axioms.

This is deliberately not a global instance. -/
theorem waldhausenHasBinaryCoproducts :
    HasBinaryCoproducts C :=
  { has_colimit := fun F =>
      HasColimit.mk (binaryCoproductColimitCocone C F) }

end CategoryTheory.Waldhausen
