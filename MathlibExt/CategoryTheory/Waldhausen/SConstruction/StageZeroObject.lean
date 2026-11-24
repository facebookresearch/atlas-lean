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

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Zero objects in finite Waldhausen stages

The pointwise-zero `Ar n` diagram is a finite stage.  Registering it as a
`ContainsZero` witness for `stageProperty C n` lets Mathlib's generic full
subcategory construction provide `HasZeroObject (Stage C n)`.

This is independent of any proposed Waldhausen structure on `Stage C n` and
does not install one.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- The stage property contains the pointwise-zero diagram.  Consequently,
the generic full-subcategory instance supplies a zero object on every finite
stage category. -/
instance stagePropertyContainsZero (n : ℕ) :
    (stageProperty C n).ContainsZero where
  exists_zero :=
    ⟨zeroDiagram C n,
      Functor.isZero _ (fun _ ↦ isZero_zero C),
      isStage_zeroDiagram C n⟩

end CategoryTheory.Waldhausen.SConstruction
