/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationStabilizerClass

/-!
# Public stabilizer classes with independent category universes

The neutral invariant can be used without importing homology coefficients.
Its identity and composition laws retain the original public names.
-/

noncomputable section

open CategoryTheory Limits ZeroObject
open CategoryTheory.SInverseS

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example {X Y : Translation C} (r s : Translation.RawHom X Y) (h : r.Rel s) :
    translationStabilizerClass C (Translation.Hom.mk r) = toSkeleton s.stabilizer := by
  rw [show Translation.Hom.mk r = Translation.Hom.mk s from Quotient.sound h]
  exact translationStabilizerClass_mk C s

example (X : Translation C) : translationStabilizerClass C (𝟙 X) = 0 :=
  translationStabilizerClass_id C X

example {X Y Z : Translation C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    translationStabilizerClass C (f ≫ g) =
      translationStabilizerClass C f + translationStabilizerClass C g :=
  translationStabilizerClass_comp C f g

end
