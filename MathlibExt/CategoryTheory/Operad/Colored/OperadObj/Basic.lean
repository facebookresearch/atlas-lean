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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Associativity

/-!
# Enriched colored operads

A fixed-color enriched operad consists of a colored symmetric collection, a unit at every color,
a natural simultaneous-substitution operation, and the two unit laws and associativity law.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

/-- An enriched operad with a fixed type of colors. -/
structure ColoredOperadObj (Color : Type u) (V : Type w)
    [Category.{v} V] [FiniteTensor V] where
  /-- The underlying colored symmetric collection. -/
  toCollection : ColoredSymmetricCollection Color V
  /-- The unit operation at every color. -/
  unit : ColoredOperadUnit toCollection
  /-- Simultaneous color-matching substitution. -/
  subst : ColoredOperadSubstitution toCollection
  /-- Right unit law. -/
  right_unit : ColoredOperadObj.IsRightUnit toCollection unit subst
  /-- Left unit law. -/
  left_unit : ColoredOperadObj.IsLeftUnit toCollection unit subst
  /-- Associativity law. -/
  assoc : ColoredOperadObj.IsAssociative toCollection subst

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

/-- Units are preserved along unit-profile maps, at general `V`: any
profile map between unary identity profiles is the identity (its input
equivalence is uniquely determined), so mapping the unit along it is
the unit. -/
theorem map_unitProfileMap_unit (O : ColoredOperadObj Color V)
    {c c' : Color} (f : ColoredSubstitutionData.unitProfile c ⟶
      ColoredSubstitutionData.unitProfile c') :
    O.unit c ≫ O.toCollection.map f = O.unit c' := by
  have hcc : c = c' := f.outputColor_eq
  cases hcc
  have hf : f = 𝟙 (ColoredSubstitutionData.unitProfile c) := by
    apply ColoredProfile.Hom.ext
    exact Equiv.ext (fun x => by
      cases x with
      | unit =>
          cases h : f.inputEquiv PUnit.unit with
          | unit => rfl)
  rw [hf, O.toCollection.map_id]
  exact Category.comp_id _

end ColoredOperadObj

end CategoryTheory.Operad
