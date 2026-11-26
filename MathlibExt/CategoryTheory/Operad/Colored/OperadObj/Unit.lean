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

public import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Indexing
public import MathlibExt.CategoryTheory.Operad.OperadObj.Unit

/-!
# Units and substitution operations for colored operads

This file introduces the raw unit and substitution data carried by a colored symmetric collection.
The unit is indexed by colors, while substitution is a natural transformation on the category of
color-matching substitution shapes.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

/-- A unit operation at every color of a colored symmetric collection. -/
abbrev ColoredOperadUnit {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V) :=
  (c : Color) → operadUnitSource (V := V) ⟶
    O.obj (ColoredSubstitutionData.unitProfile c)

/-- A simultaneous color-matching substitution operation. -/
abbrev ColoredOperadSubstitution {Color : Type u} {V : Type w}
    [Category.{v} V] [FiniteTensor V] (O : ColoredSymmetricCollection Color V) :=
  ColoredOperadObj.substitutionSource O ⟶ ColoredOperadObj.substitutionTarget O

end CategoryTheory.Operad
