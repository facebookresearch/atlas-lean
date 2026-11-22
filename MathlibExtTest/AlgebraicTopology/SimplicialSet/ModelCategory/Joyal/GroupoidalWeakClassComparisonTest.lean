/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GroupoidalWeakClassComparison

/-!
# Groupoidal Weak Class Comparison Test
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

universe u

namespace SSet

-- The public type requires groupoidality of the two ORIGINAL homotopy categories.
example {X Y : SSet.{u}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Y.HomotopyCategory] (f : X ⟶ Y) :
    categoricalEquivalences f ↔ realizationWeakEquivalences f :=
  categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid f

-- Both implications preserve the literal input arrow.
example {X Y : SSet.{u}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Y.HomotopyCategory] (f : X ⟶ Y)
    (hf : categoricalEquivalences f) : realizationWeakEquivalences f :=
  (categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid f).mp hf

example {X Y : SSet.{u}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Y.HomotopyCategory] (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) : categoricalEquivalences f :=
  (categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid f).mpr hf

-- The intermediate source need not be supplied as a Kan complex or quasicategory.
example {X Y Z : SSet.{u}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Z.HomotopyCategory] (f : X ⟶ Y) (g : Y ⟶ Z) :
    categoricalEquivalences (f ≫ g) ↔ realizationWeakEquivalences (f ≫ g) :=
  categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid (f ≫ g)

-- Raising the original value universe does not add structural hypotheses.
example {X Y : SSet.{u + 1}} [IsGroupoid X.HomotopyCategory]
    [IsGroupoid Y.HomotopyCategory] (f : X ⟶ Y) :
    categoricalEquivalences f ↔ realizationWeakEquivalences f :=
  categoricalEquivalences_iff_realizationWeakEquivalences_of_isGroupoid f

end SSet
