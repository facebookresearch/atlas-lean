/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Middle functor comparisons

Compatible isomorphisms for Arrow-valued source functors and intermediate
object functors give an isomorphism between their composites across a
functor `F`. Whiskering combines the intermediate-functor comparison with
the source-Arrow comparison.
-/

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The entire original intermediate functor comparison follows its exact zero-arrow comparison. -/
def originalMiddleComparison (F : C ⥤ D) (Z : Arrow D ⥤ D) (Z' : Arrow C ⥤ C)
    (A : C ⥤ Arrow C) (A' : D ⥤ Arrow D)
    (cZ : Z' ⋙ F ≅ F.mapArrow ⋙ Z) (cA : A ⋙ F.mapArrow ≅ F ⋙ A') :
    (A ⋙ Z') ⋙ F ≅ F ⋙ (A' ⋙ Z) :=
  Functor.isoWhiskerLeft A cZ ≪≫ Functor.isoWhiskerRight cA Z

end CategoryTheory
