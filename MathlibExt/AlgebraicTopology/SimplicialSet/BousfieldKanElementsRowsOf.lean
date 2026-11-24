/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsDiagonal

/-!
# Full coefficient-elements rows at independent original universes

The actual existing flip, elements and nerve functors retain each
original coefficient category with independent indexing object, Hom
and coefficient universes. At the native value universe this is
literally the full original Bousfield--Kan elements-row diagram.
-/

noncomputable section

universe uJ vJ w

open CategoryTheory Opposite

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- The same canonical full coefficient-elements rows at arbitrary independent original
value universe. -/
def bkElementsRowsOf (D : J ⥤ SSet.{w}) : SimplexCategoryᵒᵖ ⥤ SSet.{max uJ vJ w} :=
  D.flip ⋙ Functor.elementsFunctor ⋙ nerveFunctor

/-- The entire arbitrary-value elements row is the same original native row at its native
coefficient universe. -/
theorem bkElementsRowsOf_eq_native (D : J ⥤ SSet.{max uJ vJ}) :
    bkElementsRowsOf D = bkElementsRows D := rfl

end SSet
