/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal

/-!
# The actual coefficient lift commutes with the full original diagonal

Both inverse maps keep the same full lifted coefficient. The original
inner and outer scalar operators are both retained by the canonical
whiskering functor.
-/

noncomputable section

universe u v

open CategoryTheory Opposite

namespace SSet

/-- Both full original diagonal directions retain the same complete lifted coefficient and
both original ordinal
operators. -/
def uliftDiagonalIso (D : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    uliftFunctor.{v,u}.obj (simplicialDiagonalFunctor.obj D) ≅
      simplicialDiagonalFunctor.obj (D ⋙ uliftFunctor.{v,u}) :=
  NatIso.ofComponents (fun q => Iso.refl _) (by intro q r θ; rfl)

end SSet
