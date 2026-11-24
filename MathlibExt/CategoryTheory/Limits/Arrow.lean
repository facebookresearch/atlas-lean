/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Limit preservation by the arrow projections

Limits in an arrow category are computed componentwise. Mathlib already exposes
the corresponding colimit-preservation instances for `Arrow.leftFunc` and
`Arrow.rightFunc`; this file supplies their limit-side duals.
-/

@[expose] public section

noncomputable section

universe v u vJ uJ

open CategoryTheory Limits

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]
variable (J : Type uJ) [Category.{vJ} J]

set_option backward.isDefEq.respectTransparency false in
/-- The left projection from an arrow category preserves limits whenever the
base category has limits of the given shape. -/
instance preservesLimitsOfShape_leftFunc [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Arrow.leftFunc : Arrow C ⥤ C) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (Comma.coneOfPreservesIsLimit F (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The right projection from an arrow category preserves limits whenever the
base category has limits of the given shape. -/
instance preservesLimitsOfShape_rightFunc [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (Arrow.rightFunc : Arrow C ⥤ C) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (Comma.coneOfPreservesIsLimit F (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

end CategoryTheory.Arrow
