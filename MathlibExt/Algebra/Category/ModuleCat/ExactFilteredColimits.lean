/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Exact filtered colimits with independent scalar and carrier universes

The existing module forgetful functor preserves colimits and finite limits and
reflects finite limits independently of the scalar world. Transfer exactness
from native additive-group colimits; no module colimit object is reimplemented.
The filtered specialization records both shape-universe bounds and actual
additive-group colimit existence. These are named capabilities rather than a
new global AB5 instance. No separator or injective-resolution conclusion is made.

The filtered capability generalizes the closed formalization of Weibel,
*An Introduction to Homological Algebra*, Theorem 2.6.15, by @toskua and Avocado
in `FormalizedTextbooks.WeibelHomologicalAlgebra.Chapter02.Section06.Colimits`.
That original short-exact-sequence theorem now specializes this shared API,
retaining its original modules, colimit functor and universe assumptions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uScalar vCarrier uShape vShape

namespace ModuleCat

variable (R : Type uScalar) [Ring R]

/-- Exact additive-group colimits transfer to the actual native module colimits. -/
theorem hasExactColimitsOfShape_of_addCommGrp
    (J : Type uShape) [Category.{vShape} J]
    [HasColimitsOfShape J AddCommGrpCat.{vCarrier}]
    [HasExactColimitsOfShape J AddCommGrpCat.{vCarrier}] :
    HasExactColimitsOfShape J (ModuleCat.{vCarrier} R) :=
  HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{vCarrier} R) AddCommGrpCat.{vCarrier})

/-- Filtered colimits are exact when both shape universes fit the carrier world. -/
theorem hasExactFilteredColimitsOfShape
    (J : Type uShape) [Category.{vShape} J] [IsFiltered J]
    [UnivLE.{uShape, vCarrier}] [UnivLE.{vShape, vCarrier}]
    [HasColimitsOfShape J AddCommGrpCat.{vCarrier}] :
    HasExactColimitsOfShape J (ModuleCat.{vCarrier} R) := by
  let : HasFilteredColimitsOfSize.{vShape, uShape} AddCommGrpCat.{vCarrier} :=
    hasFilteredColimitsOfSize_of_univLE.{vShape, uShape, vCarrier, vCarrier}
      (C := AddCommGrpCat.{vCarrier})
  let : AB5OfSize.{vShape, uShape} AddCommGrpCat.{vCarrier} :=
    AB5OfSize_of_univLE.{vShape, uShape, vCarrier, vCarrier} AddCommGrpCat.{vCarrier}
  exact hasExactColimitsOfShape_of_addCommGrp R J

end ModuleCat
