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

/-
The filtered capability generalizes the closed formalization of Weibel,
*An Introduction to Homological Algebra*, Theorem 2.6.15, by @toskua and Avocado
in `FormalizedTextbooks.WeibelHomologicalAlgebra.Chapter02.Section06.Colimits`.
That original short-exact-sequence theorem now specializes this shared API,
retaining its original modules, colimit functor and universe assumptions.
-/

/-!
# Exact module colimits from additive-group colimits

Let R be a ring with scalar world independent of the module carrier
world v. For a category J, if additive groups in world v have
colimits of shape J and these colimits are exact, the corresponding
R-module colimits are exact.

For filtered J, it suffices that both its object and morphism worlds
are bounded by v, together with existence of the additive-group
colimits of shape J. The module colimit functor then preserves finite
limits, equivalently short exact sequences in the module category.

Reference: Weibel, *An Introduction to Homological Algebra*,
Theorem 2.6.15.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uScalar vCarrier uShape vShape

namespace ModuleCat

variable (R : Type uScalar) [Ring R]

/-- For a ring R and a category J, assume additive groups
in carrier world v have colimits of shape J and that this
colimit functor preserves finite limits.
Then ModuleCat^v(R) has exact colimits of shape J.
The scalar world of R is independent of v. -/
theorem hasExactColimitsOfShape_of_addCommGrp
    (J : Type uShape) [Category.{vShape} J]
    [HasColimitsOfShape J AddCommGrpCat.{vCarrier}]
    [HasExactColimitsOfShape J AddCommGrpCat.{vCarrier}] :
    HasExactColimitsOfShape J (ModuleCat.{vCarrier} R) :=
  HasExactColimitsOfShape.domain_of_functor J
    (forget₂ (ModuleCat.{vCarrier} R) AddCommGrpCat.{vCarrier})

/-- For a ring R and a filtered category J, suppose both
the object and morphism universes of J are bounded by
the module carrier world v, and additive-group colimits
of shape J exist in world v.
Then ModuleCat^v(R) has exact colimits of shape J. -/
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
