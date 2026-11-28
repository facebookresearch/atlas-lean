/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GroupSchemeSeparated

/-!
# Tests for group schemes over a field being separated
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace MathlibExtTest.AlgebraicGeometry.GroupSchemeSeparated

universe u

/-- A group scheme over a field is separated. -/
example {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)] :
    IsSeparated f :=
  isSeparated_of_grpObj f

/-- Its diagonal is therefore a closed immersion, and so is the identity section. -/
example {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)] :
    IsClosedImmersion (pullback.diagonal f) ∧ IsClosedImmersion η[Over.mk f].left :=
  have := isSeparated_of_grpObj f
  ⟨inferInstance, isClosedImmersion_of_comp_eq_id (Y := Spec (.of k)) f _ (Over.w η[Over.mk f])⟩

/-- Over any base, a group scheme with closed identity section is separated. -/
example {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)]
    [IsClosedImmersion η[Over.mk f].left] : IsSeparated f :=
  isSeparated_of_grpObj_of_isClosedImmersion f

/-- The diagonal of a group object over a scheme is the pullback of the unit along division. -/
example {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (lift (fst G G) (snd G G ≫ ι) ≫ μ) η[G] :=
  GrpObj.isPullback_lift_id_id G

end MathlibExtTest.AlgebraicGeometry.GroupSchemeSeparated
