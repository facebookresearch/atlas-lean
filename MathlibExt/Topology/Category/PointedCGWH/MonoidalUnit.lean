/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# The cartesian tensor unit as a pointed CGWH space

The native point and the chosen cartesian tensor unit are both terminal in
`CGWH`. Their canonical isomorphism equips the tensor unit with a point.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

/-- The canonical isomorphism from the native point to the chosen cartesian
tensor unit. -/
noncomputable def pointIsoTensorUnit :
    CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} where
  hom := terminalIsTerminal.from _
  inv := CGWH.point_isTerminal.from _
  hom_inv_id := CGWH.point_isTerminal.hom_ext _ _
  inv_hom_id := terminalIsTerminal.hom_ext _ _

@[simp]
theorem pointIsoTensorUnit_hom :
    pointIsoTensorUnit.{u, v}.hom =
      terminalIsTerminal.from CGWH.point.{u, v} :=
  rfl

@[simp]
theorem pointIsoTensorUnit_inv :
    pointIsoTensorUnit.{u, v}.inv =
      CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) :=
  rfl

/-- The chosen cartesian tensor unit as a pointed CGWH space. -/
noncomputable def tensorUnit : PointedCGWH.{u, v} :=
  Under.mk pointIsoTensorUnit.hom

@[simp]
theorem tensorUnit_right : tensorUnit.{u, v}.right = 𝟙_ CGWH.{u, v} :=
  rfl

@[simp]
theorem tensorUnit_hom : tensorUnit.{u, v}.hom = pointIsoTensorUnit.hom :=
  rfl

end PointedCGWH
