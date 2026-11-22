/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Smash
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# The pointed CGWH smash unit is a separator

Maps from the freely based point `S⁰` select arbitrary points of a pointed
compactly generated weak Hausdorff space, so they separate pointed maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u v

namespace PointedCGWH

/-- The freely based CGWH point separates pointed CGWH maps. -/
theorem isSeparator_sphereZero :
    CategoryTheory.IsSeparator sphereZero.{u, v} := by
  have hPoint : CategoryTheory.IsSeparator CGWH.point.{u, v} := by
    rw [CategoryTheory.isSeparator_def]
    intro X Y f g hfg
    apply ConcreteCategory.hom_ext
    intro x
    let b : CGWH.point.{u, v} ⟶ X :=
      (CGWH.pointHomEquiv X).symm x
    calc
      f x = CGWH.pointHomEquiv Y (b ≫ f) := by
        rw [CGWH.pointHomEquiv_apply]
        change f x = f ((CGWH.pointHomEquiv X).symm x PUnit.unit)
        rw [CGWH.pointHomEquiv_symm_apply_apply]
      _ = CGWH.pointHomEquiv Y (b ≫ g) :=
        congrArg (CGWH.pointHomEquiv Y) (hfg b)
      _ = g x := by
        rw [CGWH.pointHomEquiv_apply]
        change g ((CGWH.pointHomEquiv X).symm x PUnit.unit) = g x
        rw [CGWH.pointHomEquiv_symm_apply_apply]
  change CategoryTheory.IsSeparator sphereZero.{u, v}
  exact hPoint.leftAdjoint_obj (Under.costarAdjForget CGWH.point.{u, v})

/-- The native pointed CGWH smash unit separates pointed CGWH maps. -/
theorem isSeparator_tensorUnit :
    CategoryTheory.IsSeparator (𝟙_ PointedCGWH.{u, v}) := by
  change CategoryTheory.IsSeparator sphereZero.{u, v}
  exact isSeparator_sphereZero

end PointedCGWH
