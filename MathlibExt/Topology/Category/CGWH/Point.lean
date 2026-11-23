/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The point object in CGWH

This file defines the native one-point CGWH space, proves directly that it is
terminal, and identifies maps from it with points of the target.  It does not
install a global chosen terminal object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CGWH

/-- The one-point CGWH space. -/
def point : CGWH.{u, v} :=
  CGWH.of PUnit.{v + 1}

/-- The one-point CGWH space is terminal. -/
def point_isTerminal : IsTerminal point.{u, v} :=
  IsTerminal.ofUniqueHom
    (fun X =>
      ConcreteCategory.ofHom
        (show C(X, point.{u, v}) from
          ⟨fun _ => PUnit.unit, continuous_const⟩))
    (fun _ _ => by
      ext x
      change _ = (PUnit.unit : PUnit.{v + 1})
      exact Subsingleton.elim _ _)

/-- Evaluation at the unique point identifies maps from the named CGWH point with points of the
target. -/
noncomputable def pointHomEquiv (X : CGWH.{u, v}) :
    (CGWH.point.{u, v} ⟶ X) ≃ X where
  toFun f := f PUnit.unit
  invFun x := ConcreteCategory.ofHom (ContinuousMap.const PUnit x)
  left_inv f := by
    apply ConcreteCategory.hom_ext
    intro p
    change PUnit.{v + 1} at p
    rcases p with ⟨⟩
    rfl
  right_inv _ := rfl

@[simp]
theorem pointHomEquiv_apply (X : CGWH.{u, v}) (f : CGWH.point.{u, v} ⟶ X) :
    pointHomEquiv X f = f PUnit.unit :=
  rfl

@[simp]
theorem pointHomEquiv_symm_apply_apply (X : CGWH.{u, v}) (x : X) (p : PUnit) :
    (pointHomEquiv X).symm x p = x :=
  rfl

end CGWH
