/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The zero object of pointed CGWH spaces

The identity of the native CGWH point is both initial and terminal in its
undercategory, and hence defines the canonical zero object of `PointedCGWH`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace PointedCGWH

/-- The identity of the native CGWH point is a zero object in its
undercategory. -/
noncomputable instance instHasZeroObject :
    HasZeroObject PointedCGWH.{u, v} where
  zero :=
    ⟨Under.mk (𝟙 CGWH.point.{u, v}),
      { unique_to := fun Y =>
          ⟨{ default := Under.mkIdInitial.to Y
             uniq := fun f => Under.mkIdInitial.hom_ext f _ }⟩
        unique_from := fun Y =>
          ⟨{ default := Under.homMk
                (CGWH.point_isTerminal.from Y.right)
                (CGWH.point_isTerminal.hom_ext _ _)
             uniq := fun f => Under.UnderMorphism.ext
               (CGWH.point_isTerminal.hom_ext f.right _) }⟩ }⟩

/-- The underlying CGWH space of the chosen pointed zero object is the native
point. -/
@[simp]
theorem zero_right :
    (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}).right =
      CGWH.point.{u, v} :=
  rfl

/-- The selected point of the pointed zero object is the identity of the
native point. -/
@[simp]
theorem zero_hom :
    (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}).hom =
      𝟙 CGWH.point.{u, v} := by
  rfl

end PointedCGWH
