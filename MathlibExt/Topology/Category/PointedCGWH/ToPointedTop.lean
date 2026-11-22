/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.Topology.Category.PointedTopCat

/-!
# Forgetting pointed CGWH spaces to pointed topological spaces
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory

namespace PointedCGWH

/-- The direct inclusion of pointed CGWH spaces into pointed topological
spaces. -/
noncomputable def toPointedTop :
    PointedCGWH.{u, v} ⥤ PointedTopCat.{v} :=
  Under.post CGWH.cgwhToTop.{u, v}

/-- The underlying object of the pointed inclusion is the CGWH inclusion of
the underlying object. -/
@[simp]
theorem toPointedTop_obj_right (X : PointedCGWH.{u, v}) :
    (toPointedTop.obj X).right = CGWH.cgwhToTop.obj X.right :=
  rfl

/-- The selected-point map is carried directly by the CGWH inclusion. -/
@[simp]
theorem toPointedTop_obj_hom (X : PointedCGWH.{u, v}) :
    (toPointedTop.obj X).hom = CGWH.cgwhToTop.map X.hom :=
  rfl

/-- The right component of an included pointed map is its underlying
topological map. -/
@[simp]
theorem toPointedTop_map_right {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (toPointedTop.map f).right = CGWH.cgwhToTop.map f.right :=
  rfl

end PointedCGWH

end
