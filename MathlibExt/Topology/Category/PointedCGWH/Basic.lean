/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Point
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Pointed compactly generated weak Hausdorff spaces

Pointed CGWH spaces are the generic undercategory of the native point
object.  All pointed-object and pointed-morphism data are inherited from
`CategoryTheory.Under`.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of pointed CGWH spaces. -/
abbrev PointedCGWH := Under CGWH.point.{u, v}

namespace PointedCGWH

/-- Forget the selected point of a pointed CGWH space. -/
abbrev pointedToCGWH : PointedCGWH.{u, v} ⥤ CGWH.{u, v} :=
  Under.forget CGWH.point.{u, v}

end PointedCGWH
