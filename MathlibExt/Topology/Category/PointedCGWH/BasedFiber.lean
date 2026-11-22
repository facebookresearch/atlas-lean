/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CGWH.BasedFiber
import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Pointed native strict fibers

A chosen lift of a target point gives the native CGWH strict fiber its
pointed object. A compatible square preserving the two chosen points gives
its pointed map. These whole functions depend only on native strict fibers
and the undercategory of the native point.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace PointedCGWH

/-- The native strict fiber pointed by a chosen lift of the basepoint. -/
noncomputable def strictFiberPointed
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b) :
    PointedCGWH.{u, v} :=
  Under.mk (CGWH.strictFiberPoint p b e over)

/-- A compatible square carrying the chosen lift induces a pointed map of
strict fibers. -/
noncomputable def strictFiberPointedMap
    {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b')
    (point : e ≫ a = e') :
    strictFiberPointed p b e over ⟶ strictFiberPointed p' b' e' over' :=
  Under.homMk (CGWH.strictFiberMap a d square base)
    (CGWH.strictFiberPoint_naturality
      a d square base e over e' over' point)

end PointedCGWH
