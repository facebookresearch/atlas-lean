/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.DiscreteFunctor
public import MathlibExt.Topology.Category.PointedCGWH.DiscreteCoproduct

/-!
# Actual based discrete CGWH index functors
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory

namespace PointedCGWH

/-- The actual index functor followed by the native free-basepoint functor. -/
def basedDiscreteFunctor : Type w ⥤ PointedCGWH.{u, max v w} :=
  CGWH.discreteFunctor.{u, v, w} ⋙ Under.costar CGWH.point

@[simp]
theorem basedDiscreteFunctor_obj (I : Type w) :
    basedDiscreteFunctor.{u, v, w}.obj I = basedDiscreteObj.{u, v, w} I :=
  rfl

@[simp]
theorem basedDiscreteFunctor_map {I J : Type w} (f : I → J) :
    basedDiscreteFunctor.{u, v, w}.map (↾f) =
      (Under.costar CGWH.point.{u, max v w}).map (CGWH.discreteMap.{u, v, w} f) :=
  rfl

/-- Based point injections retain the actual native index-map naturality. -/
@[reassoc (attr := simp)]
theorem basedDiscreteIncl_naturality {I J : Type w} (f : I → J) (i : I) :
    basedDiscreteIncl.{u, v, w} I i ≫ basedDiscreteFunctor.map (↾f) =
      basedDiscreteIncl J (f i) := by
  change (Under.costar CGWH.point.{u, max v w}).map (CGWH.discreteObjIncl I i) ≫
      (Under.costar CGWH.point).map (CGWH.discreteMap f) =
    (Under.costar CGWH.point).map (CGWH.discreteObjIncl J (f i))
  rw [← Functor.map_comp, CGWH.discreteObjIncl_naturality]

end PointedCGWH
