/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.DiscreteCoproduct
public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Freely based discrete CGWH objects as coproducts of the freely based point
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH

/-- The actual freely based lifted discrete native space. -/
def basedDiscreteObj (I : Type w) : PointedCGWH.{u, max v w} :=
  (Under.costar CGWH.point.{u, max v w}).obj (CGWH.discreteObj.{u, v, w} I)

/-- The based point injection is the actual free-basepoint functor map. -/
def basedDiscreteIncl (I : Type w) (i : I) :
    (Under.costar CGWH.point.{u, max v w}).obj CGWH.point ⟶
      basedDiscreteObj.{u, v, w} I :=
  (Under.costar CGWH.point.{u, max v w}).map (CGWH.discreteObjIncl.{u, v, w} I i)

/-- The actual based discrete point injections form the constant free-point cofan. -/
def basedDiscreteCofan (I : Type w) :
    Cofan (fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point) :=
  Cofan.mk (basedDiscreteObj.{u, v, w} I) (basedDiscreteIncl I)

/-- The free-basepoint adjunction preserves the actual native point coproduct. -/
def basedDiscreteCofanIsColimit (I : Type w) :
    IsColimit (basedDiscreteCofan.{u, v, w} I) := by
  let F : CGWH.{u, max v w} ⥤ PointedCGWH.{u, max v w} :=
    Under.costar CGWH.point
  exact (Cofan.isColimitMapCoconeEquiv F
    (fun _ : I => CGWH.point) (CGWH.discreteCofan.{u, v, w} I))
    (isColimitOfPreserves F (CGWH.discreteCofanIsColimit.{u, v, w} I))

/-- The literal based cofan supplies free-point-coproduct existence. -/
theorem basedDiscreteHasCoproduct (I : Type w) :
    HasCoproduct (fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point) :=
  HasColimit.mk ⟨basedDiscreteCofan I, basedDiscreteCofanIsColimit I⟩

/-- Comparison of the actual based discrete object with any chosen free-point coproduct. -/
def basedDiscreteCoproductIso (I : Type w)
    [HasCoproduct (fun _ : I =>
      (Under.costar CGWH.point.{u, max v w}).obj CGWH.point)] :
    basedDiscreteObj.{u, v, w} I ≅
      ∐ fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point :=
  (basedDiscreteCofanIsColimit I).coconePointUniqueUpToIso
    (coproductIsCoproduct
      (fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point))

/-- The comparison preserves each actual free-basepoint functor injection. -/
@[reassoc (attr := simp)]
theorem basedDiscreteCoproductIso_generator (I : Type w)
    [HasCoproduct (fun _ : I =>
      (Under.costar CGWH.point.{u, max v w}).obj CGWH.point)] (i : I) :
    basedDiscreteIncl.{u, v, w} I i ≫ (basedDiscreteCoproductIso I).hom =
      Sigma.ι (fun _ : I =>
        (Under.costar CGWH.point.{u, max v w}).obj CGWH.point) i :=
  (basedDiscreteCofanIsColimit I).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct
      (fun _ : I => (Under.costar CGWH.point.{u, max v w}).obj CGWH.point)) ⟨i⟩

end PointedCGWH
