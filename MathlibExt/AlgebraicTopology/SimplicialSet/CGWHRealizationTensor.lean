/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationProduct
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# The original native tensor comparison of realization

The existing realization-product theorem supplies the canonical cartesian
comparison Iso. These are its actual tensor coordinates and naturality,
reusing the existing general cartesian comparison inverse laws.
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u v

namespace SSet

/-- The canonical realization tensor comparison, through the existing
cartesian product-comparison Iso. No inverse is a caller input. -/
public abbrev realizationTensorIsoCGWH (X Y : SSet.{v}) :
    SSet.toCGWH.{u, v}.obj (X ⊗ Y) ≅
      SSet.toCGWH.{u, v}.obj X ⊗ SSet.toCGWH.{u, v}.obj Y :=
  asIso (CartesianMonoidalCategory.prodComparison SSet.toCGWH.{u, v} X Y)

/-- The original first coordinate of its actual inverse. -/
@[reassoc]
public theorem realizationTensorIsoCGWH_inv_fst (X Y : SSet.{v}) :
    (realizationTensorIsoCGWH.{u, v} X Y).inv ≫
        SSet.toCGWH.{u, v}.map (CartesianMonoidalCategory.fst X Y) =
      CartesianMonoidalCategory.fst _ _ :=
  CartesianMonoidalCategory.inv_prodComparison_map_fst SSet.toCGWH.{u, v} X Y

/-- The original second coordinate of its actual inverse. -/
@[reassoc]
public theorem realizationTensorIsoCGWH_inv_snd (X Y : SSet.{v}) :
    (realizationTensorIsoCGWH.{u, v} X Y).inv ≫
        SSet.toCGWH.{u, v}.map (CartesianMonoidalCategory.snd X Y) =
      CartesianMonoidalCategory.snd _ _ :=
  CartesianMonoidalCategory.inv_prodComparison_map_snd SSet.toCGWH.{u, v} X Y

/-- Inverse naturality retains the original second simplicial map. -/
@[reassoc]
public theorem realizationTensorIsoCGWH_inv_whiskerLeft
    (X : SSet.{v}) {Y Z : SSet.{v}} (f : Y ⟶ Z) :
    (realizationTensorIsoCGWH.{u, v} X Y).inv ≫ SSet.toCGWH.{u, v}.map (X ◁ f) =
      (SSet.toCGWH.{u, v}.obj X ◁ SSet.toCGWH.{u, v}.map f) ≫
        (realizationTensorIsoCGWH.{u, v} X Z).inv :=
  CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft SSet.toCGWH.{u, v} f

/-- Inverse naturality also retains the original first simplicial map. -/
@[reassoc]
public theorem realizationTensorIsoCGWH_inv_whiskerRight
    {X X' : SSet.{v}} (f : X ⟶ X') (Y : SSet.{v}) :
    (realizationTensorIsoCGWH.{u, v} X Y).inv ≫ SSet.toCGWH.{u, v}.map (f ▷ Y) =
      (SSet.toCGWH.{u, v}.map f ▷ SSet.toCGWH.{u, v}.obj Y) ≫
        (realizationTensorIsoCGWH.{u, v} X' Y).inv :=
  CartesianMonoidalCategory.prodComparison_inv_natural_whiskerRight SSet.toCGWH.{u, v} f

end SSet

end
