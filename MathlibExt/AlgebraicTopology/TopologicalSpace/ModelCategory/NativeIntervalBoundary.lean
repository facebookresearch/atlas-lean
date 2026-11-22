/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalArrows
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# The original joint endpoint arrow

The two ordered faces give an actual coproduct presentation of the simplicial
one-boundary. Native realization and the original costar functor transport
that presentation to the same two pointed units. The resulting whole Arrow
isomorphism identifies the original joint endpoints with the original native
finite boundary generator. No model or cylinder input is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial



namespace PointedCGWH.IntervalCoefficient

private abbrev boundaryRealizer : SSet.{v} ⥤ PointedCGWH.{u, v} :=
  SSet.toCGWH.{u, v} ⋙ Under.costar CGWH.point.{u, v}

private instance boundaryRealizerPreservesPair :
    PreservesColimitsOfShape (Discrete WalkingPair) boundaryRealizer.{u, v} := by
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let _ : PreservesColimits (Under.costar CGWH.point.{u, v}) :=
    (Under.costarAdjForget CGWH.point.{u, v}).leftAdjoint_preservesColimits
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The actual realized one-boundary with disjoint basepoint is the two original pointed units. -/
@[no_expose]
def boundaryPointedIso :
    (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v})) ≅
      (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v}) :=
  boundaryRealizer.mapIso SSet.boundaryOneIsoTwoPoints ≪≫
    preservesColimitIso boundaryRealizer (pair (Δ[0] : SSet.{v}) Δ[0]) ≪≫
      HasColimit.isoOfNatIso (pairComp (Δ[0] : SSet.{v}) Δ[0] boundaryRealizer) ≪≫
        coprod.mapIso ((Under.costar CGWH.point.{u, v}).mapIso zeroSimplexIsoPoint)
          ((Under.costar CGWH.point.{u, v}).mapIso zeroSimplexIsoPoint)

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryPointedIso_inl_inv_private :
    (coprod.inl : (𝟙_ PointedCGWH.{u, v}) ⟶
      (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})) ≫ boundaryPointedIso.inv =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) := by
  suffices h : (Under.costar CGWH.point.{u, v}).map zeroSimplexIsoPoint.inv ≫
      (pairComp (Δ[0] : SSet.{v}) Δ[0]
        (SSet.toCGWH.{u, v} ⋙ Under.costar CGWH.point.{u, v})).inv.app
          (Discrete.mk WalkingPair.left) ≫
        (Under.costar CGWH.point.{u, v}).map
          (SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) by
    simpa [boundaryPointedIso, boundaryRealizer,
      SSet.boundaryOneIsoTwoPoints_inl_inv, ← CategoryTheory.Functor.map_comp]
      using h
  change (Under.costar CGWH.point.{u, v}).map zeroSimplexIsoPoint.inv ≫
      𝟙 _ ≫ (Under.costar CGWH.point.{u, v}).map
        (SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) = _
  rw [Category.id_comp, CategoryTheory.Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen native boundary inverse retains the original first face and point comparison. -/
@[reassoc]
theorem boundaryPointedIso_inl_inv :
    (coprod.inl : (𝟙_ PointedCGWH.{u, v}) ⟶
      (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})) ≫ boundaryPointedIso.inv =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) :=
  boundaryPointedIso_inl_inv_private

set_option backward.isDefEq.respectTransparency false in
private theorem boundaryPointedIso_inr_inv_private :
    (coprod.inr : (𝟙_ PointedCGWH.{u, v}) ⟶
      (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})) ≫ boundaryPointedIso.inv =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) := by
  suffices h : (Under.costar CGWH.point.{u, v}).map zeroSimplexIsoPoint.inv ≫
      (pairComp (Δ[0] : SSet.{v}) Δ[0]
        (SSet.toCGWH.{u, v} ⋙ Under.costar CGWH.point.{u, v})).inv.app
          (Discrete.mk WalkingPair.right) ≫
        (Under.costar CGWH.point.{u, v}).map
          (SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) by
    simpa [boundaryPointedIso, boundaryRealizer,
      SSet.boundaryOneIsoTwoPoints_inr_inv, ← CategoryTheory.Functor.map_comp]
      using h
  change (Under.costar CGWH.point.{u, v}).map zeroSimplexIsoPoint.inv ≫
      𝟙 _ ≫ (Under.costar CGWH.point.{u, v}).map
        (SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) = _
  rw [Category.id_comp, CategoryTheory.Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The chosen native boundary inverse retains the original second face and point comparison. -/
@[reassoc]
theorem boundaryPointedIso_inr_inv :
    (coprod.inr : (𝟙_ PointedCGWH.{u, v}) ⟶
      (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v})) ≫ boundaryPointedIso.inv =
      (Under.costar CGWH.point.{u, v}).map
        (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) :=
  boundaryPointedIso_inr_inv_private

/-- The whole original joint endpoint arrow is the actual coproduct descent of both endpoints. -/
abbrev jointEndpoints :
    (𝟙_ PointedCGWH.{u, v}) ⨿ (𝟙_ PointedCGWH.{u, v}) ⟶ interval.{u, v} :=
  coprod.desc (endpoint 0) (endpoint 1)

set_option backward.isDefEq.respectTransparency false in
private def jointGeneralBoundaryArrowIso : Arrow.mk jointEndpoints.{u, v} ≅
    Arrow.mk (boundaryRealizer.{u, v}.map (SSet.boundary.{v} 1).ι) :=
  Arrow.isoMk' _ _ boundaryPointedIso.symm (Iso.refl _) (by
    rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    apply coprod.hom_ext
    · rw [← Category.assoc, boundaryPointedIso_inl_inv]
      dsimp only [jointEndpoints, boundaryRealizer]
      rw [coprod.inl_desc]
      change (Under.costar CGWH.point.{u, v}).map
          (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (0 : Fin 2))) ≫
        (Under.costar CGWH.point.{u, v}).map (SSet.toCGWH.map (SSet.boundary.{v} 1).ι) =
          endpoint 0
      rw [← CategoryTheory.Functor.map_comp, Category.assoc,
        ← CategoryTheory.Functor.map_comp, SSet.boundary.ι_ι]
      exact (endpoint_eq 0).symm
    · rw [← Category.assoc, boundaryPointedIso_inr_inv]
      dsimp only [jointEndpoints, boundaryRealizer]
      rw [coprod.inr_desc]
      change (Under.costar CGWH.point.{u, v}).map
          (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.boundary.ι (1 : Fin 2))) ≫
        (Under.costar CGWH.point.{u, v}).map (SSet.toCGWH.map (SSet.boundary.{v} 1).ι) =
          endpoint 1
      rw [← CategoryTheory.Functor.map_comp, Category.assoc,
        ← CategoryTheory.Functor.map_comp, SSet.boundary.ι_ι]
      exact (endpoint_eq 1).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The entire original joint endpoint arrow is the original costar finite boundary generator. -/
@[no_expose]
def jointBoundaryArrowIso : Arrow.mk jointEndpoints.{u, v} ≅
    Arrow.mk ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedBoundaryInclusion.{v, u} 1)) :=
  jointGeneralBoundaryArrowIso ≪≫
    (Under.costar CGWH.point.{u, v}).mapArrow.mapIso
      (CGWH.IntervalArrows.generalBoundaryArrowIso 1)

set_option backward.isDefEq.respectTransparency false in
/-- Every whole Arrow invariant recognizes the same original boundary generator. -/
theorem jointEndpoints_property_iff (W : MorphismProperty PointedCGWH.{u, v})
    [W.RespectsIso] :
    W jointEndpoints.{u, v} ↔ W ((Under.costar CGWH.point.{u, v}).map
      (CGWH.realizedBoundaryInclusion.{v, u} 1)) := W.arrow_mk_iso_iff jointBoundaryArrowIso

end PointedCGWH.IntervalCoefficient
