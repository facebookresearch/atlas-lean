/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoundaryMatching
import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# The original relative boundary–matching arrow

At every fixed outer degree, the existing inner boundary pullback-power
functor is naturally isomorphic to the existing relative matching-arrow
functor. Both pullback orders, both inverse projections, the original arrow
square and all original commutative-square naturality are retained.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace

private abbrev boundaryObject (m : ℕ) : SimplicialSpace.{u} :=
  ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (SSet.boundary.{u} m : SSet.{u}))

private abbrev simplexObject (m : ℕ) : SimplicialSpace.{u} :=
  ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[m] : SSet.{u}))

private abbrev powerFunctor (m : ℕ) : Arrow SimplicialSpace.{u} ⥤ Arrow SSet.{u} :=
  innerHomFunctor.{u}.leibnizPullback.obj
    (op (Arrow.mk (ReedyGeneratingFamilies.outerBoundaryMap.{u} m)))

private abbrev matchingFunctor (m : ℕ) : Arrow SimplicialSpace.{u} ⥤ Arrow SSet.{u} :=
  forget.{u}.mapArrow ⋙ SimplicialObject.relativeMatchingMapArrowFunctor m

private abbrev powerSquare (m : ℕ) (p : Arrow SimplicialSpace.{u}) :=
  Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
    (ReedyGeneratingFamilies.outerBoundaryMap.{u} m) p.hom

private abbrev simplexIso (m : ℕ) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.{u}.obj (op (simplexObject m))).obj Z ≅ (forget.{u}.obj Z).obj (op ⦋m⦌) :=
  SSet.Rezk.pointwiseYonedaIso m (forget.{u}.obj Z)

private abbrev boundaryIso (m : ℕ) (Z : SimplicialSpace.{u}) :=
  (boundaryMatchingIso.{u} m).app Z

private abbrev firstMap (m : ℕ) (p : Arrow SimplicialSpace.{u}) :=
  SimplicialObject.matchingMap (forget.{u}.obj p.right) m

private abbrev secondMap (m : ℕ) (p : Arrow SimplicialSpace.{u}) :=
  (SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map p.hom)

/-- The actual native square is flipped before transporting its three corners. -/
private lemma transportedPullback (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    IsPullback
      ((powerSquare m p).snd ≫ (simplexIso m p.right).hom)
      ((powerSquare m p).fst ≫ (boundaryIso m p.left).hom)
      (firstMap m p) (secondMap m p) := by
  exact (powerSquare m p).isPullback.flip.of_iso
    (Iso.refl _) (simplexIso m p.right)
    (boundaryIso m p.left) (boundaryIso m p.right)
    (by simp) (by simp)
    (boundaryMatchingIso_boundary m p.right)
    ((boundaryMatchingIso.{u} m).hom.naturality p.hom)

private def pointIso (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (powerSquare m p).pt ≅ pullback (firstMap m p) (secondMap m p) :=
  (transportedPullback m p).isoIsPullback _ _
    (IsPullback.of_hasPullback (firstMap m p) (secondMap m p))

private lemma pointIso_hom_fst (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (pointIso m p).hom ≫ pullback.fst (firstMap m p) (secondMap m p) =
      (powerSquare m p).snd ≫ (simplexIso m p.right).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ (transportedPullback m p)
    (IsPullback.of_hasPullback (firstMap m p) (secondMap m p))

private lemma pointIso_hom_snd (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (pointIso m p).hom ≫ pullback.snd (firstMap m p) (secondMap m p) =
      (powerSquare m p).fst ≫ (boundaryIso m p.left).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ (transportedPullback m p)
    (IsPullback.of_hasPullback (firstMap m p) (secondMap m p))

private lemma pointIso_inv_fst (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (pointIso m p).inv ≫ (powerSquare m p).fst =
      pullback.snd (firstMap m p) (secondMap m p) ≫ (boundaryIso m p.left).inv := by
  apply (cancel_mono (boundaryIso m p.left).hom).1
  simpa only [pointIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (IsPullback.isoIsPullback_inv_snd _ _ (transportedPullback m p)
      (IsPullback.of_hasPullback (firstMap m p) (secondMap m p)))

private lemma pointIso_inv_snd (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (pointIso m p).inv ≫ (powerSquare m p).snd =
      pullback.fst (firstMap m p) (secondMap m p) ≫ (simplexIso m p.right).inv := by
  apply (cancel_mono (simplexIso m p.right).hom).1
  simpa only [pointIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (IsPullback.isoIsPullback_inv_fst _ _ (transportedPullback m p)
      (IsPullback.of_hasPullback (firstMap m p) (secondMap m p)))

private lemma original_square (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (simplexIso m p.left).hom ≫
        SimplicialObject.relativeMatchingMap (forget.{u}.map p.hom) m =
      (powerSquare m p).π ≫ (pointIso m p).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, SimplicialObject.relativeMatchingMap_fst,
      Category.assoc, pointIso_hom_fst, ← Category.assoc,
      (powerSquare m p).π_snd]
    exact (SSet.Rezk.pointwiseYonedaIso_naturality_target m (forget.{u}.map p.hom)).symm
  · rw [Category.assoc, SimplicialObject.relativeMatchingMap_snd,
      Category.assoc, pointIso_hom_snd, ← Category.assoc,
      (powerSquare m p).π_fst]
    exact (boundaryMatchingIso_boundary m p.left).symm

private def arrowIso (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    (powerFunctor m).obj p ≅ (matchingFunctor m).obj p :=
  Arrow.isoMk (simplexIso m p.left) (pointIso m p) (original_square m p)

private lemma power_map_left (m : ℕ) {p p' : Arrow SimplicialSpace.{u}} (a : p ⟶ p') :
    ((powerFunctor m).map a).left =
      (innerHomFunctor.{u}.obj (op (simplexObject m))).map a.left := rfl

private lemma power_map_fst (m : ℕ) {p p' : Arrow SimplicialSpace.{u}} (a : p ⟶ p') :
    ((powerFunctor m).map a).right ≫ (powerSquare m p').fst =
      (powerSquare m p).fst ≫
        (innerHomFunctor.{u}.obj (op (boundaryObject m))).map a.left := by
  change (powerSquare m p').isPullback.lift _ _ _ ≫ (powerSquare m p').fst = _
  exact (powerSquare m p').isPullback.lift_fst _ _ _

private lemma power_map_snd (m : ℕ) {p p' : Arrow SimplicialSpace.{u}} (a : p ⟶ p') :
    ((powerFunctor m).map a).right ≫ (powerSquare m p').snd =
      (powerSquare m p).snd ≫
        (innerHomFunctor.{u}.obj (op (simplexObject m))).map a.right := by
  change (powerSquare m p').isPullback.lift _ _ _ ≫ (powerSquare m p').snd = _
  exact (powerSquare m p').isPullback.lift_snd _ _ _

/-- Fixed-degree relative matching is the original inner boundary pullback power,
naturally on the entire category of arrows. -/
def relativeBoundaryMatchingArrowIso (m : ℕ) :
    innerHomFunctor.{u}.leibnizPullback.obj
        (op (Arrow.mk (ReedyGeneratingFamilies.outerBoundaryMap.{u} m))) ≅
      forget.{u}.mapArrow ⋙ SimplicialObject.relativeMatchingMapArrowFunctor m :=
  NatIso.ofComponents (arrowIso m) (by
    intro p p' a
    apply Arrow.hom_ext
    · change ((powerFunctor m).map a).left ≫ (simplexIso m p'.left).hom =
        (simplexIso m p.left).hom ≫ (forget.{u}.map a.left).app (op ⦋m⦌)
      rw [power_map_left]
      exact SSet.Rezk.pointwiseYonedaIso_naturality_target m (forget.{u}.map a.left)
    · change ((powerFunctor m).map a).right ≫ (pointIso m p').hom =
        (pointIso m p).hom ≫ ((matchingFunctor m).map a).right
      have hsnd := power_map_snd m a
      have hfst := power_map_fst m a
      have hrelfst : ((matchingFunctor m).map a).right ≫
          pullback.fst (firstMap m p') (secondMap m p') =
          pullback.fst (firstMap m p) (secondMap m p) ≫
            (forget.{u}.map a.right).app (op ⦋m⦌) := by
        exact SimplicialObject.relativeMatchingMapArrowFunctor_map_right_fst m
          (forget.{u}.mapArrow.map a)
      have hrelsnd : ((matchingFunctor m).map a).right ≫
          pullback.snd (firstMap m p') (secondMap m p') =
          pullback.snd (firstMap m p) (secondMap m p) ≫
            (SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map a.left) := by
        exact SimplicialObject.relativeMatchingMapArrowFunctor_map_right_snd m
          (forget.{u}.mapArrow.map a)
      have hYoneda : (innerHomFunctor.{u}.obj (op (simplexObject m))).map a.right ≫
          (simplexIso m p'.right).hom =
          (simplexIso m p.right).hom ≫ (forget.{u}.map a.right).app (op ⦋m⦌) := by
        exact SSet.Rezk.pointwiseYonedaIso_naturality_target m (forget.{u}.map a.right)
      have hBoundary : (innerHomFunctor.{u}.obj (op (boundaryObject m))).map a.left ≫
          (boundaryIso m p'.left).hom = (boundaryIso m p.left).hom ≫
            (SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map a.left) := by
        exact (boundaryMatchingIso.{u} m).hom.naturality a.left
      dsimp only [powerFunctor, Functor.leibnizPullback] at hsnd hfst
      dsimp only [matchingFunctor, Functor.comp_map, Functor.mapArrow,
        SimplicialObject.relativeMatchingMapArrowFunctor,
        SimplicialObject.relativeMatchingObject] at hrelfst hrelsnd
      dsimp only [powerFunctor, Functor.leibnizPullback, matchingFunctor,
        Functor.comp_map, Functor.mapArrow, SimplicialObject.relativeMatchingMapArrowFunctor,
        SimplicialObject.relativeMatchingObject]
      apply pullback.hom_ext
      · rw [Category.assoc, pointIso_hom_fst, ← Category.assoc, hsnd]
        rw [Category.assoc, hYoneda]
        rw [Category.assoc, hrelfst]
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (forget.{u}.map a.right).app (op ⦋m⦌))
          (pointIso_hom_fst m p).symm
      · rw [Category.assoc, pointIso_hom_snd, ← Category.assoc, hfst]
        rw [Category.assoc, hBoundary]
        rw [Category.assoc, hrelsnd]
        simpa only [Category.assoc] using congrArg
          (fun k => k ≫ (SimplicialObject.matchingObjectFunctor m).map
            (forget.{u}.map a.left)) (pointIso_hom_snd m p).symm)

/-- The source component is the original enriched Yoneda map. -/
lemma relativeBoundaryMatchingArrowIso_hom_left (m : ℕ) (p : Arrow SimplicialSpace.{u}) :
    ((relativeBoundaryMatchingArrowIso.{u} m).app p).hom.left =
      (SSet.Rezk.pointwiseYonedaIso m p.left.diagram).hom := rfl

/-- Forward projection to the original target component. -/
@[reassoc]
lemma relativeBoundaryMatchingArrowIso_hom_right_fst (m : ℕ)
    (p : Arrow SimplicialSpace.{u}) :
    ((relativeBoundaryMatchingArrowIso.{u} m).app p).hom.right ≫
        pullback.fst (SimplicialObject.matchingMap (forget.{u}.obj p.right) m)
          ((SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map p.hom)) =
      (Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
          (ReedyGeneratingFamilies.outerBoundaryMap.{u} m) p.hom).snd ≫
        (SSet.Rezk.pointwiseYonedaIso m p.right.diagram).hom :=
  pointIso_hom_fst m p

/-- Forward projection to the original source matching object. -/
@[reassoc]
lemma relativeBoundaryMatchingArrowIso_hom_right_snd (m : ℕ)
    (p : Arrow SimplicialSpace.{u}) :
    ((relativeBoundaryMatchingArrowIso.{u} m).app p).hom.right ≫
        pullback.snd (SimplicialObject.matchingMap (forget.{u}.obj p.right) m)
          ((SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map p.hom)) =
      (Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
          (ReedyGeneratingFamilies.outerBoundaryMap.{u} m) p.hom).fst ≫
        ((boundaryMatchingIso.{u} m).app p.left).hom :=
  pointIso_hom_snd m p

/-- Inverse projection to the original boundary mapping object. -/
@[reassoc]
lemma relativeBoundaryMatchingArrowIso_inv_right_fst (m : ℕ)
    (p : Arrow SimplicialSpace.{u}) :
    ((relativeBoundaryMatchingArrowIso.{u} m).app p).inv.right ≫
        (Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
          (ReedyGeneratingFamilies.outerBoundaryMap.{u} m) p.hom).fst =
      pullback.snd (SimplicialObject.matchingMap (forget.{u}.obj p.right) m)
          ((SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map p.hom)) ≫
        ((boundaryMatchingIso.{u} m).app p.left).inv :=
  pointIso_inv_fst m p

/-- Inverse projection to the original representable mapping object. -/
@[reassoc]
lemma relativeBoundaryMatchingArrowIso_inv_right_snd (m : ℕ)
    (p : Arrow SimplicialSpace.{u}) :
    ((relativeBoundaryMatchingArrowIso.{u} m).app p).inv.right ≫
        (Functor.PullbackObjObj.ofHasPullback innerHomFunctor.{u}
          (ReedyGeneratingFamilies.outerBoundaryMap.{u} m) p.hom).snd =
      pullback.fst (SimplicialObject.matchingMap (forget.{u}.obj p.right) m)
          ((SimplicialObject.matchingObjectFunctor m).map (forget.{u}.map p.hom)) ≫
        (SSet.Rezk.pointwiseYonedaIso m p.right.diagram).inv :=
  pointIso_inv_snd m p

end SimplicialSpace
