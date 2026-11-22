/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryMatching
import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingIso
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Actual boundary lifts from relative matching surjectivity

Every original commuting boundary square defines a point of the actual
relative matching pullback. A preimage is the same whole simplex lift,
with both original boundary and target equations retained.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.BoundaryMatching
open SSet.ProperFaceBoundary

/-- A strict simplicial map acts on the matching comparison by the same whole original boundary postcomposition. -/
theorem matching_map_readback {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (b : SimplicialObject.matchingObject X n) :
    (matchingBoundaryIso Y n).hom ((SimplicialObject.matchingObjectFunctor n).map f b) =
      (matchingBoundaryIso X n).hom b ≫ f := by
  apply (properFaceBoundaryIsColimit.{u} n).hom_ext
  intro a
  change properFaceBoundaryInclusion.{u} a.unop ≫
      (matchingBoundaryIso Y n).hom ((SimplicialObject.matchingObjectFunctor n).map f b) =
    properFaceBoundaryInclusion.{u} a.unop ≫ ((matchingBoundaryIso X n).hom b ≫ f)
  calc
    _ = (yonedaEquiv (X := Y) (n := a.unop.obj.right.unop)).symm
        (SimplicialObject.matchingπ Y n a.unop
          ((SimplicialObject.matchingObjectFunctor n).map f b)) :=
      matchingBoundaryIso_hom_face Y n _ a.unop
    _ = (yonedaEquiv (X := Y) (n := a.unop.obj.right.unop)).symm
        (f.app a.unop.obj.right (SimplicialObject.matchingπ X n a.unop b)) :=
      congrArg (fun z : Y.obj a.unop.obj.right =>
        (yonedaEquiv (X := Y) (n := a.unop.obj.right.unop)).symm z)
          (ConcreteCategory.congr_hom (SimplicialObject.matchingObjectFunctor_map_π n f a.unop) b)
    _ = (yonedaEquiv (X := X) (n := a.unop.obj.right.unop)).symm
        (SimplicialObject.matchingπ X n a.unop b) ≫ f :=
      (yonedaEquiv_symm_comp (SimplicialObject.matchingπ X n a.unop b) f).symm
    _ = (properFaceBoundaryInclusion.{u} a.unop ≫ (matchingBoundaryIso X n).hom b) ≫ f :=
      congrArg (fun z => z ≫ f) (matchingBoundaryIso_hom_face X n b a.unop).symm
    _ = _ := Category.assoc _ _ _

private theorem square_matching_equation {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    {a : (boundary.{u} n : SSet.{u}) ⟶ X} {b : stdSimplex.obj ⦋n⦌ ⟶ Y}
    (sq : CommSq a (boundary n).ι f b) :
    SimplicialObject.matchingMap Y n (yonedaEquiv b) =
      (SimplicialObject.matchingObjectFunctor n).map f ((matchingBoundaryIso X n).inv a) := by
  apply (matchingBoundaryIso Y n).toEquiv.injective
  change (matchingBoundaryIso Y n).hom (SimplicialObject.matchingMap Y n (yonedaEquiv b)) =
    (matchingBoundaryIso Y n).hom
      ((SimplicialObject.matchingObjectFunctor n).map f ((matchingBoundaryIso X n).inv a))
  rw [matchingMap_readback, yonedaEquiv.symm_apply_apply, matching_map_readback]
  exact sq.w.symm.trans (congrArg (fun z => z ≫ f)
    ((matchingBoundaryIso X n).toEquiv.apply_symm_apply a)).symm

private def squareMatchingPoint {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    {a : (boundary.{u} n : SSet.{u}) ⟶ X} {b : stdSimplex.obj ⦋n⦌ ⟶ Y}
    (sq : CommSq a (boundary n).ι f b) : SimplicialObject.relativeMatchingObject f n :=
  (pullback.lift
    (↾fun _ : PUnit.{u + 1} => yonedaEquiv b)
    (↾fun _ : PUnit.{u + 1} => (matchingBoundaryIso X n).inv a)
    (by
      ext t
      exact square_matching_equation f n sq)) PUnit.unit

private theorem squareMatchingPoint_fst {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    {a : (boundary.{u} n : SSet.{u}) ⟶ X} {b : stdSimplex.obj ⦋n⦌ ⟶ Y}
    (sq : CommSq a (boundary n).ι f b) :
    pullback.fst (SimplicialObject.matchingMap Y n)
        ((SimplicialObject.matchingObjectFunctor n).map f) (squareMatchingPoint f n sq) =
      yonedaEquiv b :=
  ConcreteCategory.congr_hom (pullback.lift_fst
    (↾fun _ : PUnit.{u + 1} => yonedaEquiv b)
    (↾fun _ : PUnit.{u + 1} => (matchingBoundaryIso X n).inv a)
    (by
      ext t
      exact square_matching_equation f n sq)) (PUnit.unit : PUnit.{u + 1})

private theorem squareMatchingPoint_snd {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    {a : (boundary.{u} n : SSet.{u}) ⟶ X} {b : stdSimplex.obj ⦋n⦌ ⟶ Y}
    (sq : CommSq a (boundary n).ι f b) :
    pullback.snd (SimplicialObject.matchingMap Y n)
        ((SimplicialObject.matchingObjectFunctor n).map f) (squareMatchingPoint f n sq) =
      (matchingBoundaryIso X n).inv a :=
  ConcreteCategory.congr_hom (pullback.lift_snd
    (↾fun _ : PUnit.{u + 1} => yonedaEquiv b)
    (↾fun _ : PUnit.{u + 1} => (matchingBoundaryIso X n).inv a)
    (by
      ext t
      exact square_matching_equation f n sq)) (PUnit.unit : PUnit.{u + 1})

/-- Surjectivity of the actual relative matching map supplies a whole original simplex lift of every
  prescribed boundary square. -/
theorem hasLiftingProperty_boundary_of_relativeMatching_surjective {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (hf : Function.Surjective (SimplicialObject.relativeMatchingMap f n)) :
    HasLiftingProperty (boundary.{u} n).ι f := by
  refine ⟨fun {a} {b} sq => ?_⟩
  obtain ⟨x, hx⟩ := hf (squareMatchingPoint f n sq)
  have hfst : f.app (op ⦋n⦌) x = yonedaEquiv b :=
    (ConcreteCategory.congr_hom (SimplicialObject.relativeMatchingMap_fst f n) x).symm.trans
      ((congrArg (fun z => pullback.fst (SimplicialObject.matchingMap Y n)
        ((SimplicialObject.matchingObjectFunctor n).map f) z) hx).trans
          (squareMatchingPoint_fst f n sq))
  have hsnd : SimplicialObject.matchingMap X n x = (matchingBoundaryIso X n).inv a :=
    (ConcreteCategory.congr_hom (SimplicialObject.relativeMatchingMap_snd f n) x).symm.trans
      ((congrArg (fun z => pullback.snd (SimplicialObject.matchingMap Y n)
        ((SimplicialObject.matchingObjectFunctor n).map f) z) hx).trans
          (squareMatchingPoint_snd f n sq))
  apply CommSq.HasLift.mk'
  refine { l := (yonedaEquiv (X := X) (n := ⦋n⦌)).symm x, fac_left := ?_, fac_right := ?_ }
  · exact (matchingMap_readback X n x).symm.trans
      ((congrArg (fun z => (matchingBoundaryIso X n).hom z) hsnd).trans
        ((matchingBoundaryIso X n).toEquiv.apply_symm_apply a))
  · exact (yonedaEquiv_symm_comp x f).trans
      ((congrArg (fun z => (yonedaEquiv (X := Y) (n := ⦋n⦌)).symm z) hfst).trans
        ((yonedaEquiv (X := Y) (n := ⦋n⦌)).symm_apply_apply b))

end SSet.BoundaryMatching
