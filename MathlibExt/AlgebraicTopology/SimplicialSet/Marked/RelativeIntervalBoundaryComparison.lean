/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalProductNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorLeibniz

/-!
# The entire native relative cylinder boundary is its scalar product corner

The double-point units and original coordinate swap identify the actual
specified fixed-base pushout with the scalar whole-boundary product.
Both endpoint copies, the entire original source cylinder restriction,
and the final target swap remain literal. The native cotensor comparison
therefore transposes the whole original boundary lifting problem.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

private theorem relativeBoundary_product_map (Z : Marked.{u}) (X : Over Z) :
    ((relativeIntervalCylinder Z).app X).i ≫ (relativeIntervalProductIso Z X).inv =
      (relativeDoublePointProductIso Z X).inv ≫
        (overParameterFunctor Z X).map relativeIntervalWholeBoundary.{u} := by
  have h := congrArg (fun z => z ≫ (relativeIntervalProductIso Z X).inv)
    (relativeDoublePointProductIso_boundary_inv Z X)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.symm

private theorem relativeBoundary_product_map_forward (Z : Marked.{u}) (X : Over Z) :
    (relativeDoublePointProductIso Z X).hom ≫ ((relativeIntervalCylinder Z).app X).i ≫
        (relativeIntervalProductIso Z X).inv =
      (overParameterFunctor Z X).map relativeIntervalWholeBoundary.{u} := by
  rw [relativeBoundary_product_map]
  exact (relativeDoublePointProductIso Z X).hom_inv_id_assoc _

/-- The actual full cylinder-boundary pushout is the native scalar whole-boundary square, retaining its
  whole target swap. -/
def relativeIntervalBoundaryProductSquare {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    (overParameterBifunctor Z).PushoutObjObj f relativeIntervalWholeBoundary.{u} := by
  let P := relativeIntervalCylinder Z
  let bX := (P.app X).i
  let bY := (P.app Y).i
  let dX := relativeDoublePointProductIso Z X
  let dY := relativeDoublePointProductIso Z Y
  let vX := relativeIntervalProductIso Z X
  let vY := relativeIntervalProductIso Z Y
  let hp := IsPushout.of_hasPushout (coprod.map f f) bX
  refine {
    pt := pushout (coprod.map f f) bX
    inl := dY.hom ≫ pushout.inl (coprod.map f f) bX
    inr := vX.hom ≫ pushout.inr (coprod.map f f) bX
    isPushout := ?_
    ι := P.boundaryCorner f ≫ vY.inv
    inl_ι := ?_
    inr_ι := ?_ }
  · exact hp.of_iso dX.symm dY.symm vX.symm (Iso.refl _)
      (relativeDoublePointProductIso_inv_natural f)
      ((Category.comp_id _).trans (relativeBoundary_product_map Z X))
      ((Category.comp_id _).trans (dY.inv_hom_id_assoc _).symm)
      ((Category.comp_id _).trans (vX.inv_hom_id_assoc _).symm)
  · change (dY.hom ≫ pushout.inl (coprod.map f f) bX) ≫ (P.boundaryCorner f ≫ vY.inv) = _
    rw [Category.assoc, ← Category.assoc (pushout.inl (coprod.map f f) bX), Precylinder.inl_boundaryCorner]
    exact relativeBoundary_product_map_forward Z Y
  · change (vX.hom ≫ pushout.inr (coprod.map f f) bX) ≫ (P.boundaryCorner f ≫ vY.inv) = _
    rw [Category.assoc, ← Category.assoc (pushout.inr (coprod.map f f) bX), Precylinder.inr_boundaryCorner]
    have h := congrArg (fun z => z ≫ vY.inv) (relativeIntervalProductIso_natural f)
    have hh : (overParameterMap f).app (Δ[1] : SSet.{u}) = vX.hom ≫ P.I.map f ≫ vY.inv := by
      change ((overParameterMap f).app (Δ[1] : SSet.{u}) ≫ vY.hom) ≫ vY.inv =
        (vX.hom ≫ P.I.map f) ≫ vY.inv at h
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
      exact h.trans (Category.assoc _ _ _)
    exact hh.symm

/-- The actual parameter corner and the whole original fixed-base cylinder corner are native Arrow-isomorphic. -/
def relativeIntervalBoundaryCornerIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) :
    Arrow.mk (overParameterPushoutProduct relativeIntervalWholeBoundary.{u} f) ≅
      Arrow.mk ((relativeIntervalCylinder Z).boundaryCorner f) := by
  let s := overParameterPushout relativeIntervalWholeBoundary.{u} f
  let t := relativeIntervalBoundaryProductSquare f
  let e := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk f) (f₂ := Arrow.mk relativeIntervalWholeBoundary.{u})
    (f₂' := Arrow.mk relativeIntervalWholeBoundary.{u}) s t (Iso.refl _)
  let h : Arrow.mk t.ι ≅ Arrow.mk ((relativeIntervalCylinder Z).boundaryCorner f) :=
    Arrow.isoMk (Iso.refl _) (relativeIntervalProductIso Z Y) (by
      change 𝟙 _ ≫ (relativeIntervalCylinder Z).boundaryCorner f =
        ((relativeIntervalCylinder Z).boundaryCorner f ≫ (relativeIntervalProductIso Z Y).inv) ≫
          (relativeIntervalProductIso Z Y).hom
      rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact e ≪≫ h

/-- Lifting the complete original relative cylinder boundary is exactly the supplied native cotensor comparison test. -/
theorem relativeIntervalBoundaryCorner_lifting_iff {Z : Marked.{u}} {X Y E F : Over Z}
    (f : X ⟶ Y) (p : E ⟶ F) :
    HasLiftingProperty ((relativeIntervalCylinder Z).boundaryCorner f) p ↔
      HasLiftingProperty f (overCotensorComparison relativeIntervalWholeBoundary.{u} p) :=
  (HasLiftingProperty.iff_of_arrow_iso_left (relativeIntervalBoundaryCornerIso f) p).symm.trans
    (overParameter_cotensor_lifting_iff _ f p)

end SSet.Marked
