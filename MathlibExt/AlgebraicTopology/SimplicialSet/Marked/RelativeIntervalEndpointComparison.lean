/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalProductNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseAnodyneRightReduction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundaryScalarClosure

/-!
# Original fixed-base endpoint corners lie in the actual small left class

The zero units and original product swap identify the whole supplied
endpoint pushout with the native scalar endpoint corner. Each scalar
endpoint is a genuine Kan-anodyne horn inclusion through its original
face isomorphism. The proved small horn-right reduction lifts this corner
against every actual completed right map, regardless of its codomain.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The scalar endpoint retaining the same original source/target convention. -/
def relativeIntervalScalarEndpoint (ε : Fin 2) : (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  Fin.cases (stdSimplex.δ (1 : Fin 2)) (fun _ => stdSimplex.δ (0 : Fin 2)) ε

/-- Both original scalar interval endpoints are actual native Kan-anodyne maps. -/
theorem relativeIntervalScalarEndpoint_anodyne (ε : Fin 2) :
    anodyneExtensions (relativeIntervalScalarEndpoint.{u} ε) := by
  fin_cases ε
  · change anodyneExtensions (stdSimplex.{u}.δ (1 : Fin 2))
    have hface : stdSimplex.face {0} = horn.{u} (n := 1) (0 : Fin 2) := by
      have hfin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
      rw [hfin]
      ext m x
      simp [horn_eq_iSup]
    rw [← stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
    exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
      (by rw [hface]; exact anodyneExtensions.horn_ι (0 : Fin 2))
  · change anodyneExtensions (stdSimplex.{u}.δ (0 : Fin 2))
    have hface : stdSimplex.face {1} = horn.{u} (n := 1) (1 : Fin 2) := by
      have hfin : ({1} : Finset (Fin 2)) = {0}ᶜ := by decide
      rw [hfin]
      ext m x
      simp [horn_eq_iSup]
    rw [← stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
    exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
      (by rw [hface]; exact anodyneExtensions.horn_ι (1 : Fin 2))

/-- The literal original endpoint retains its full scalar point family under the native relative coordinate swap. -/
theorem relativeIntervalEndpoint_product_map (Z : Marked.{u}) (X : Over Z) (ε : Fin 2) :
    ((relativeIntervalCylinder Z).app X).endpoint ε ≫ (relativeIntervalProductIso Z X).inv =
      (relativePointProductIso Z X).inv ≫
        (overParameterFunctor Z X).map (relativeIntervalScalarEndpoint.{u} ε) := by
  fin_cases ε <;> apply Over.OverMorphism.ext <;> apply Hom.ext <;> rfl

private theorem relativeIntervalEndpoint_product_map_forward (Z : Marked.{u}) (X : Over Z) (ε : Fin 2) :
    (relativePointProductIso Z X).hom ≫ ((relativeIntervalCylinder Z).app X).endpoint ε ≫
        (relativeIntervalProductIso Z X).inv =
      (overParameterFunctor Z X).map (relativeIntervalScalarEndpoint.{u} ε) := by
  rw [relativeIntervalEndpoint_product_map]
  exact (relativePointProductIso Z X).hom_inv_id_assoc _

/-- The actual specified endpoint pushout is its original scalar product square over the same base. -/
def relativeIntervalEndpointProductSquare {Z : Marked.{u}} {X Y : Over Z}
    (f : X ⟶ Y) (ε : Fin 2) :
    (overParameterBifunctor Z).PushoutObjObj f (relativeIntervalScalarEndpoint.{u} ε) := by
  let P := relativeIntervalCylinder Z
  let eX := (P.app X).endpoint ε
  let UX := relativePointProductIso Z X
  let UY := relativePointProductIso Z Y
  let vX := relativeIntervalProductIso Z X
  let vY := relativeIntervalProductIso Z Y
  let hp := IsPushout.of_hasPushout f eX
  refine {
    pt := pushout f eX
    inl := UY.hom ≫ pushout.inl f eX
    inr := vX.hom ≫ pushout.inr f eX
    isPushout := ?_
    ι := P.endpointCorner f ε ≫ vY.inv
    inl_ι := ?_
    inr_ι := ?_ }
  · exact hp.of_iso UX.symm UY.symm vX.symm (Iso.refl _)
      (relativePointProductIso_inv_natural f)
      ((Category.comp_id _).trans (relativeIntervalEndpoint_product_map Z X ε))
      ((Category.comp_id _).trans (UY.inv_hom_id_assoc _).symm)
      ((Category.comp_id _).trans (vX.inv_hom_id_assoc _).symm)
  · change (UY.hom ≫ pushout.inl f eX) ≫ (P.endpointCorner f ε ≫ vY.inv) = _
    rw [Category.assoc, ← Category.assoc (pushout.inl f eX), Precylinder.inl_endpointCorner]
    exact relativeIntervalEndpoint_product_map_forward Z Y ε
  · change (vX.hom ≫ pushout.inr f eX) ≫ (P.endpointCorner f ε ≫ vY.inv) = _
    rw [Category.assoc, ← Category.assoc (pushout.inr f eX), Precylinder.inr_endpointCorner]
    have h := congrArg (fun z => z ≫ vY.inv) (relativeIntervalProductIso_natural f)
    change ((overParameterMap f).app (Δ[1] : SSet.{u}) ≫ vY.hom) ≫ vY.inv =
      (vX.hom ≫ P.I.map f) ≫ vY.inv at h
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact (h.trans (Category.assoc _ _ _)).symm

/-- Native endpoint-corner comparison retains the original full source pushout and its target coordinate swap. -/
def relativeIntervalEndpointCornerIso {Z : Marked.{u}} {X Y : Over Z} (f : X ⟶ Y) (ε : Fin 2) :
    Arrow.mk (overParameterPushoutProduct (relativeIntervalScalarEndpoint.{u} ε) f) ≅
      Arrow.mk ((relativeIntervalCylinder Z).endpointCorner f ε) := by
  let s := overParameterPushout (relativeIntervalScalarEndpoint.{u} ε) f
  let t := relativeIntervalEndpointProductSquare f ε
  let e := Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk f) (f₂ := Arrow.mk (relativeIntervalScalarEndpoint.{u} ε))
    (f₂' := Arrow.mk (relativeIntervalScalarEndpoint.{u} ε)) s t (Iso.refl _)
  let h : Arrow.mk t.ι ≅ Arrow.mk ((relativeIntervalCylinder Z).endpointCorner f ε) :=
    Arrow.isoMk (Iso.refl _) (relativeIntervalProductIso Z Y) (by
      change 𝟙 _ ≫ (relativeIntervalCylinder Z).endpointCorner f ε =
        ((relativeIntervalCylinder Z).endpointCorner f ε ≫ (relativeIntervalProductIso Z Y).inv) ≫
          (relativeIntervalProductIso Z Y).hom
      rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact e ≪≫ h

/-- Every original monomorphism has both actual native endpoint corners in the completed Cartesian left class. -/
theorem cartesianRelativeBoundary_endpoint_left {B : SSet.{u}} {X Y : Over (max B)}
    (f : X ⟶ Y) [Mono f] (ε : Fin 2) :
    (cartesianRelativeBoundaryCells B).rlp.llp ((relativeIntervalCylinder (max B)).endpointCorner f ε) := by
  intro E F p hp
  have ho := antitone_rlp (cartesianFixedBaseCells_le_relativeBoundary B) _ hp
  have h := cartesianFixedBaseRight_anodyne_lifting p ho f _ (relativeIntervalScalarEndpoint_anodyne ε)
  exact (HasLiftingProperty.iff_of_arrow_iso_left (relativeIntervalEndpointCornerIso f ε) p).mp h

/-- The same original fixed-base mono has both native dual endpoint corners in the genuine dual left class. -/
theorem cocartesianRelativeBoundary_endpoint_left {B : SSet.{u}} {X Y : Over (max B)}
    (f : X ⟶ Y) [Mono f] (ε : Fin 2) :
    (cocartesianRelativeBoundaryCells B).rlp.llp ((relativeIntervalCylinder (max B)).endpointCorner f ε) := by
  intro E F p hp
  have ho := antitone_rlp (cocartesianFixedBaseCells_le_relativeBoundary B) _ hp
  have h := cocartesianFixedBaseRight_anodyne_lifting p ho f _ (relativeIntervalScalarEndpoint_anodyne ε)
  exact (HasLiftingProperty.iff_of_arrow_iso_left (relativeIntervalEndpointCornerIso f ε) p).mp h

end SSet.Marked
