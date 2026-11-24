/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeHornData

/-!
# Genuine full relative coherent-boundary Hom lifts

The prescribed original nerve boundary square determines its exact
target outer Hom and true endpoint equalities. Every original full
Hom boundary right-class map then lifts its monic full face union.
No local Kan target or enriched filler outcome is a premise.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeFullBoundaryData
open SimplicialEnrichment HornBoxFaces

variable {C D : Carrier.{u}} {n : ℕ}
  (F : C ⟶ D) (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ D)
  (sq : CommSq f (SSet.boundary.{u} (n+2)).ι (coherentNerveFunctor.map F)
    (SSet.yonedaEquiv.symm σ))

include sq in
/-- The same supplied full boundary square restricts to the same canonical original inner horn. -/
theorem hornSquare :
    CommSq (BoundaryFaces.horn f (1 : Fin (n+3))) (Λ[n+2,1]).ι
      (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ) :=
  ⟨(Category.assoc _ _ _).trans
    ((congrArg (fun q => SSet.Subcomplex.homOfLE (BoundaryFaces.horn_le_boundary (1 : Fin (n+3))) ≫ q)
      sq.w).trans (Category.assoc _ _ _).symm)⟩

include sq in
/-- Every actual original boundary vertex has exactly its prescribed target image. -/
theorem object_image (t : Fin (n+3)) :
    F.obj (BoundaryFaces.object f t) = σ.obj (.mk (ULift.up t)) :=
  RelativeHornData.object_image F (BoundaryFaces.horn f 1) σ (hornSquare F f σ sq) t

/-- The true original two-endpoint target Hom equality isomorphism. -/
def endpointIso :
    (F.obj (BoundaryFaces.object f 0) ⟶[SSet.{u}] F.obj (BoundaryFaces.object f (Fin.last (n+2)))) ≅
      (σ.obj (.mk (ULift.up 0)) ⟶[SSet.{u}] σ.obj (.mk (ULift.up (Fin.last (n+2))))) :=
  eqToIso (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
    (object_image F f σ sq 0) (object_image F f σ sq (Fin.last (n+2))))

/-- The entire prescribed target Hom, using precisely the same original boundary-image endpoints. -/
def targetMap : outerHom.{u} n ⟶
    (F.obj (BoundaryFaces.object f 0) ⟶[SSet.{u}] F.obj (BoundaryFaces.object f (Fin.last (n+2)))) :=
  σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))) ≫ (endpointIso F f σ sq).inv

private theorem map_congr {f₁ f₂ : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj D}
    (h : f₁ = f₂) :
    BoundaryHomGlue.map f₁ ≫
      eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
        (congrArg (fun q => BoundaryFaces.object q 0) h)
        (congrArg (fun q => BoundaryFaces.object q (Fin.last (n+2))) h)) =
      BoundaryHomGlue.map f₂ := by
  subst f₂
  exact Category.comp_id _

include sq in
/-- The full same original boundary Hom map and actual prescribed target form the genuine scalar lifting square. -/
theorem boundary_square :
    BoundaryHomGlue.map f ≫ F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
      (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ targetMap F f σ sq := by
  let E := endpointIso F f σ sq
  let M := σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2))))
  have hE : BoundaryHomGlue.map (f ≫ coherentNerveFunctor.map F) ≫ E.hom =
      BoundaryHomGlue.map (BoundaryHomNaturality.fromSimplex σ) :=
    map_congr sq.w
  have hT : BoundaryHomGlue.map (f ≫ coherentNerveFunctor.map F) ≫ E.hom =
      (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ M :=
    hE.trans (BoundaryHomNaturality.fromSimplex_map σ)
  have hI : ((BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ M) ≫ E.inv =
      BoundaryHomGlue.map (f ≫ coherentNerveFunctor.map F) :=
    (Iso.comp_inv_eq E).mpr hT.symm
  exact (BoundaryHomNaturality.map_postcompose F f).trans
    (hI.symm.trans (Category.assoc _ _ _))

/-- The actual full original scalar boundary lifting problem, with both complete specified maps. -/
theorem liftingSquare :
    CommSq (BoundaryHomGlue.map f) (BoundaryHomGlue.boundary.{u} (n := n)).ι
      (F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))))
      (targetMap F f σ sq) := ⟨boundary_square F f σ sq⟩

/-- Every full original Hom boundary right-class map lifts the SAME monic full boundary subcomplex. -/
theorem hasLiftingProperty
    (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    HasLiftingProperty (BoundaryHomGlue.boundary.{u} (n := n)).ι
      (F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))) := by
  have h := hF (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))
  rw [← SSet.rlp_monomorphisms] at h
  exact h _ (show Mono (BoundaryHomGlue.boundary.{u} (n := n)).ι from inferInstance)

/-- The SAME actual full-Hom lifting problem constructs an original outer Hom extension. -/
def outerMap
    (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    outerHom.{u} n ⟶
      (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n+2))) := by
  let _ : HasLiftingProperty (BoundaryHomGlue.boundary.{u} (n := n)).ι
      (F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))) :=
    hasLiftingProperty F f hF
  exact (liftingSquare F f σ sq).lift

/-- The actual original outer map retains the entire supplied full boundary Hom. -/
theorem outerMap_boundary
    (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ outerMap F f σ sq hF = BoundaryHomGlue.map f := by
  let _ : HasLiftingProperty (BoundaryHomGlue.boundary.{u} (n := n)).ι
      (F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))) :=
    hasLiftingProperty F f hF
  exact (liftingSquare F f σ sq).fac_left

/-- The actual original outer lift maps to the entire prescribed original target Hom. -/
theorem outerMap_target
    (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    outerMap F f σ sq hF ≫
      F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
        targetMap F f σ sq := by
  let _ : HasLiftingProperty (BoundaryHomGlue.boundary.{u} (n := n)).ι
      (F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))) :=
    hasLiftingProperty F f hF
  exact (liftingSquare F f σ sq).fac_right

end CategoryTheory.CoherentRealization.RelativeFullBoundaryData
