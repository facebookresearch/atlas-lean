/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningMarkedEndpointComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InitialMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeIntervalCylinderExact
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCofibrations

/-!
# The same original source-projection cylinder has actual native weak images

The actual marked endpoint comparison lifts all original marked mono
parameters. The original initial-parameter corner is the same full
marked endpoint tensor through its genuine initial pushout isomorphism.
The original point-unit map identifies that tensor with the same actual
interval-cylinder endpoint. The whole original slice endpoint retains
its original base projection under the native adjunction. Its actual
target trivial cofibration and original endpoint/projection identity
prove the same native source-projection cylinder map weak. No Quillen
result, native filler or weak projection is supplied as input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private def endpointInitialProductIsInitial (D : Marked.{u}) :
    IsInitial (prod (⊥_ Marked.{u}) D) := by
  let adj := internalHomAdjunction D
  refine IsInitial.ofUniqueHom (fun Y => (adj.homEquiv (⊥_ Marked.{u}) Y).symm (initial.to _)) ?_
  intro Y f
  apply (adj.homEquiv (⊥_ Marked.{u}) Y).injective
  exact Subsingleton.elim _ _

private theorem endpointInitialProductMap_isIso :
    IsIso (prodMap (𝟙 (⊥_ Marked.{u})) cartesianEndpointCell.{u}) := by
  let A := endpointInitialProductIsInitial (min (Δ[0] : SSet.{u}))
  let D := endpointInitialProductIsInitial (max (Δ[1] : SSet.{u}))
  let e := A.uniqueUpToIso D
  have he : prodMap (𝟙 (⊥_ Marked.{u})) cartesianEndpointCell.{u} = e.hom := A.hom_ext _ _
  exact he.symm ▸ (inferInstanceAs (IsIso e.hom))

/-- The same whole original initial-parameter marked corner is its original endpoint tensor through the actual
initial pushout-point isomorphism. -/
def nativeEndpointInitialCornerIso (P : Marked.{u}) :
    Arrow.mk (prodMap (𝟙 P) cartesianEndpointCell.{u}) ≅
      Arrow.mk (markedPushoutProduct cartesianEndpointCell.{u} (initial.to P)) := by
  let sq := markedProductPushout cartesianEndpointCell.{u} (initial.to P)
  have hfirst : IsIso ((markedProductBifunctor.map cartesianEndpointCell.{u}).app (⊥_ Marked.{u})) :=
    endpointInitialProductMap_isIso
  have hinr : IsIso sq.inr := sq.isPushout.isIso_inr_of_isIso hfirst
  let e : prod P (min (Δ[0] : SSet.{u})) ≅ sq.pt := @asIso Marked.{u} _ _ _ sq.inr hinr
  exact Arrow.isoMk e (Iso.refl _)
    (sq.inr_ι.trans (Category.comp_id _).symm)

/-- Every arbitrary original marked endpoint tensor lifts the same actual native model-fibration map, through the
original marked mono comparison and genuine initial corner. -/
theorem nativeUnstraightening_map_markedEndpointTensorLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (P : Marked.{u}) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (prodMap (𝟙 P) cartesianEndpointCell.{u}) ((nativeUnstraightening B).map
      q).left := by
  let _ := coherentDiagramModelCategory B
  let _ : InitialMonoClass Marked.{u} := initialMonoClass
  dsimp only
  intro hq
  have hp := nativeUnstraightening_map_markedEndpointMonoCornerLifting B q hq (initial.to P) inferInstance
  exact (HasLiftingProperty.iff_of_arrow_iso_left (nativeEndpointInitialCornerIso P)
    ((nativeUnstraightening B).map q).left).mpr hp

/-- The original arbitrary marked parameter and minimally marked point retain their exact original point-unit
isomorphism. -/
def nativeMarkedEndpointPointUnit (P : Marked.{u}) : prod P (min (Δ[0] : SSet.{u})) ≅ P :=
  prodSwapIso P (min (Δ[0] : SSet.{u})) ≪≫ zeroParameterUnitIso .minimal P

/-- The same entire original point-unit tensor endpoint is the original actual interval-cylinder endpoint. -/
theorem nativeMarkedEndpointPointUnit_endpoint (P : Marked.{u}) :
    (nativeMarkedEndpointPointUnit P).inv ≫ prodMap (𝟙 P) cartesianEndpointCell.{u} =
      intervalCylinderEndpoint P (1 : Fin 2) := by
  apply Hom.ext
  ext n a
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro j
    rfl

/-- Both original full marked endpoint arrows are identified by the genuine original point unit, retaining the
entire original target prism. -/
def nativeOriginalCylinderEndpointArrowIso (P : Marked.{u}) :
    Arrow.mk (intervalCylinderEndpoint P (1 : Fin 2)) ≅ Arrow.mk (prodMap (𝟙 P) cartesianEndpointCell.{u}) :=
  Arrow.isoMk (nativeMarkedEndpointPointUnit P).symm (Iso.refl _)
    ((nativeMarkedEndpointPointUnit_endpoint P).trans (Category.comp_id _).symm)

/-- Every original whole marked interval-cylinder target endpoint lifts the same native map of an actual
coherent-model fibration. -/
theorem nativeUnstraightening_map_originalCylinderEndpointLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (P : Marked.{u}) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (intervalCylinderEndpoint P (1 : Fin 2)) ((nativeUnstraightening B).map q).left
      := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  exact (HasLiftingProperty.iff_of_arrow_iso_left (nativeOriginalCylinderEndpointArrowIso P)
    ((nativeUnstraightening B).map q).left).mpr (nativeUnstraightening_map_markedEndpointTensorLifting B q P hq)

/-- The same original source-projection interval endpoint in the original marked slice has its whole native lift and
unchanged original base equation. -/
theorem nativeUnstraightening_map_originalRelativeCylinderEndpointLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    Fibration q → HasLiftingProperty (((relativeIntervalCylinder (max B)).app X).endpoint (1 : Fin 2))
      ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  have hp := nativeUnstraightening_map_originalCylinderEndpointLifting B q X.left hq
  let _ : HasLiftingProperty (((relativeIntervalCylinder (max B)).app X).endpoint (1 : Fin 2)).left
      ((nativeUnstraightening B).map q).left :=
    (relativeIntervalCylinder_endpoint_left (max B) X (1 : Fin 2)).symm ▸ hp
  exact HasLiftingProperty.over _ ((nativeUnstraightening B).map q)

/-- The same original source-projection cylinder endpoint has an actual native projective weak left image over every
original marked slice object. -/
theorem nativeStraightening_originalCylinderEndpoint_projectiveWeakLeft (B : SSet.{u}) (X : Over (max B)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (((relativeIntervalCylinder (max B)).app X).endpoint (1 : Fin 2))) := by
  let _ := coherentDiagramModelCategory B
  intro F G q hq
  have hq' : Fibration q := (fibration_iff q).mpr hq
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (((relativeIntervalCylinder (max B)).app X).endpoint (1 : Fin 2)) q).mpr
      (nativeUnstraightening_map_originalRelativeCylinderEndpointLifting B q X hq')

/-- The same original native source-projection cylinder target endpoint is a trivial cofibration in the actual
coherent target model. -/
theorem nativeStraightening_originalCylinderEndpoint_trivialCofibration (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (((relativeIntervalCylinder (max B)).app X).endpoint (1 : Fin 2))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeStraightening_originalCylinderEndpoint_projectiveWeakLeft B X

/-- The same original whole source-projection cylinder map has an actual native weak image, from the original
endpoint/projection identity and proved endpoint trivial cofibration. -/
theorem nativeStraightening_originalCylinderProjection_weakEquivalence (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    WeakEquivalence ((nativeStraightening B).map ((relativeIntervalCylinder (max B)).app X).π) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  let P := (relativeIntervalCylinder (max B)).app X
  let S := nativeStraightening B
  have hi : weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ) (S.map P.i₁) :=
    (nativeStraightening_originalCylinderEndpoint_trivialCofibration B X).2
  have hfac : S.map P.i₁ ≫ S.map P.π = 𝟙 (S.obj X) :=
    (S.map_comp P.i₁ P.π).symm.trans ((congrArg S.map P.i₁_π).trans (S.map_id X))
  have hcomp : weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ) (S.map P.i₁ ≫ S.map P.π) :=
    hfac.symm ▸ (weakEquivalences (EnrichedDiagram (realization B)ᵒᵖ)).id_mem (S.obj X)
  exact (weakEquivalence_iff _).mpr (MorphismProperty.of_precomp _ _ _ hi hcomp)

/-- The actual image of the same original marked source-projection precylinder retains its original full object and
all three whole maps. -/
def nativeStraighteningOriginalPrecylinder (B : SSet.{u}) (X : Over (max B)) :
    Precylinder ((nativeStraightening B).obj X) :=
  ((relativeIntervalCylinder (max B)).app X).map (nativeStraightening B)

/-- The same native source-projection precylinder is a genuine cylinder in the actual original target model. -/
def nativeStraighteningOriginalCylinder (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    Cylinder ((nativeStraightening B).obj X) := by
  let _ := coherentDiagramModelCategory B
  exact
    { __ := nativeStraighteningOriginalPrecylinder B X
      weakEquivalence_π := nativeStraightening_originalCylinderProjection_weakEquivalence B X }

/-- The native cylinder boundary keeps the original whole coproduct comparison and original marked source boundary. -/
theorem nativeStraighteningOriginalPrecylinder_boundary (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    let _ : PreservesColimitsOfSize.{0, 0} (nativeStraightening B) :=
      (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
    (PreservesColimitPair.iso (nativeStraightening B) X X).hom ≫
      (nativeStraightening B).map ((relativeIntervalCylinder (max B)).app X).i =
        (nativeStraighteningOriginalPrecylinder B X).i := by
  let _ := coherentDiagramModelCategory B
  let S := nativeStraightening B
  let _ : PreservesColimitsOfSize.{0, 0} S := (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  dsimp only
  let P := (relativeIntervalCylinder (max B)).app X
  let Q := nativeStraighteningOriginalPrecylinder B X
  let e := PreservesColimitPair.iso S X X
  apply coprod.hom_ext
  · have he : (coprod.inl : S.obj X ⟶ S.obj X ⨿ S.obj X) ≫ e.hom = S.map (coprod.inl : X ⟶ X ⨿ X) := by
      rw [PreservesColimitPair.iso_hom]
      exact coprod.inl_desc _ _
    exact (Category.assoc (coprod.inl : S.obj X ⟶ S.obj X ⨿ S.obj X) e.hom (S.map P.i)).symm.trans
      ((congrArg (fun f => f ≫ S.map P.i) he).trans
        ((S.map_comp (coprod.inl : X ⟶ X ⨿ X) P.i).symm.trans
          ((congrArg S.map P.inl_i).trans Q.inl_i.symm)))
  · have he : (coprod.inr : S.obj X ⟶ S.obj X ⨿ S.obj X) ≫ e.hom = S.map (coprod.inr : X ⟶ X ⨿ X) := by
      rw [PreservesColimitPair.iso_hom]
      exact coprod.inr_desc _ _
    exact (Category.assoc (coprod.inr : S.obj X ⟶ S.obj X ⨿ S.obj X) e.hom (S.map P.i)).symm.trans
      ((congrArg (fun f => f ≫ S.map P.i) he).trans
        ((S.map_comp (coprod.inr : X ⟶ X ⨿ X) P.i).symm.trans
          ((congrArg S.map P.inr_i).trans Q.inr_i.symm)))

/-- The same actual native source-projection cylinder is good in the original coherent target model, through the
original marked boundary mono and whole coproduct comparison. -/
theorem nativeStraighteningOriginalCylinder_isGood (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    (nativeStraighteningOriginalCylinder B X).IsGood := by
  let _ := coherentDiagramModelCategory B
  let S := nativeStraightening B
  let _ : PreservesColimitsOfSize.{0, 0} S := (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  dsimp only
  let P := (relativeIntervalCylinder (max B)).app X
  let Q := nativeStraighteningOriginalPrecylinder B X
  let _ : Mono P.i := relativeIntervalCylinder_boundary_mono (max B) X
  have hi : cofibrations (EnrichedDiagram (realization B)ᵒᵖ) (S.map P.i) := by
    rw [coherentDiagramModel_cofibrations B]
    exact nativeStraightening_mono_projectiveLeft B P.i
  let e := PreservesColimitPair.iso S X X
  let a : Arrow.mk Q.i ≅ Arrow.mk (S.map P.i) :=
    Arrow.isoMk e (Iso.refl _) ((nativeStraighteningOriginalPrecylinder_boundary B X).trans (Category.comp_id _).symm)
  have hq : cofibrations (EnrichedDiagram (realization B)ᵒᵖ) Q.i :=
    ((cofibrations (EnrichedDiagram (realization B)ᵒᵖ)).arrow_mk_iso_iff a).mpr hi
  exact ⟨(cofibration_iff _).mpr hq⟩

end SSet.Marked
