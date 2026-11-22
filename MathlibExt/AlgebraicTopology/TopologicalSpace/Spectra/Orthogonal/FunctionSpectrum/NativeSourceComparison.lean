/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeEvaluation
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction

/-!
# Module comparison for shifted orthogonal cotensors

Constructs the free-source mapping-adjunction morphism from explicit target-object, carrier and
action laws. In the orthogonal presentation, verifies these laws for shifted cotensors and
identifies the resulting comparison with the delooping map.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uI vI uJ
open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping.SourceStage
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
open EnrichedDayKernel ModuleMappingR
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I) (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (B : EnrichedFunctor.LaxBraidedData L)

private abbrev freeFunction (r : I) (X : V) (N : Module d S L) : Module d S L := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact moduleObject d b S L B
    (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N

/-- The actual target object family is the original translated closed carrier. -/
def TargetObjectLaw (r : I) (X : V) (N T : Module d S L) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  ∀ c : I, T.X.toEnrichedFunctor.obj c =
    (ihom X).obj ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))

/-- The raw carrier retains the original whole value comparison through target reconstruction. -/
def CarrierLaw (r : I) (X : V) (N T : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    ((freeFunction d b S L B r X N).X ≅ T.X) →
      TargetObjectLaw d S L r X N T → Prop := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro e hObj
  exact ∀ c : I, component e.hom c ≫ eqToHom (hObj c) =
    (translatedValueIso d b S L r X N c).hom

/-- The original target source action is evaluation, original sphere action and the full block. -/
def TargetActionLaw (r : I) (X : V) (N T : Module d S L)
    (hObj : TargetObjectLaw d S L r X N T) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  ∀ c a : I, MonoidalClosed.uncurry
      ((eqToHom (hObj c).symm ▷ S.obj a) ≫
        ExternalRightModule.sigma d S T.X T.action c a ≫ eqToHom (hObj (c ⊗ a))) =
    (α_ X ((ihom X).obj
      ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))) (S.obj a)).inv ≫
      ((ihom.ev X).app
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) ▷ S.obj a) ≫
      ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
        (SphereModuleMappingEnd.action d S L N) (c ⊗ r) a ≫
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
        (RightShift.Internal.blockSwap r c a).hom

omit [SymmetricCategory V] [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every coefficient parameter preserves original evaluation before the complete target action. -/
theorem parameter_uncurry (X Y Z A : V) (g : Y ⊗ A ⟶ Z)
    (s : (ihom X).obj Y ⊗ A ⟶ (ihom X).obj Z)
    (hs : MonoidalClosed.uncurry s =
      (α_ X ((ihom X).obj Y) A).inv ≫ ((ihom.ev X).app Y ▷ A) ≫ g)
    {P : V} (f : P ⟶ (ihom X).obj Y) :
    MonoidalClosed.uncurry ((f ▷ A) ≫ s) =
      (α_ X P A).inv ≫ (MonoidalClosed.uncurry f ▷ A) ≫ g := by
  rw [MonoidalClosed.uncurry_natural_left, hs,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    ← MonoidalClosed.uncurry_eq]

/-- Raw free values and genuine original target source actions imply complete R-linearity. -/
theorem carrier_linear (r : I) (X : V) (N T : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    ∀ (e : (freeFunction d b S L B r X N).X ≅ T.X)
      (hObj : TargetObjectLaw d S L r X N T),
      CarrierLaw d b S L B r X N T e hObj →
      TargetActionLaw d S L r X N T hObj →
      ExternalRightModule.SourceComm d S (freeFunction d b S L B r X N).X T.X
        (freeFunction d b S L B r X N).action T.action e.hom := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro e hObj hCarrier hAction c a
  let ec := eqToIso (hObj c)
  let eca := eqToIso (hObj (c ⊗ a))
  let p := (translatedValueIso d b S L r X N c).hom
  let p' := (translatedValueIso d b S L r X N (c ⊗ a)).hom
  let u := component e.hom c
  let u' := component e.hom (c ⊗ a)
  have hc : u ≫ ec.hom = p := hCarrier c
  have hca : u' ≫ eca.hom = p' := hCarrier (c ⊗ a)
  have hcu : u = p ≫ ec.inv := by
    calc
      u = (u ≫ ec.hom) ≫ ec.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = p ≫ ec.inv := congrArg (fun f => f ≫ ec.inv) hc
  change ExternalRightModule.sigma d S (freeFunction d b S L B r X N).X
      (freeFunction d b S L B r X N).action c a ≫ u' =
    (u ⊗ₘ 𝟙 (S.obj a)) ≫ ExternalRightModule.sigma d S T.X T.action c a
  rw [tensorHom_id]
  apply (cancel_mono eca.hom).1
  rw [Category.assoc, hca, hcu, comp_whiskerRight]
  simp only [Category.assoc]
  apply MonoidalClosed.uncurry_injective (A := X)
  let s := (ec.inv ▷ S.obj a) ≫ ExternalRightModule.sigma d S T.X T.action c a ≫ eca.hom
  let g := ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
    (SphereModuleMappingEnd.action d S L N) (c ⊗ r) a ≫
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.toOrdinaryFunctor.map
      (RightShift.Internal.blockSwap r c a).hom
  have hT : MonoidalClosed.uncurry s =
      (α_ X ((ihom X).obj
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))) (S.obj a)).inv ≫
      ((ihom.ev X).app
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) ▷ S.obj a) ≫ g :=
    hAction c a
  have hParameter := parameter_uncurry X _ _ (S.obj a) g s hT p
  have hFree := translatedValueIso_sigma d b S L B r X N c a
  change MonoidalClosed.uncurry (moduleSigma d b S L B
      (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d S L r X) N c a ≫ p') =
    MonoidalClosed.uncurry ((p ▷ S.obj a) ≫ s)
  exact hFree.trans hParameter.symm

/-- The full stock output module and its actual original target, before native specialization. -/
def OutputIsoType (r : I) (X : V) (N T : Module d S L) :=
  freeFunction d b S L B r X N ≅ T

/-- Both actual module arrows are constructed from raw free values and original source actions. -/
def outputIso (r : I) (X : V) (N T : Module d S L) :
    letI := ColimitMonoidal.monoidalCategory d
    letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
    ∀ (e : (freeFunction d b S L B r X N).X ≅ T.X)
      (hObj : TargetObjectLaw d S L r X N T),
      CarrierLaw d b S L B r X N T e hObj →
      TargetActionLaw d S L r X N T hObj → OutputIsoType d b S L B r X N T := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro e hObj hCarrier hAction
  exact RightModuleFree.isoOfCarrier (⟨S⟩ : EnrichedFunctorCat V I) _ _ e
    ((ExternalRightModule.comm_iff d S _ _ _ _ _).1
      (carrier_linear d b S L B r X N T e hObj hCarrier hAction))

universe uA
omit [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Original equality transports keep their actual complete coefficient components. -/
theorem component_eqToHom {A : Type uA} [EnrichedCategory V A]
    {F G : EnrichedFunctorCat V A} (p : F = G) (a : A) :
    component (eqToHom p) a =
      eqToHom (congrArg (fun F : EnrichedFunctorCat V A => F.toEnrichedFunctor.obj a) p) := by
  cases p
  exact component_id F a

/-- The complete mapping carrier retains the actual original chosen source module endpoints. -/
def CarrierIsoType (r : I) (X : V) (N T : Module d S L) :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  (freeFunction d b S L B r X N).X ≅ T.X

/-- The original restriction inverse identifies each translated source value,
after the specified object equality, with its unchanged identity map. -/
def RestrictionInverseLaw {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L
      N) r)
    (c : I) (hObj : F.toEnrichedFunctor.obj (i.obj c) =
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) : Prop :=
  component e.inv c ≫ eqToHom hObj =
    𝟙 ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))

/-- The raw free comparison retains original value, block and reconstructed target maps. -/
def RawCarrierProperty {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L
      N) r)
    (c : I) (hObj : F.toEnrichedFunctor.obj (i.obj c) =
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r)) : Prop :=
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  component (Mapping.outputCarrierIso d b S L B i r X N F e).hom c ≫
    (ihom X).map (eqToHom hObj) = (translatedValueIso d b S L r X N c).hom

/-- Genuine original shift recovery cancels the last restriction map in every full free value. -/
theorem rawCarrier_property {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N : Module d S L) (F : EnrichedFunctorCat V J)
    (e : restrictionObject i F ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L
      N) r)
    (c : I) (hObj : F.toEnrichedFunctor.obj (i.obj c) =
      (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (c ⊗ r))
    (hInv : RestrictionInverseLaw d S L i r N F e c hObj) :
    RawCarrierProperty d b S L B i r X N F e c hObj := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have hc := Mapping.outputCarrierIso_hom_component d b S L B i r X N F e c
  let p := (translatedValueIso d b S L r X N c).hom
  let q := (ihom X).map (component e.inv c)
  let t := (ihom X).map (eqToHom hObj)
  have hqt : q ≫ t = 𝟙 _ :=
    ((ihom X).map_comp (component e.inv c) (eqToHom hObj)).symm.trans
      ((congrArg (ihom X).map hInv).trans ((ihom X).map_id _))
  change component (Mapping.outputCarrierIso d b S L B i r X N F e).hom c ≫ t = p
  have hp : component (Mapping.outputCarrierIso d b S L B i r X N F e).hom c = p ≫ q :=
    hc.trans (Category.assoc _ _ _).symm
  exact (congrArg (fun f => f ≫ t) hp).trans
    ((Category.assoc p q t).trans ((congrArg (fun f => p ≫ f) hqt).trans (Category.comp_id p)))

omit [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Equality transports compose on complete original level objects. -/
theorem object_transport_cancel {A B C : V} (p : A = B) (q : B = C) :
    eqToHom p.symm ≫ eqToHom (p.trans q) = eqToHom q := by
  cases p
  cases q
  exact Category.id_comp _

omit [SymmetricCategory V] [HasColimitsOfSize.{uI, uI} V]
  [HasProducts.{uI} V] [HasEqualizers V] in
/-- The actual closed scalar functor retains the original object equality map. -/
theorem ihom_map_eqToHom (X : V) {Y Z : V} (p : Y = Z) :
    (ihom X).map (eqToHom p) = eqToHom (congrArg (ihom X).obj p) := by
  cases p
  exact (ihom X).map_id Y

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Original restriction and actual module reconstruction determine all target level spaces. -/
theorem targetObjectsOfRestriction {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N T : Module d S L)
    (F : EnrichedFunctorCat V J)
    (hT : SphereModuleMappingEnd.diagram d S L T = restrictionObject i (cotensorObject X F))
    (hObj : ∀ c : I, F.toEnrichedFunctor.obj (i.obj c) = (SphereModuleMappingEnd.diagram d S L
      N).toEnrichedFunctor.obj (c ⊗ r)) :
    TargetObjectLaw d S L r X N T := fun c =>
  (congrArg (fun Y : EnrichedFunctorCat V I => Y.toEnrichedFunctor.obj c) hT).trans
    (congrArg (ihom X).obj (hObj c))

/-- The original complete free carrier is carried through the actual target-module equality. -/
def carrierIsoOfRestriction {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N T : Module d S L)
    (F : EnrichedFunctorCat V J)
    (hT : SphereModuleMappingEnd.diagram d S L T = restrictionObject i (cotensorObject X F))
    (e : restrictionObject i F ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L
      N) r) :
    CarrierIsoType d b S L B r X N T := by
  letI := ColimitMonoidal.monoidalCategory d
  letI : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  exact Mapping.outputCarrierIso d b S L B i r X N F e ≪≫ (eqToIso hT).symm

/-- Both genuine restriction transports retain the entire original translated value map. -/
theorem carrierIsoOfRestriction_component {J : Type uJ} [EnrichedCategory V J]
    (i : EnrichedFunctor V I J) (r : I) (X : V) (N T : Module d S L)
    (F : EnrichedFunctorCat V J)
    (hT : SphereModuleMappingEnd.diagram d S L T = restrictionObject i (cotensorObject X F))
    (hObj : ∀ c : I, F.toEnrichedFunctor.obj (i.obj c) = (SphereModuleMappingEnd.diagram d S L
      N).toEnrichedFunctor.obj (c ⊗ r))
    (e : restrictionObject i F ≅ Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L
      N) r)
    (hInv : ∀ c : I, RestrictionInverseLaw d S L i r N F e c (hObj c)) :
    CarrierLaw d b S L B r X N T
      (carrierIsoOfRestriction d b S L B i r X N T F hT e)
      (targetObjectsOfRestriction d S L i r X N T F hT hObj) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro c
  let p := congrArg (fun Y : EnrichedFunctorCat V I => Y.toEnrichedFunctor.obj c) hT
  let q := congrArg (ihom X).obj (hObj c)
  let z := component (Mapping.outputCarrierIso d b S L B i r X N F e).hom c
  have hc := rawCarrier_property d b S L B i r X N F e c (hObj c) (hInv c)
  have hp : component (carrierIsoOfRestriction d b S L B i r X N T F hT e).hom c =
      z ≫ eqToHom p.symm := by
    rw [carrierIsoOfRestriction, Iso.trans_hom, component_comp]
    simp only [Iso.symm_hom, eqToIso]
    rw [component_eqToHom]
  change component (carrierIsoOfRestriction d b S L B i r X N T F hT e).hom c ≫
    eqToHom (p.trans q) = _
  rw [hp, Category.assoc, object_transport_cancel p q, ← ihom_map_eqToHom X (hObj c)]
  exact hc

omit [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V] in
/-- The original identity object transport removes the whole final coefficient map. -/
theorem cancel_identity_transport {P Q : V} (f g : P ⟶ Q) (p : Q = Q)
    (h : f ≫ eqToHom p = g) : f = g :=
  (Category.comp_id f).symm.trans h

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Whole original module and factory equality retains every full component without rebuilding
it. -/
theorem moduleMap_component_heq {M M' N N' : Module d S L}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') (hf : HEq f g) (c : I) :
    HEq (component (SphereModuleMappingEnd.moduleMap d S L f) c)
      (component (SphereModuleMappingEnd.moduleMap d S L g) c) := by
  cases hM
  cases hN
  have h : f = g := eq_of_heq hf
  cases h
  rfl

/-- The actual stock delta followed by the proved complete original output module comparison. -/
def originalSourceComparison (r : I) (N T : Module d S L)
    (e : CarrierIsoType d b S L B r (S.obj r) N T)
    (hObj : TargetObjectLaw d S L r (S.obj r) N T)
    (hCarrier : CarrierLaw d b S L B r (S.obj r) N T e hObj)
    (hAction : TargetActionLaw d S L r (S.obj r) N T hObj) : N ⟶ T :=
  Mapping.CanonicalDelta.sourceDelta d b S L B r N ≫
    (outputIso d b S L B r (S.obj r) N T e hObj hCarrier hAction).hom

/-- The whole stock source comparison is the original coefficient-first native transpose. -/
theorem originalSourceComparison_component (r : I) (N T : Module d S L)
    (e : CarrierIsoType d b S L B r (S.obj r) N T)
    (hObj : TargetObjectLaw d S L r (S.obj r) N T)
    (hCarrier : CarrierLaw d b S L B r (S.obj r) N T e hObj)
    (hAction : TargetActionLaw d S L r (S.obj r) N T hObj) (c : I) :
    component (SphereModuleMappingEnd.moduleMap d S L
      (originalSourceComparison d b S L B r N T e hObj hCarrier hAction)) c ≫
        eqToHom (hObj c) =
      MonoidalClosed.curry ((β_ (S.obj r)
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj c)).hom ≫
        ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
          (SphereModuleMappingEnd.action d S L N) c r) := by
  let := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have he : SphereModuleMappingEnd.moduleMap d S L
      (outputIso d b S L B r (S.obj r) N T e hObj hCarrier hAction).hom = e.hom := rfl
  rw [originalSourceComparison, SphereModuleMappingEnd.moduleMap_comp, component_comp,
    Category.assoc, he]
  erw [hCarrier c, Mapping.CanonicalDelta.sourceDelta_component]
  exact Mapping.sourceDeltaValue_translated d b S L r N c

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.Mapping.SourceStage

universe u v
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.LiteralModuleStage
/-- The continuous isometry category used by the original orthogonal source. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original direct sum tensor on the continuous orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The pointed continuous enrichment of the original orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry of the continuous orthogonal index. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The continuous Day tensor on the original orthogonal spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original representation sphere monoid for the continuous Day tensor. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}
private abbrev B := orthogonalSphereBraidedData.{u, v}
open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open EnrichedDayKernel ModuleMappingR Mapping.SourceStage

/-- Every original right-shift value retains the complete literal target level. -/
theorem shift_objects (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) (c : OrthogonalIndex) :
    ((RightShift.shift r).obj F).toEnrichedFunctor.obj (indexFunctor.{u, v}.obj c) =
      (toModule F).X.toEnrichedFunctor.obj (c + r) := rfl

/-- The original scalar value of every actual shifted source module, at all input degrees. -/
theorem target_objects (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    TargetObjectLaw d.{u, v} S.{u, v} L.{u, v} r X (toModule F)
      (toModule (NativeModule.shiftedCotensor r X F)) :=
  targetObjectsOfRestriction d.{u, v} S.{u, v} L.{u, v} indexFunctor.{u, v} r X
    (toModule F) (toModule (NativeModule.shiftedCotensor r X F)) ((RightShift.shift r).obj F)
    (toModule_X (NativeModule.shiftedCotensor r X F)) (shift_objects r F)

/-- Every actual inverse shift comparison retains the original full continuous block object. -/
theorem shift_inverse (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) (c : OrthogonalIndex) :
    RestrictionInverseLaw d.{u, v} S.{u, v} L.{u, v} indexFunctor.{u, v} r (toModule F)
      ((RightShift.shift r).obj F) (FreeSource.bareShiftIso r F) c (shift_objects r F c) := by
  have h := CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso_inv_component
    d.{u, v} S.{u, v} L.{u, v} PointedCGWH.isSeparator_tensorUnit F r c
  exact (congrArg (fun z => z ≫ eqToHom (shift_objects r F c)) h).trans (Category.comp_id _)

/-- The existing original free-value isomorphism, on the actual complete source module carrier. -/
def carrierIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    Mapping.SourceStage.CarrierIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      r X (toModule F) (toModule (NativeModule.shiftedCotensor r X F)) :=
  carrierIsoOfRestriction d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} indexFunctor.{u, v}
    r X (toModule F) (toModule (NativeModule.shiftedCotensor r X F)) ((RightShift.shift r).obj F)
    (toModule_X (NativeModule.shiftedCotensor r X F)) (FreeSource.bareShiftIso r F)

/-- The whole original source map retains the same translated free-value component at every c. -/
theorem carrier_component (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u,
  v}) :
    CarrierLaw d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v} r X (toModule F)
      (toModule (NativeModule.shiftedCotensor r X F)) (carrierIso r X F) (target_objects r X F) :=
  carrierIsoOfRestriction_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    indexFunctor.{u, v} r X (toModule F) (toModule (NativeModule.shiftedCotensor r X F))
    ((RightShift.shift r).obj F) (toModule_X (NativeModule.shiftedCotensor r X F))
    (shift_objects r F) (FreeSource.bareShiftIso r F) (shift_inverse r F)

/-- Every actual native sphere action is the complete original source module action. -/
theorem source_sigma (F : NativeDiagram.{u, v}) (c a : OrthogonalIndex) :
    ExternalRightModule.sigma d.{u, v} S.{u, v} (toModule F).X (toModule F).action c a =
      SphereOperator.rightSphereAction d.{u, v} S.{u, v} L.{u, v} F c a :=
  (NativeSphereModule.sphereComponent_day_point (toModule F) c a).symm.trans
    (toModule_sphereComponent F c a)

/-- The entire actual cotensor source action is original closed evaluation followed by action. -/
theorem cotensor_sigma (X : PointedCGWH.{u, v}) (H : NativeDiagram.{u, v}) (c a : OrthogonalIndex) :
    MonoidalClosed.uncurry (A := X)
      (ExternalRightModule.sigma d.{u, v} S.{u, v} (toModule (cotensorObject X H)).X
        (toModule (cotensorObject X H)).action c a) =
      (α_ X ((ihom X).obj (H.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c)))
        (S.{u, v}.obj a)).inv ≫
      ((ihom.ev X).app (H.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c)) ▷
        S.{u, v}.obj a) ≫
      ExternalRightModule.sigma d.{u, v} S.{u, v} (toModule H).X (toModule H).action c a := by
  erw [source_sigma]
  have h := Internal.cotensorSphereAction_uncurry d.{u, v} S.{u, v} L.{u, v} H X c a
  exact h.trans (congrArg (fun q =>
    (α_ X ((ihom X).obj (H.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c)))
      (S.{u, v}.obj a)).inv ≫
    ((ihom.ev X).app (H.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c)) ▷
      S.{u, v}.obj a) ≫ q) (source_sigma H c a).symm)

/-- Every original sphere coefficient of the actual right shift retains the full source block. -/
theorem shift_sigma (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) (c a : OrthogonalIndex) :
    ExternalRightModule.sigma d.{u, v} S.{u, v} (toModule ((RightShift.shift r).obj F)).X
      (toModule ((RightShift.shift r).obj F)).action c a =
      ExternalRightModule.sigma d.{u, v} S.{u, v} (toModule F).X (toModule F).action (c + r) a ≫
        (toModule F).X.toEnrichedFunctor.toOrdinaryFunctor.map (RightShift.Internal.blockSwap r c
          a).hom := by
  have h := Internal.rightSphereAction_shift d.{u, v} S.{u, v} L.{u, v} F r c a
  exact (source_sigma ((RightShift.shift r).obj F) c a).trans
    (h.trans (congrArg (fun q => q ≫ (toModule F).X.toEnrichedFunctor.toOrdinaryFunctor.map
      (RightShift.Internal.blockSwap r c a).hom) (source_sigma F (c + r) a).symm))

/-- The actual target module action keeps original closed evaluation and the entire right block. -/
theorem target_action (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    TargetActionLaw d.{u, v} S.{u, v} L.{u, v} r X (toModule F)
      (toModule (NativeModule.shiftedCotensor r X F)) (target_objects r X F) := by
  intro c a
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp, Category.comp_id]
  erw [cotensor_sigma, shift_sigma]
  rfl

/-- Both whole stock module maps follow from the proved full original carrier and action laws. -/
def moduleIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (F : NativeDiagram.{u, v}) :
    Mapping.SourceStage.OutputIsoType d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
      r X (toModule F) (toModule (NativeModule.shiftedCotensor r X F)) :=
  Mapping.SourceStage.outputIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r X (toModule F) (toModule (NativeModule.shiftedCotensor r X F))
    (carrierIso r X F) (target_objects r X F) (carrier_component r X F) (target_action r X F)

/-- The actual shifted-loop functor has exactly the original native shift and cotensor object. -/
theorem shiftedLoop_eq (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    NativeModule.shiftedCotensor r (S.{u, v}.obj r) F = (Delooping.shiftedLoop r).obj F := rfl

/-- The actual stock source delta lands in the complete original native delooping source module. -/
def sourceComparison (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    toModule F ⟶ toModule ((Delooping.shiftedLoop r).obj F) :=
  originalSourceComparison d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r (toModule F) (toModule (NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
    (carrierIso r (S.{u, v}.obj r) F) (target_objects r (S.{u, v}.obj r) F)
    (carrier_component r (S.{u, v}.obj r) F) (target_action r (S.{u, v}.obj r) F)

/-- The literal native source comparison preserves the original whole stock construction. -/
theorem sourceComparison_factory_heq (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    HEq (sourceComparison r F)
      (originalSourceComparison d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
        r (toModule F) (toModule (NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
        (carrierIso r (S.{u, v}.obj r) F) (target_objects r (S.{u, v}.obj r) F)
        (carrier_component r (S.{u, v}.obj r) F) (target_action r (S.{u, v}.obj r) F)) := by
  rfl

/-- Every original source comparison component is the entire actual Delooping component. -/
theorem sourceComparison_component (r : OrthogonalIndex) (F : NativeDiagram.{u, v})
    (c : OrthogonalIndex) :
    component (SphereModuleMappingEnd.moduleMap d.{u, v} S.{u, v} L.{u, v}
      (sourceComparison r F)) c =
        component (Delooping.comparison r F) (OrthogonalOperatorIndex.ofIndex.{u, v} c) := by
  have h := originalSourceComparison_component d.{u, v} b.{u, v} S.{u, v} L.{u, v} B.{u, v}
    r (toModule F) (toModule (NativeModule.shiftedCotensor r (S.{u, v}.obj r) F))
    (carrierIso r (S.{u, v}.obj r) F) (target_objects r (S.{u, v}.obj r) F)
    (carrier_component r (S.{u, v}.obj r) F) (target_action r (S.{u, v}.obj r) F) c
  have hs := source_sigma F c r
  have hA := congrArg MonoidalClosed.curry (congrArg (fun q =>
    (β_ (S.{u, v}.obj r) (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} c))).hom
      ≫ q) hs)
  have hc := h.trans (hA.trans (NativeModule.comparison_source_action r F c).symm)
  have hg := cancel_identity_transport _ _ ((target_objects r (S.{u, v}.obj r) F) c) hc
  have hf := moduleMap_component_heq d.{u, v} S.{u, v} L.{u, v} rfl
    (congrArg toModule (shiftedLoop_eq r F)).symm
    (sourceComparison r F) _ (sourceComparison_factory_heq r F) c
  exact (eq_of_heq hf).trans hg

/-- The complete genuine stock delta comparison is the actual source image of Delooping. -/
theorem sourceComparison_eq (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    sourceComparison r F = toModuleFunctor.map (Delooping.comparison r F) := by
  apply SphereModuleMappingEnd.moduleMap_ext d.{u, v} S.{u, v} L.{u, v}
  apply EnrichedFunctorCat.hom_ext
  intro c
  exact (sourceComparison_component r F c).trans
    (toModuleMap_component (Delooping.comparison r F) c).symm

/-- Actual E unit and inverse unit carry the same whole stock source delta to the native carrier. -/
def nativeDeltaComparison (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    F ⟶ (Delooping.shiftedLoop r).obj F :=
  equivalence.unitIso.hom.app F ≫ fromModuleFunctor.map (sourceComparison r F) ≫
    equivalence.unitIso.inv.app ((Delooping.shiftedLoop r).obj F)

/-- The whole original stock delta on the native carrier is exactly the native Delooping map. -/
theorem nativeDeltaComparison_eq (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    nativeDeltaComparison r F = Delooping.comparison r F := by
  rw [nativeDeltaComparison, sourceComparison_eq]
  exact native_morphism_inverse (Delooping.comparison r F)

/-- The original representation-one coefficient comparison carries stock delta to the first loop. -/
def firstDeltaComparison (F : NativeDiagram.{u, v}) : F ⟶ Delooping.firstDeloopingLoop.obj F :=
  nativeDeltaComparison 1 F ≫ Delooping.firstLoopIso.hom.app (Delooping.firstDelooping.obj F)

/-- The entire original stock construction is the actual first native delta. -/
theorem firstDeltaComparison_eq (F : NativeDiagram.{u, v}) :
    firstDeltaComparison F = Delooping.delta.app F := by
  rw [firstDeltaComparison, nativeDeltaComparison_eq]
  rfl

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSourceAction.LiteralModuleStage
