/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarCompatibility
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeBoundedSources
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderCofibration
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LevelFibrancy
public import MathlibExt.AlgebraicTopology.ModelCategory.BrownSourceFunctor
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.Topology.Category.PointedCGWH.NativeCurrentMappingSM7
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingSourceFunctor
public import MathlibExt.Topology.Category.PointedCGWH.NativeMappingZeroSource
public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
public import MathlibExt.CategoryTheory.Enriched.FreeGraded
public import MathlibExt.CategoryTheory.Presentable.FiniteSourceClosure
public import MathlibExt.CategoryTheory.SmallObject.Image
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Original free stabilization and full native mapping comparisons

These are the unchanged original free and mapping bodies, now in a
model-category API home. Native diagram statements retain all their
original source maps, full Hom functions and actual enrichment.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open CategoryTheory.BraidedCategory
open Topology
open scoped CGWH.modelCategory MonoidalClosed Cardinal Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
namespace CurrentFree

open PointedCGWH.EnrichedFunctorMapping
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The braiding comparison moving a scalar through a free enriched diagram. -/
def scalarFreeBraidComponent
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a : A) (K T : V) :
    tensorLeftObject T (Free.object a K) ≅ Free.object a (K ⊗ T) :=
  Free.scalarFreeIso T K a ≪≫ (Free.functor a).mapIso (β_ T K)

private theorem scalarFreeBraidComponent_naturality
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a : A) (K : V) {T U : V} (h : T ⟶ U) :
    scalarTensorMap h (Free.object a K) ≫ (scalarFreeBraidComponent a K U).hom =
      (scalarFreeBraidComponent a K T).hom ≫ Free.coefficientMap a (K ◁ h) := by
  simp only [scalarFreeBraidComponent, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, Free.scalarFreeIso_scalar, Category.assoc]
  rw [← (Free.functor a).map_comp, ← (Free.functor a).map_comp]
  exact congrArg (fun q => (Free.scalarFreeIso T K a).hom ≫ (Free.functor a).map q)
    (braiding_naturality_left h K)

private theorem scalarFreeBraidComponent_hom_component
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a b : A) (K T : V) :
    component (scalarFreeBraidComponent a K T).hom b =
      (α_ T K (a ⟶[V] b)).inv ≫ ((β_ T K).hom ▷ (a ⟶[V] b)) := by
  simp only [scalarFreeBraidComponent, Iso.trans_hom, Functor.mapIso_hom]
  rw [component_comp, Free.scalarFreeIso_hom_component, Free.coefficientMap_component]
  rfl

private theorem scalarFreeBraidComponent_inv_component
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a b : A) (K T : V) :
    component (scalarFreeBraidComponent a K T).inv b =
      ((β_ T K).inv ▷ (a ⟶[V] b)) ≫ (α_ T K (a ⟶[V] b)).hom := by
  simp only [scalarFreeBraidComponent, Iso.trans_inv, Functor.mapIso_inv]
  rw [component_comp, Free.scalarFreeIso_inv_component, Free.coefficientMap_component]
  rfl

private theorem rightAdjointUniq_onHom
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G G' : D ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F ⊣ G') {T : C} {X : D} (h : T ⟶ G.obj X) :
    h ≫ (Adjunction.rightAdjointUniq adj₁ adj₂).hom.app X =
      adj₂.homEquiv T X ((adj₁.homEquiv T X).symm h) := by
  apply (adj₂.homEquiv T X).symm.injective
  rw [adj₂.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Equiv.symm_apply_apply]
  rfl

private theorem rightAdjointUniq_transport_onHom
    {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj : F ⊣ G) (e : F ≅ F') (adj' : F' ⊣ G')
    {T : C} {X : D} (h : T ⟶ G.obj X) :
    h ≫ (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj').hom.app X =
      adj'.homEquiv T X (e.inv.app T ≫ (adj.homEquiv T X).symm h) := by
  rw [rightAdjointUniq_onHom, Adjunction.homEquiv_ofNatIsoLeft_symm_apply]

private theorem rightAdjointUniq_transport_ofHomEquiv
    {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj : F ⊣ G) (e : F ≅ F') (adj' : F' ⊣ G') {T : C} {X : D}
    (q : (T ⟶ G.obj X) ≃ (F.obj T ⟶ X)) (hq : adj.homEquiv T X = q.symm)
    (h : T ⟶ G.obj X) :
    h ≫ (Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj').hom.app X =
      adj'.homEquiv T X (e.inv.app T ≫ q h) := by
  rw [rightAdjointUniq_transport_onHom, hq]
  rfl

/-- Primitive native tensor/end transport is proved before choosing a free source. -/
private theorem nativeTensorMappingTransport
    (F : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {L' : PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I}
    {R' : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ PointedCGWH.{u, v}}
    (e : WeightedEndVariance.tensorBifunctor.flip.obj F ≅ L') (adj' : L' ⊣ R')
    (T : PointedCGWH.{u, v}) (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (h : T ⟶ mappingObject F X) :
    h ≫ (Adjunction.rightAdjointUniq
        ((tensorMappingAdjunction F).ofNatIsoLeft e) adj').hom.app X =
      adj'.homEquiv T X (e.inv.app T ≫ tensorHomEquiv F X T h) := by
  have hTransport := rightAdjointUniq_transport_onHom (tensorMappingAdjunction F) e adj' h
  rw [tensorMappingAdjunction_homEquiv] at hTransport
  exact hTransport

private theorem freeClosedAdjunction_homEquiv
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a : A) (K T : V)
    (X : EnrichedFunctorCat V A) (g : Free.object a (K ⊗ T) ⟶ X) :
    ((ihom.adjunction K).comp (Free.adjunction a)).homEquiv T X g =
      MonoidalClosed.curry (Free.evaluate a (K ⊗ T) X g) := by
  rw [Adjunction.comp_homEquiv, Free.adjunction_homEquiv]
  rfl

private theorem freeClosedAdjunction_symm_id
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a : A) (K : V) (X : EnrichedFunctorCat V A) :
    (((ihom.adjunction K).comp (Free.adjunction a)).homEquiv
      ((ihom K).obj (X.toEnrichedFunctor.obj a)) X).symm (𝟙 _) =
      Free.extend a (K ⊗ (ihom K).obj (X.toEnrichedFunctor.obj a)) X
        ((ihom.ev K).app (X.toEnrichedFunctor.obj a)) := by
  rw [Adjunction.comp_homEquiv, Free.adjunction_homEquiv]
  change Free.extend a _ X (MonoidalClosed.uncurry (𝟙 _)) = _
  rw [MonoidalClosed.uncurry_eq, whiskerLeft_id, Category.id_comp]

private theorem iso_inverse_square
    {C : Type*} [Category C] {A B X Y : C} (e : A ≅ X) (d : B ≅ Y)
    (f : A ⟶ B) (g : X ⟶ Y) (h : f ≫ d.hom = e.hom ≫ g) :
    g ≫ d.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem homCongr_refl_inverse
    {C : Type*} [Category C] {T X Y : C} (e : X ≅ Y) :
    ((Iso.homCongr (Iso.refl T) e).symm : (T ⟶ Y) → (T ⟶ X)) =
      fun h => h ≫ e.inv := by
  funext h
  change 𝟙 T ≫ h ≫ e.inv = h ≫ e.inv
  rw [Category.id_comp]

/-- The whole native scalar/free comparison, with the coefficient crossing restored. -/
def leftIso (a : I) (K : PointedCGWH.{u, v}) :
    WeightedEndVariance.tensorBifunctor.flip.obj (Free.object a K) ≅
      MonoidalCategory.tensorLeft K ⋙ Free.functor a :=
  NatIso.ofComponents
    (fun T => scalarFreeBraidComponent a K T)
    (fun h => by exact scalarFreeBraidComponent_naturality a K h)

private theorem leftIso_hom_app (a : I) (K T : PointedCGWH.{u, v}) :
    (leftIso a K).hom.app T = (scalarFreeBraidComponent a K T).hom := rfl

private theorem leftIso_inv_app (a : I) (K T : PointedCGWH.{u, v}) :
    (leftIso a K).inv.app T = (scalarFreeBraidComponent a K T).inv := rfl

/-- Every forward comparison component retains the actual inverse associator and braid. -/
theorem leftIso_hom_component (a b : I) (K T : PointedCGWH.{u, v}) :
    component ((leftIso a K).hom.app T) b =
      (α_ T K (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
        ((β_ T K).hom ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  exact scalarFreeBraidComponent_hom_component a b K T

/-- The actual inverse comparison keeps the reverse crossing and original associator. -/
theorem leftIso_inv_component (a b : I) (K T : PointedCGWH.{u, v}) :
    component ((leftIso a K).inv.app T) b =
      ((β_ T K).inv ▷ (a ⟶[PointedCGWH.{u, v}] b)) ≫
        (α_ T K (a ⟶[PointedCGWH.{u, v}] b)).hom := by
  exact scalarFreeBraidComponent_inv_component a b K T

/-- The native tensor/mapping adjunction transported by that exact whole left comparison. -/
def mappingAdjunction (a : I) (K : PointedCGWH.{u, v}) :
    MonoidalCategory.tensorLeft K ⋙ Free.functor a ⊣
      WeightedEndVariance.rightFunctor (Free.object a K) :=
  (tensorMappingAdjunction (Free.object a K)).ofNatIsoLeft (leftIso a K)

/-- The complete free/evaluation and fixed-left closed adjunctions, with their original maps. -/
def evaluationAdjunction (a : I) (K : PointedCGWH.{u, v}) :
    MonoidalCategory.tensorLeft K ⋙ Free.functor a ⊣ evaluation a ⋙ ihom K :=
  (ihom.adjunction K).comp (Free.adjunction a)

/-- Both native right adjoints give the full free mapping natural isomorphism. -/
def mappingNatIso (a : I) (K : PointedCGWH.{u, v}) :
    WeightedEndVariance.rightFunctor (Free.object a K) ≅ evaluation a ⋙ ihom K :=
  Adjunction.rightAdjointUniq (mappingAdjunction a K) (evaluationAdjunction a K)

/-- The current native full mapping end of a free source, with both constructed functions. -/
def mappingIso (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    mappingObject (Free.object a K) X ≅ (ihom K).obj (X.toEnrichedFunctor.obj a) :=
  (mappingNatIso a K).app X

/-- The forward function is the original scalar correspondence, actual free evaluation and curry. -/
theorem mappingIso_forward_onHom (a : I) (K T : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (h : T ⟶ mappingObject (Free.object a K) X) :
    h ≫ (mappingIso a K X).hom =
      (evaluationAdjunction a K).homEquiv T X
        ((leftIso a K).inv.app T ≫ tensorHomEquiv (Free.object a K) X T h) := by
  have hTransport := rightAdjointUniq_onHom (mappingAdjunction a K)
    (evaluationAdjunction a K) h
  have hLeft := Adjunction.homEquiv_ofNatIsoLeft_symm_apply
    (tensorMappingAdjunction (Free.object a K)) (leftIso a K) h
  have hTensor : ((tensorMappingAdjunction (Free.object a K)).homEquiv T X).symm h =
      tensorHomEquiv (Free.object a K) X T h :=
    congrArg (fun e => e.symm h)
      (tensorMappingAdjunction_homEquiv (Free.object a K) X T)
  have hValue : ((mappingAdjunction a K).homEquiv T X).symm h =
      (leftIso a K).inv.app T ≫ tensorHomEquiv (Free.object a K) X T h :=
    hLeft.trans (congrArg (fun q => (leftIso a K).inv.app T ≫ q) hTensor)
  exact hTransport.trans (congrArg ((evaluationAdjunction a K).homEquiv T X) hValue)

/-- Every target map commutes with the complete native forward reconstruction. -/
theorem mappingIso_hom_naturality (a : I) (K : PointedCGWH.{u, v})
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    WeightedEndVariance.post (Free.object a K) f ≫ (mappingIso a K Y).hom =
      (mappingIso a K X).hom ≫ (ihom K).map (component f a) := by
  have h := (mappingNatIso a K).hom.naturality f
  simp only [WeightedEndVariance.rightFunctor, Functor.comp_map, evaluation_map] at h
  exact h

/-- The inverse function retains the same whole original target-input square. -/
theorem mappingIso_inv_naturality (a : I) (K : PointedCGWH.{u, v})
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    (ihom K).map (component f a) ≫ (mappingIso a K Y).inv =
      (mappingIso a K X).inv ≫ WeightedEndVariance.post (Free.object a K) f := by
  exact iso_inverse_square (mappingIso a K X) (mappingIso a K Y)
    (WeightedEndVariance.post (Free.object a K) f) ((ihom K).map (component f a))
    (mappingIso_hom_naturality a K f)

/-- Forward and inverse are actual inverse functions on every native coefficient Hom. -/
def mappingHomEquiv (a : I) (K T : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (T ⟶ mappingObject (Free.object a K) X) ≃
      (T ⟶ (ihom K).obj (X.toEnrichedFunctor.obj a)) :=
  Iso.homCongr (Iso.refl T) (mappingIso a K X)

/-- The full forward Hom function is postcomposition by the actual free mapping function. -/
theorem mappingHomEquiv_forward (a : I) (K T : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (mappingHomEquiv a K T X :
      (T ⟶ mappingObject (Free.object a K) X) →
        (T ⟶ (ihom K).obj (X.toEnrichedFunctor.obj a))) =
      fun h => h ≫ (mappingIso a K X).hom := by
  funext h
  change 𝟙 T ≫ h ≫ (mappingIso a K X).hom = h ≫ (mappingIso a K X).hom
  rw [Category.id_comp]

/-- The complete inverse Hom function is the actual inverse mapping reconstruction. -/
theorem mappingHomEquiv_inverse (a : I) (K T : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((mappingHomEquiv a K T X).symm :
      (T ⟶ (ihom K).obj (X.toEnrichedFunctor.obj a)) →
        (T ⟶ mappingObject (Free.object a K) X)) =
      fun h => h ≫ (mappingIso a K X).inv := by
  exact homCongr_refl_inverse (mappingIso a K X)

/-- Every native scalar input keeps the full forward function square. -/
theorem mappingHomEquiv_coefficient (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {T U : PointedCGWH.{u, v}} (r : T ⟶ U)
    (h : U ⟶ mappingObject (Free.object a K) X) :
    mappingHomEquiv a K T X (r ≫ h) = r ≫ mappingHomEquiv a K U X h := by
  simp [mappingHomEquiv_forward, Category.assoc]

/-- The current native unit end is evaluated by its full free map and actual closed-unit Iso. -/
def unitMappingIso (a : I) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    mappingObject (Free.object a (𝟙_ PointedCGWH.{u, v})) X ≅
      X.toEnrichedFunctor.obj a :=
  mappingIso a (𝟙_ PointedCGWH.{u, v}) X ≪≫
    MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)

/-- The original full coefficient-to-Hom map determines the actual unit stabilization arrow. -/
def stabilization
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    Free.object b K ⟶ Free.object a (𝟙_ V) :=
  ((Free.adjunction b).homEquiv K (Free.object a (𝟙_ V))).symm
    (D ≫ (λ_ (a ⟶[V] b)).inv)

/-- Its normalized adjunct is derived from that actual definition, with no supplied law. -/
theorem stabilization_adjunct
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) :
    (Free.adjunction b).homEquiv K (Free.object a (𝟙_ V)) (stabilization a b K D) =
      D ≫ (λ_ (a ⟶[V] b)).inv :=
  ((Free.adjunction b).homEquiv K (Free.object a (𝟙_ V))).apply_symm_apply _

namespace OriginalConstructors

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {A : Type w} [EnrichedCategory V A]

/-- The original scalar/free comparison uses the supplied actual central half braid. -/
def comparison (Γ : Center V) (a : A) (M : V) :
    tensorLeftObject Γ.1 (Free.object a M) ≅ Free.object a (M ⊗ Γ.1) :=
  Free.scalarFreeIso Γ.1 M a ≪≫ (Free.functor a).mapIso (Γ.2.β M)

/-- Every complete inverse component preserves the original half braid and associator. -/
theorem comparison_inv_component (Γ : Center V) (a b : A) (M : V) :
    component (comparison Γ a M).inv b =
      ((Γ.2.β M).inv ▷ (a ⟶[V] b)) ≫ (α_ Γ.1 M (a ⟶[V] b)).hom := by
  simp only [comparison, Iso.trans_inv, Functor.mapIso_inv]
  rw [component_comp, Free.coefficientMap_component, Free.scalarFreeIso_inv_component]
  rfl

omit [BraidedCategory V] [MonoidalClosed V] in
private theorem identity_comparison (M T H : V) (e : T ⊗ M ≅ M ⊗ T)
    (q : 𝟙_ V ⟶ H) :
    (ρ_ (M ⊗ T)).inv ≫ ((M ⊗ T) ◁ q) ≫ (e.inv ▷ H) ≫ (α_ T M H).hom =
      e.inv ≫ T ◁ ((ρ_ M).inv ≫ M ◁ q) := by
  have hExchange := whisker_exchange e.inv q
  have hUnit : (ρ_ (T ⊗ M)).inv ≫ (α_ T M (𝟙_ V)).hom =
      T ◁ (ρ_ M).inv := by monoidal
  have hAssoc := associator_naturality_right T M q
  rw [reassoc_of% hExchange, ← reassoc_of% (rightUnitor_inv_naturality e.inv),
    hAssoc, reassoc_of% hUnit]
  exact congrArg (fun r => e.inv ≫ r)
    (whiskerLeft_comp T (ρ_ M).inv (M ◁ q)).symm

/-- Scalar/free transport is the actual inverse half braid followed by original grade evaluation. -/
theorem comparison_evaluate (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    Free.evaluate a (M ⊗ Γ.1) Y ((comparison Γ a M).inv ≫ gradedTensorToUnit Γ t) =
      (Γ.2.β M).inv ≫ FreeGraded.evaluationEquiv Γ a M Y t := by
  rw [Free.evaluate, component_comp, comparison_inv_component,
    gradedTensorToUnit_component, FreeGraded.evaluationEquiv_gradeFirst]
  change (ρ_ (M ⊗ Γ.1)).inv ≫ ((M ⊗ Γ.1) ◁ eId V a) ≫
      (((Γ.2.β M).inv ▷ (a ⟶[V] a)) ≫ (α_ Γ.1 M (a ⟶[V] a)).hom) ≫
      GradedNatTrans.gradeFirstComponent Γ t a =
    (Γ.2.β M).inv ≫ (Γ.1 ◁ ((ρ_ M).inv ≫ M ◁ eId V a)) ≫
      GradedNatTrans.gradeFirstComponent Γ t a
  simpa only [Category.assoc] using congrArg
    (fun r => r ≫ GradedNatTrans.gradeFirstComponent Γ t a)
    (identity_comparison M Γ.1 (a ⟶[V] a) (Γ.2.β M) (eId V a))

/-- The full constructor TYPE is fixed before every original grade, coefficient and target input. -/
def constructorFunctionType :=
  ∀ (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A),
    GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor ≃
      (Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a))

/-- The complete scalar constructor retains both actual Free adjunction and comparison functions. -/
def scalarConstructorFunction : constructorFunctionType (V := V) (A := A) :=
  fun Γ a M Y => (gradedTensorHomEquiv Γ (Free.object a M) Y).trans
    ((Iso.homCongr (comparison Γ a M) (Iso.refl Y)).trans
      (((Free.adjunction a).homEquiv (M ⊗ Γ.1) Y).trans
        ((ihom.adjunction M).homEquiv Γ.1 (Y.toEnrichedFunctor.obj a))))

/-- The complete raw constructor is the original cotensor/Free/half-braid closed correspondence. -/
def rawConstructorFunction : constructorFunctionType (V := V) (A := A) :=
  fun Γ a M Y => FreeGraded.homEquiv Γ a M Y

/-- Both entire constructor FUNCTIONS agree before any native carrier substitution. -/
theorem constructor_functions_eq :
    scalarConstructorFunction (V := V) (A := A) = rawConstructorFunction (V := V) (A := A) := by
  funext Γ a M Y
  apply Equiv.ext
  intro t
  change (ihom.adjunction M).homEquiv Γ.1 (Y.toEnrichedFunctor.obj a)
    ((Free.adjunction a).homEquiv (M ⊗ Γ.1) Y
      (Iso.homCongr (comparison Γ a M) (Iso.refl Y) (gradedTensorToUnit Γ t))) =
    FreeGraded.homEquiv Γ a M Y t
  rw [Iso.homCongr_apply]
  change MonoidalClosed.curry ((Free.adjunction a).homEquiv (M ⊗ Γ.1) Y
    ((comparison Γ a M).inv ≫ gradedTensorToUnit Γ t ≫ 𝟙 Y)) = _
  rw [Category.comp_id, Free.adjunction_homEquiv]
  change MonoidalClosed.curry
    (Free.evaluate a (M ⊗ Γ.1) Y ((comparison Γ a M).inv ≫ gradedTensorToUnit Γ t)) = _
  rw [comparison_evaluate, FreeGraded.homEquiv_factor]

/-- The same equality retains the complete inverse FUNCTIONS, on every original raw Hom. -/
theorem constructor_inverse_functions_eq :
    (fun Γ a M Y => (scalarConstructorFunction (V := V) (A := A) Γ a M Y).symm) =
      fun Γ a M Y => (rawConstructorFunction (V := V) (A := A) Γ a M Y).symm :=
  congrArg (fun f : constructorFunctionType (V := V) (A := A) =>
    fun Γ a M Y => (f Γ a M Y).symm) constructor_functions_eq

/-- The original raw inverse is normalized using both complete scalar/free maps and the unitor. -/
def rawStabilization (Γ : Center V) (a b : A) (D : Γ.1 ⟶ (a ⟶[V] b)) :
    Free.object b Γ.1 ⟶ Free.object a (𝟙_ V) :=
  (Free.functor b).map (λ_ Γ.1).inv ≫ (comparison Γ b (𝟙_ V)).inv ≫
    gradedTensorToUnit Γ
      ((FreeGraded.homEquiv Γ b (𝟙_ V) (Free.object a (𝟙_ V))).symm
        (MonoidalClosed.curry (𝟙_ V ◁ D)))

/-- Normalization is proved from both original inverse functions, with all central inputs. -/
theorem rawStabilization_adjunct (Γ : Center V) (a b : A) (D : Γ.1 ⟶ (a ⟶[V] b)) :
    (Free.adjunction b).homEquiv Γ.1 (Free.object a (𝟙_ V)) (rawStabilization Γ a b D) =
      D ≫ (λ_ (a ⟶[V] b)).inv := by
  let Y := Free.object a (𝟙_ V)
  let t := (FreeGraded.homEquiv Γ b (𝟙_ V) Y).symm
    (MonoidalClosed.curry (𝟙_ V ◁ D))
  have hEval : Free.evaluate b ((𝟙_ V) ⊗ Γ.1) Y
      ((comparison Γ b (𝟙_ V)).inv ≫ gradedTensorToUnit Γ t) = 𝟙_ V ◁ D := by
    rw [comparison_evaluate]
    have ht : FreeGraded.evaluationEquiv Γ b (𝟙_ V) Y t =
        (Γ.2.β (𝟙_ V)).hom ≫ 𝟙_ V ◁ D := by
      dsimp only [t]
      rw [FreeGraded.homEquiv_symm_factor, Equiv.apply_symm_apply,
        MonoidalClosed.uncurry_curry]
    rw [ht, Iso.inv_hom_id_assoc]
  have hNat := (Free.adjunction b).homEquiv_naturality_left (λ_ Γ.1).inv
    ((comparison Γ b (𝟙_ V)).inv ≫ gradedTensorToUnit Γ t)
  rw [Free.adjunction_homEquiv] at hNat
  rw [Free.adjunction_homEquiv]
  exact hNat.trans ((congrArg (fun r => (λ_ Γ.1).inv ≫ r) hEval).trans
    (leftUnitor_inv_naturality D).symm)

/-- Both whole stabilization FUNCTIONS agree on all original indices, grades and full Hom inputs. -/
theorem stabilization_functions_eq :
    (fun (Γ : Center V) (a b : A) (D : Γ.1 ⟶ (a ⟶[V] b)) =>
      stabilization a b Γ.1 D) =
    fun (Γ : Center V) (a b : A) (D : Γ.1 ⟶ (a ⟶[V] b)) => rawStabilization Γ a b D := by
  funext Γ a b D
  apply ((Free.adjunction b).homEquiv Γ.1 (Free.object a (𝟙_ V))).injective
  exact (stabilization_adjunct a b Γ.1 D).trans (rawStabilization_adjunct Γ a b D).symm

/-- The original canonical scalar/free braid is the same full central comparison function. -/
theorem comparison_canonical_function :
    (fun (a : A) (M T : V) => comparison ((Center.ofBraided V).obj T) a M) =
      fun (a : A) (M T : V) => scalarFreeBraidComponent a M T := rfl

end OriginalConstructors

/-- The actual coefficient-first operator action retains its complete original Hom object. -/
def action (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    K ⊗ X.toEnrichedFunctor.obj a ⟶ X.toEnrichedFunctor.obj b :=
  (D ▷ X.toEnrichedFunctor.obj a) ≫
    (β_ (X.toEnrichedFunctor.obj a) (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
      MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)

/-- The native Omega map is the transpose of the actual operator action. -/
def adjoint (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    X.toEnrichedFunctor.obj a ⟶ (ihom K).obj (X.toEnrichedFunctor.obj b) :=
  MonoidalClosed.curry (action a b K D X)

/-- Uncurrying recovers the entire original native action. -/
theorem adjoint_uncurry (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    MonoidalClosed.uncurry (adjoint a b K D X) = action a b K D X :=
  MonoidalClosed.uncurry_curry _

/-- Every genuine native spectrum transformation preserves that whole operator action. -/
theorem action_naturality (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    action a b K D X ≫ component f b =
      (K ◁ component f a) ≫ action a b K D Y := by
  have hn := f.uncurriedNaturality a b
  rw [tensorHom_id] at hn
  unfold action
  simp only [Category.assoc]
  rw [hn]
  have hb : (β_ (X.toEnrichedFunctor.obj a) (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
      (component f a ▷ (a ⟶[PointedCGWH.{u, v}] b)) =
    ((a ⟶[PointedCGWH.{u, v}] b) ◁ component f a) ≫
      (β_ (Y.toEnrichedFunctor.obj a) (a ⟶[PointedCGWH.{u, v}] b)).inv :=
    (braiding_inv_naturality_right (a ⟶[PointedCGWH.{u, v}] b) (component f a)).symm
  rw [reassoc_of% hb, ← reassoc_of% (whisker_exchange D (component f a))]

/-- All actual input maps commute with the complete native Omega transpose. -/
theorem adjoint_naturality (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    component f a ≫ adjoint a b K D Y =
      adjoint a b K D X ≫ (ihom K).map (component f b) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
    adjoint_uncurry, adjoint_uncurry]
  exact (action_naturality a b K D f).symm

/-- Original source variance is the actual full weighted-end map of the constructed arrow. -/
def mappingArrow
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type w} [EnrichedCategory V A] [HasProducts.{w} V] [HasEqualizers V]
    (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b)) (X : EnrichedFunctorCat V A) :
    WeightedEndVariance.object (Free.object a (𝟙_ V)) X ⟶
      WeightedEndVariance.object (Free.object b K) X :=
  Enriched.weightedEnd.mapWeight (Free.object a (𝟙_ V)).toEnrichedFunctor
    X.toEnrichedFunctor (Free.object b K).toEnrichedFunctor (stabilization a b K D)

private theorem originalMappingInput_naturality
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type} [EnrichedCategory V A] [HasProducts.{0} V] [HasEqualizers V]
    {WA WB X Y : EnrichedFunctorCat V A} (j : WB ⟶ WA) (f : X ⟶ Y) :
    Enriched.weightedEnd.mapDiagram WA.toEnrichedFunctor X.toEnrichedFunctor
        Y.toEnrichedFunctor f ≫
      Enriched.weightedEnd.mapWeight WA.toEnrichedFunctor Y.toEnrichedFunctor
        WB.toEnrichedFunctor j =
    Enriched.weightedEnd.mapWeight WA.toEnrichedFunctor X.toEnrichedFunctor
        WB.toEnrichedFunctor j ≫
      Enriched.weightedEnd.mapDiagram WB.toEnrichedFunctor X.toEnrichedFunctor
        Y.toEnrichedFunctor f :=
  WeightedEndVariance.pre_post j f

private theorem originalMappingProjection_pre
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type} [EnrichedCategory V A] [HasProducts.{0} V] [HasEqualizers V]
    {WA WB : EnrichedFunctorCat V A} (j : WB ⟶ WA) (X : EnrichedFunctorCat V A)
    (b : A) {K : V} (η : K ⟶ WB.toEnrichedFunctor.obj b)
    (w : K ⟶ WA.toEnrichedFunctor.obj b) (hw : η ≫ component j b = w) :
    WeightedEndVariance.pre j X ≫ WeightedEndVariance.projection WB X b ≫
        (MonoidalClosed.pre η).app (X.toEnrichedFunctor.obj b) =
      WeightedEndVariance.projection WA X b ≫
        (MonoidalClosed.pre w).app (X.toEnrichedFunctor.obj b) := by
  rw [← Category.assoc, WeightedEndVariance.pre_projection, Category.assoc,
    ← NatTrans.comp_app, ← MonoidalClosed.pre_map, hw]

private theorem iso_inv_hom_composite
    {C : Type*} [Category C] {A B D E : C} (e : A ≅ B) (f : B ⟶ D) (g : D ⟶ E) :
    e.inv ≫ (e.hom ≫ f) ≫ g = f ≫ g := by
  rw [Category.assoc, Iso.inv_hom_id_assoc]

private theorem originalSourceFactorization
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type w} [EnrichedCategory V A] [HasProducts.{w} V] [HasEqualizers V]
    {X Y Z : EnrichedFunctorCat V A} (j : X ⟶ Y) (r : Y ⟶ Z) (f : X ⟶ Z)
    (hf : j ≫ r = f) (E : EnrichedFunctorCat V A) :
    WeightedEndVariance.pre r E ≫ WeightedEndVariance.pre j E =
      WeightedEndVariance.pre f E :=
  (WeightedEndVariance.pre_comp j r E).symm.trans
    (congrArg (fun q => WeightedEndVariance.pre q E) hf)

/-- The source natural transformation induced by a morphism of enriched diagrams. -/
def originalSourceNatTrans
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type w} [EnrichedCategory V A] [HasProducts.{w} V] [HasEqualizers V]
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    WeightedEndVariance.rightFunctor Y ⟶ WeightedEndVariance.rightFunctor X :=
  WeightedEndVariance.bifunctor.map f.op

/-- Every complete target input retains the same original weighted-end source square. -/
theorem mappingArrow_naturality
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type w} [EnrichedCategory V A] [HasProducts.{w} V] [HasEqualizers V]
    (a b : A) (K : V) (D : K ⟶ (a ⟶[V] b))
    {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) :
    WeightedEndVariance.post (Free.object a (𝟙_ V)) f ≫ mappingArrow a b K D Y =
      mappingArrow a b K D X ≫ WeightedEndVariance.post (Free.object b K) f :=
  WeightedEndVariance.pre_post (stabilization a b K D) f

private theorem evaluationAdjunction_homEquiv (a : I) (K T : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (g : Free.object a (K ⊗ T) ⟶ X) :
    (evaluationAdjunction a K).homEquiv T X g =
      MonoidalClosed.curry (Free.evaluate a (K ⊗ T) X g) :=
  freeClosedAdjunction_homEquiv a K T X g

private theorem identity_evaluation_shuffle
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    (K T H : V) (e : 𝟙_ V ⟶ H) :
    (ρ_ (K ⊗ T)).inv ≫ ((K ⊗ T) ◁ e) ≫ ((β_ T K).inv ▷ H) ≫
        (α_ T K H).hom ≫ (β_ T (K ⊗ H)).hom =
      (((ρ_ K).inv ≫ K ◁ e) ▷ T) := by
  have hExchange := whisker_exchange (β_ T K).inv e
  have hUnit : (ρ_ (T ⊗ K)).inv ≫ (α_ T K (𝟙_ V)).hom =
      T ◁ (ρ_ K).inv := by monoidal
  have hAssoc := associator_naturality_right T K e
  have hBraid := braiding_naturality_right T ((ρ_ K).inv ≫ K ◁ e)
  rw [reassoc_of% hExchange, ← reassoc_of% (rightUnitor_inv_naturality (β_ T K).inv)]
  rw [reassoc_of% hAssoc, reassoc_of% hUnit]
  rw [← reassoc_of% (whiskerLeft_comp T (ρ_ K).inv (K ◁ e)), hBraid,
    Iso.inv_hom_id_assoc]

private theorem freeEvaluate_scalarCorrespondence
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a : A) (K T : V) (X : EnrichedFunctorCat V A)
    (g : tensorLeftObject T (Free.object a K) ⟶ X)
    (q : T ⟶ (ihom (K ⊗ (a ⟶[V] a))).obj (X.toEnrichedFunctor.obj a))
    (hg : component g a = (β_ T (K ⊗ (a ⟶[V] a))).hom ≫ MonoidalClosed.uncurry q) :
    Free.evaluate a (K ⊗ T) X ((scalarFreeBraidComponent a K T).inv ≫ g) =
      (((ρ_ K).inv ≫ K ◁ eId V a) ▷ T) ≫ MonoidalClosed.uncurry q := by
  rw [Free.evaluate, component_comp, scalarFreeBraidComponent_inv_component, hg]
  change (ρ_ (K ⊗ T)).inv ≫ ((K ⊗ T) ◁ eId V a) ≫
      (((β_ T K).inv ▷ (a ⟶[V] a)) ≫ (α_ T K (a ⟶[V] a)).hom) ≫
      ((β_ T (K ⊗ (a ⟶[V] a))).hom ≫ MonoidalClosed.uncurry q) = _
  simpa only [Category.assoc] using congrArg (fun r => r ≫ MonoidalClosed.uncurry q)
    (identity_evaluation_shuffle K T (a ⟶[V] a) (eId V a))

private theorem scalarFreeBraid_extend_component
    {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A : Type*} [EnrichedCategory V A] (a b : A) (K T : V) (X : EnrichedFunctorCat V A)
    (q : K ⊗ T ⟶ X.toEnrichedFunctor.obj a) :
    component ((scalarFreeBraidComponent a K T).hom ≫ Free.extend a (K ⊗ T) X q) b =
      (α_ T K (a ⟶[V] b)).inv ≫ ((β_ T K).hom ▷ (a ⟶[V] b)) ≫
        (q ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b) := by
  rw [component_comp, scalarFreeBraidComponent_hom_component, Free.extend_component]
  simp only [Free.extensionComponent, tensorHom_id]
  change ((α_ T K (a ⟶[V] b)).inv ≫ ((β_ T K).hom ▷ (a ⟶[V] b))) ≫
      ((q ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)) = _
  exact Category.assoc _ _ _

/-- The actual original free unit is derived by identity evaluation, before any mapping test. -/
theorem freeUnit_formula (a : I) (K : PointedCGWH.{u, v}) :
    (Free.adjunction a).unit.app K = (ρ_ K).inv ≫ K ◁ eId PointedCGWH.{u, v} a := by
  rw [← (Free.adjunction a).homEquiv_id K, Free.adjunction_homEquiv]
  change Free.evaluate a K (Free.object a K) (𝟙 _) = _
  rw [Free.evaluate, component_id, Category.comp_id]

/-- The complete forward map is original end projection followed by the free-unit premap. -/
theorem mappingIso_forward_formula (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (mappingIso a K X).hom = π (Free.object a K) X a ≫
      (MonoidalClosed.pre (show K ⟶ (Free.object a K).toEnrichedFunctor.obj a from
        (Free.adjunction a).unit.app K)).app
        (X.toEnrichedFunctor.obj a) := by
  let T := mappingObject (Free.object a K) X
  have h := mappingIso_forward_onHom a K T X (𝟙 T)
  rw [Category.id_comp, evaluationAdjunction_homEquiv] at h
  rw [h]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_pre_app, freeUnit_formula,
    leftIso_inv_app]
  apply freeEvaluate_scalarCorrespondence
  rw [tensorHomEquiv_component, Category.id_comp]

/-- The inverse full-end projection is derived from both actual native adjunctions. -/
theorem mappingIso_inverse_projection (a b : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (mappingIso a K X).inv ≫ π (Free.object a K) X b =
      let T := (ihom K).obj (X.toEnrichedFunctor.obj a)
      let H := a ⟶[PointedCGWH.{u, v}] b
      MonoidalClosed.curry
        ((β_ T (K ⊗ H)).inv ≫ (α_ T K H).inv ≫
          ((β_ T K).hom ▷ H) ≫ ((ihom.ev K).app (X.toEnrichedFunctor.obj a) ▷ H) ≫
          MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)) := by
  let T := (ihom K).obj (X.toEnrichedFunctor.obj a)
  let e := mappingIso a K X
  let j := tensorHomEquiv (Free.object a K) X T e.inv
  have h := mappingIso_forward_onHom a K T X e.inv
  rw [Iso.inv_hom_id] at h
  have hj : (leftIso a K).inv.app T ≫ j =
      ((evaluationAdjunction a K).homEquiv T X).symm (𝟙 T) := by
    exact ((evaluationAdjunction a K).homEquiv T X).injective
      (h.symm.trans (((evaluationAdjunction a K).homEquiv T X).apply_symm_apply _).symm)
  have hj' : j = (leftIso a K).hom.app T ≫
      Free.extend a (K ⊗ T) X ((ihom.ev K).app (X.toEnrichedFunctor.obj a)) := by
    apply (cancel_epi ((leftIso a K).inv.app T)).1
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    exact hj.trans (freeClosedAdjunction_symm_id a K X)
  have hj'' : j = (scalarFreeBraidComponent a K T).hom ≫
      Free.extend a (K ⊗ T) X ((ihom.ev K).app (X.toEnrichedFunctor.obj a)) := hj'
  have hp := (congrArg (fun q => component q b) hj'').trans
    (scalarFreeBraid_extend_component a b K T X
      ((ihom.ev K).app (X.toEnrichedFunctor.obj a)))
  have hComponent := tensorHomEquiv_component (Free.object a K) X T e.inv b
  have hp' : (β_ T (K ⊗ (a ⟶[PointedCGWH.{u, v}] b))).hom ≫
      MonoidalClosed.uncurry (e.inv ≫ π (Free.object a K) X b) =
      (α_ T K (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
        ((β_ T K).hom ▷ (a ⟶[PointedCGWH.{u, v}] b)) ≫
        ((ihom.ev K).app (X.toEnrichedFunctor.obj a) ▷
          (a ⟶[PointedCGWH.{u, v}] b)) ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b) :=
    hComponent.symm.trans hp
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  apply (cancel_epi (β_ T (K ⊗ (a ⟶[PointedCGWH.{u, v}] b))).hom).1
  change (β_ T (K ⊗ (a ⟶[PointedCGWH.{u, v}] b))).hom ≫
      MonoidalClosed.uncurry (e.inv ≫ π (Free.object a K) X b) =
    (β_ T (K ⊗ (a ⟶[PointedCGWH.{u, v}] b))).hom ≫
      (β_ T (K ⊗ (a ⟶[PointedCGWH.{u, v}] b))).inv ≫
      (α_ T K (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
      ((β_ T K).hom ▷ (a ⟶[PointedCGWH.{u, v}] b)) ≫
      ((ihom.ev K).app (X.toEnrichedFunctor.obj a) ▷
        (a ⟶[PointedCGWH.{u, v}] b)) ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map a b)
  rw [Iso.hom_inv_id_assoc]
  exact hp'

private theorem unitIsoSelf_hom_formula (U : PointedCGWH.{u, v}) :
    (MonoidalClosed.unitIsoSelf U).hom =
      (λ_ ((ihom (𝟙_ PointedCGWH.{u, v})).obj U)).inv ≫
        (ihom.ev (𝟙_ PointedCGWH.{u, v})).app U := by
  let e := MonoidalClosed.unitIsoSelf U
  have hMate : (𝟙_ PointedCGWH.{u, v} ◁ e.inv) ≫
      (ihom.ev (𝟙_ PointedCGWH.{u, v})).app U = (λ_ U).hom := by
    have h := conjugateEquiv_counit (Adjunction.id (C := PointedCGWH.{u, v}))
      (ihom.adjunction (𝟙_ PointedCGWH.{u, v}))
      (leftUnitorNatIso PointedCGWH.{u, v}).hom U
    change (𝟙_ PointedCGWH.{u, v} ◁
      (MonoidalClosed.unitNatIso (C := PointedCGWH.{u, v})).hom.app U) ≫
      (ihom.ev (𝟙_ PointedCGWH.{u, v})).app U = (λ_ U).hom ≫ 𝟙 U at h
    have hInv : e.inv = (MonoidalClosed.unitNatIso (C := PointedCGWH.{u, v})).hom.app U := rfl
    rw [← hInv] at h
    exact h.trans (Category.comp_id _)
  apply (cancel_epi e.inv).1
  change e.inv ≫ e.hom = e.inv ≫
    ((λ_ ((ihom (𝟙_ PointedCGWH.{u, v})).obj U)).inv ≫
      (ihom.ev (𝟙_ PointedCGWH.{u, v})).app U)
  rw [Iso.inv_hom_id, ← Category.assoc, leftUnitor_inv_naturality,
    Category.assoc, hMate, Iso.inv_hom_id]

private theorem normalized_unit_inverse_shuffle
    (H U : PointedCGWH.{u, v}) :
    let T := (ihom (𝟙_ PointedCGWH.{u, v})).obj U
    ((λ_ H).inv ▷ T) ≫ (β_ T ((𝟙_ PointedCGWH.{u, v}) ⊗ H)).inv ≫
      (α_ T (𝟙_ PointedCGWH.{u, v}) H).inv ≫ ((β_ T (𝟙_ PointedCGWH.{u, v})).hom ▷ H) ≫
      ((ihom.ev (𝟙_ PointedCGWH.{u, v})).app U ▷ H) =
    (β_ T H).inv ≫ ((MonoidalClosed.unitIsoSelf U).hom ▷ H) := by
  dsimp only
  let T := (ihom (𝟙_ PointedCGWH.{u, v})).obj U
  have hBraid : ((λ_ H).inv ▷ T) ≫
      (β_ T ((𝟙_ PointedCGWH.{u, v}) ⊗ H)).inv =
      (β_ T H).inv ≫ (T ◁ (λ_ H).inv) := by
    simpa only [tensorHom_id] using braiding_inv_naturality_left (λ_ H).inv T
  have hTriangle : (T ◁ (λ_ H).inv) ≫ (α_ T (𝟙_ PointedCGWH.{u, v}) H).inv =
      ((ρ_ T).inv ▷ H) := by monoidal
  have hUnit : (ρ_ T).inv ≫ (β_ T (𝟙_ PointedCGWH.{u, v})).hom = (λ_ T).inv := by
    rw [braiding_tensorUnit_right, Iso.inv_hom_id_assoc]
  have hFold : ((ρ_ T).inv ▷ H) ≫
      ((β_ T (𝟙_ PointedCGWH.{u, v})).hom ▷ H) ≫
      ((ihom.ev (𝟙_ PointedCGWH.{u, v})).app U ▷ H) =
      (MonoidalClosed.unitIsoSelf U).hom ▷ H := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, ← Category.assoc, hUnit,
      ← unitIsoSelf_hom_formula]
  rw [reassoc_of% hBraid, reassoc_of% hTriangle]
  exact congrArg (fun q => (β_ T H).inv ≫ q) hFold

/-- Precomposition by the normalized native free arrow is its complete operator transpose. -/
theorem stabilization_mapping_characteristic (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    mappingArrow a b K D X ≫ (mappingIso b K X).hom =
      (unitMappingIso a X).hom ≫ adjoint a b K D X := by
  let WA := Free.object a (𝟙_ PointedCGWH.{u, v})
  let WB := Free.object b K
  let H := a ⟶[PointedCGWH.{u, v}] b
  let T := (ihom (𝟙_ PointedCGWH.{u, v})).obj (X.toEnrichedFunctor.obj a)
  let f := stabilization a b K D
  let η : K ⟶ (Free.object b K).toEnrichedFunctor.obj b := (Free.adjunction b).unit.app K
  let fb := component f b
  have hj : η ≫ fb = D ≫ (λ_ H).inv := by
    have h := stabilization_adjunct a b K D
    rw [(Free.adjunction b).homEquiv_apply] at h
    exact h
  have hRaw : mappingArrow a b K D X ≫ (mappingIso b K X).hom =
      π WA X b ≫ (MonoidalClosed.pre (D ≫ (λ_ H).inv)).app
        (X.toEnrichedFunctor.obj b) := by
    exact (congrArg (fun q => mappingArrow a b K D X ≫ q)
      (mappingIso_forward_formula b K X)).trans
      (originalMappingProjection_pre f X b η (D ≫ (λ_ H).inv) hj)
  apply (cancel_epi (mappingIso a (𝟙_ PointedCGWH.{u, v}) X).inv).1
  rw [hRaw, unitMappingIso, Iso.trans_hom]
  have hCancel := iso_inv_hom_composite (mappingIso a (𝟙_ PointedCGWH.{u, v}) X)
    (MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom (adjoint a b K D X)
  rw [hCancel]
  rw [← Category.assoc]
  rw [mappingIso_inverse_projection]
  rw [MonoidalClosed.curry_pre_app]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left, adjoint_uncurry]
  simp only [Category.assoc, comp_whiskerRight]
  rw [reassoc_of% (normalized_unit_inverse_shuffle H (X.toEnrichedFunctor.obj a))]
  have hb : (β_ T H).inv ≫ ((MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom ▷ H) =
      (H ◁ (MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom) ≫
        (β_ (X.toEnrichedFunctor.obj a) H).inv :=
    (braiding_inv_naturality_right H
      (MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom).symm
  rw [reassoc_of% hb, ← reassoc_of% (whisker_exchange D
    (MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom)]
  rfl

/-- Both entire original native mapping maps compare with the actual Omega action in Arrow. -/
def stabilizationMappingArrowIso (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    CategoryTheory.Arrow.mk (mappingArrow a b K D X) ≅
      CategoryTheory.Arrow.mk (adjoint a b K D X) :=
  CategoryTheory.Arrow.isoMk' _ _ (unitMappingIso a X) (mappingIso b K X)
    (stabilization_mapping_characteristic a b K D X).symm

/-- Every isomorphism-invariant native class detects the same actual original Omega map. -/
theorem stabilizationMapping_property_iff
    (P : MorphismProperty PointedCGWH.{u, v}) [P.RespectsIso]
    (a b : I) (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    P (mappingArrow a b K D X) ↔ P (adjoint a b K D X) :=
  P.arrow_mk_iso_iff (stabilizationMappingArrowIso a b K D X)

/-- The canonical identity isomorphism of the native weighted-end right functor. -/
def rightFunctorNativeIso (W : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    WeightedEndVariance.rightFunctor W ≅ WeightedEndVariance.rightFunctor W :=
  Iso.refl (WeightedEndVariance.rightFunctor W)

/-- The natural isomorphism identifying free-diagram mapping objects with scalar internal Homs. -/
def rightMappingNatIso (a : I) (K : PointedCGWH.{u, v}) :
    WeightedEndVariance.rightFunctor (Free.object a K) ≅ evaluation a ⋙ ihom K :=
  rightFunctorNativeIso (Free.object a K) ≪≫ mappingNatIso a K

/-- The natural isomorphism identifying mapping from the unit free diagram with evaluation. -/
def unitRightMappingNatIso (a : I) :
    WeightedEndVariance.rightFunctor (Free.object a (𝟙_ PointedCGWH.{u, v})) ≅ evaluation a :=
  rightMappingNatIso a (𝟙_ PointedCGWH.{u, v}) ≪≫
    Functor.isoWhiskerLeft (evaluation a)
      (MonoidalClosed.unitNatIso (C := PointedCGWH.{u, v})).symm ≪≫
        (Functor.rightUnitor (evaluation a))

/-- The whole source-mapping Arrow functor retains both actual native target functors. -/
def mappingArrowFunctor (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ CategoryTheory.Arrow PointedCGWH.{u, v} :=
  CategoryTheory.NatTrans.arrow (originalSourceNatTrans (stabilization a b K D))

/-- The natural transformation adjoint to a selected enriched coefficient map. -/
def adjointNatTrans (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    evaluation a ⟶ evaluation b ⋙ ihom K where
  app X := adjoint a b K D X
  naturality _ _ f := adjoint_naturality a b K D f

/-- The Omega-action Arrow functor retains both actual component functions. -/
def adjointArrowFunctor (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ CategoryTheory.Arrow PointedCGWH.{u, v} :=
  CategoryTheory.NatTrans.arrow (adjointNatTrans a b K D)

private theorem unitMappingIso_naturality (a : I)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y) :
    WeightedEndVariance.post (Free.object a (𝟙_ PointedCGWH.{u, v})) f ≫ (unitMappingIso a Y).hom =
      (unitMappingIso a X).hom ≫ component f a := by
  have h := mappingIso_hom_naturality a (𝟙_ PointedCGWH.{u, v}) f
  have hu := (MonoidalClosed.unitNatIso (C := PointedCGWH.{u, v})).inv.naturality (component f a)
  change (ihom (𝟙_ PointedCGWH.{u, v})).map (component f a) ≫
      (MonoidalClosed.unitIsoSelf (Y.toEnrichedFunctor.obj a)).hom =
    (MonoidalClosed.unitIsoSelf (X.toEnrichedFunctor.obj a)).hom ≫ component f a at hu
  unfold unitMappingIso
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, h, Category.assoc, hu]

private theorem rightMappingNatIso_hom_app (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (rightMappingNatIso a K).hom.app X = (mappingIso a K X).hom := by
  unfold rightMappingNatIso rightFunctorNativeIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rfl

private theorem unitRightMappingNatIso_hom_app (a : I)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (unitRightMappingNatIso a).hom.app X = (unitMappingIso a X).hom := by
  unfold unitRightMappingNatIso unitMappingIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app,
    rightMappingNatIso_hom_app, Functor.rightUnitor_hom_app]
  rfl

private theorem rightMappingNatIso_app (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (rightMappingNatIso a K).app X = mappingIso a K X :=
  Iso.ext (rightMappingNatIso_hom_app a K X)

private theorem unitRightMappingNatIso_app (a : I)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (unitRightMappingNatIso a).app X = unitMappingIso a X :=
  Iso.ext (unitRightMappingNatIso_hom_app a X)

private theorem rightMappingNatIso_inv_app (a : I) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (rightMappingNatIso a K).inv.app X = (mappingIso a K X).inv :=
  congrArg Iso.inv (rightMappingNatIso_app a K X)

private theorem unitRightMappingNatIso_inv_app (a : I)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (unitRightMappingNatIso a).inv.app X = (unitMappingIso a X).inv :=
  congrArg Iso.inv (unitRightMappingNatIso_app a X)

private theorem stabilizationRightSquare (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (unitRightMappingNatIso a).hom.app X ≫ (adjointNatTrans a b K D).app X =
      (originalSourceNatTrans (stabilization a b K D)).app X ≫
        (rightMappingNatIso b K).hom.app X := by
  rw [unitRightMappingNatIso_hom_app, rightMappingNatIso_hom_app]
  exact (stabilization_mapping_characteristic a b K D X).symm

/-- Both whole native Arrow functions compare naturally on every actual input transformation. -/
def stabilizationMappingNatIso (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    mappingArrowFunctor a b K D ≅ adjointArrowFunctor a b K D :=
  NatTrans.arrowFunctorNatIso (originalSourceNatTrans (stabilization a b K D))
    (adjointNatTrans a b K D) (unitRightMappingNatIso a) (rightMappingNatIso b K)
    (by exact stabilizationRightSquare a b K D)

/-- The full forward source comparison is the actual native free-unit mapping reconstruction. -/
theorem stabilizationMappingNatIso_hom_left (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((stabilizationMappingNatIso a b K D).hom.app X).left = (unitMappingIso a X).hom :=
  (NatTrans.arrowFunctorNatIso_hom_left _ _ _ _ (stabilizationRightSquare a b K D) X).trans
    (unitRightMappingNatIso_hom_app a X)

/-- The full forward target comparison is the actual native sphere-coefficient mapping function. -/
theorem stabilizationMappingNatIso_hom_right (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((stabilizationMappingNatIso a b K D).hom.app X).right = (mappingIso b K X).hom :=
  (NatTrans.arrowFunctorNatIso_hom_right _ _ _ _ (stabilizationRightSquare a b K D) X).trans
    (rightMappingNatIso_hom_app b K X)

/-- The full inverse source comparison keeps the actual original native unit inverse function. -/
theorem stabilizationMappingNatIso_inv_left (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((stabilizationMappingNatIso a b K D).inv.app X).left = (unitMappingIso a X).inv :=
  (NatTrans.arrowFunctorNatIso_inv_left _ _ _ _ (stabilizationRightSquare a b K D) X).trans
    (unitRightMappingNatIso_inv_app a X)

/-- The full inverse target comparison keeps the actual original coefficient reconstruction. -/
theorem stabilizationMappingNatIso_inv_right (a b : I) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    ((stabilizationMappingNatIso a b K D).inv.app X).right = (mappingIso b K X).inv :=
  (NatTrans.arrowFunctorNatIso_inv_right _ _ _ _ (stabilizationRightSquare a b K D) X).trans
    (rightMappingNatIso_inv_app b K X)

end CurrentFree

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
