/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexStabilizationTransport
import MathlibExt.CategoryTheory.Enriched.FreeStabilizationKan

/-!
# Original stabilization arrows and their cylinder transports

The complete enriched index map and the original coefficient isomorphism
construct the arrow comparison. The chosen interval mapping cylinders and
correlated scalar attachments retain their actual source and target maps.

The full symmetric family keeps every original finite-bijection pair, and the
orthogonal family keeps every original dimension pair. The scalar choices are
those of `Native.OperatorStabilizationK`: the freely pointed realized boundary
and horn inclusions, with their complete original labels and coefficients.
The family comparisons use closure by genuine arrow isomorphisms.

The coend inclusion and continuous index maps follow MMSS, *Model Categories
of Diagram Spectra*, author version dated December 30, 1999, Construction 2.1
and Theorem 2.2 (pp. 9, 63), and Definition 23.1 (pp. 63–64):
https://www.math.uchicago.edu/~may/PAPERS/mmssLMSDec30.pdf.
The original native mapping-cylinder and scalar Leibniz choices implement
Definition 9.3's construction pattern (p. 29) with the source families above.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

section FreeArrows

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]

/-- The actual original free stabilization, bundled as an arrow. -/
def stabilizationArrow (a b : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) :=
  Arrow.mk (CurrentFree.stabilization a b K D)

/-- Prolongation applies its whole actual functor to the original free arrow. -/
def prolongedStabilizationArrow (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a b : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
  (leftKan j).mapArrow.obj (stabilizationArrow a b K D)

/-- The original coefficient isomorphism supplies an isomorphism of the entire free arrows. -/
def stabilizationCoefficientIso (a b : A) {S T : PointedCGWH.{u, v}}
    (e : S ≅ T) (D : T ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    stabilizationArrow a b S (e.hom ≫ D) ≅ stabilizationArrow a b T D :=
  Arrow.isoMk ((Free.functor b).mapIso e) (Iso.refl _) (by
    change (Free.functor b).map e.hom ≫ CurrentFree.stabilization a b T D =
      CurrentFree.stabilization a b S (e.hom ≫ D) ≫ 𝟙 _
    rw [Category.comp_id]
    exact CurrentFree.stabilization_coefficient a b e.hom D)

/-- The genuine free Kan comparison transports the original arrow through every full Hom. -/
def leftKanStabilizationIso (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a b : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    prolongedStabilizationArrow j a b K D ≅
      stabilizationArrow (j.obj a) (j.obj b) K (D ≫ j.map a b) :=
  Arrow.isoMk ((Kan.leftKanFreeIso j b).app K)
    ((Kan.leftKanFreeIso j a).app (𝟙_ PointedCGWH.{u, v}))
    (leftKan_stabilization j a b K D).symm

/-- A genuine coefficient isomorphism and the full inclusion equation construct the
comparison with the actual target stabilization. -/
def leftKanCoefficientStabilizationIso (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a b : A) {S T : PointedCGWH.{u, v}} (e : S ≅ T)
    (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    let sourceIndex := j.obj a
    let targetIndex := j.obj b
    let H := sourceIndex ⟶[PointedCGWH.{u, v}] targetIndex
    ∀ (E : T ⟶ H) (hD : D ≫ j.map a b = e.hom ≫ E),
      prolongedStabilizationArrow j a b S D ≅
        stabilizationArrow sourceIndex targetIndex T E := by
  dsimp only
  intro E hD
  let es := (Kan.leftKanFreeIso j b).app S
  let et := (Kan.leftKanFreeIso j a).app (𝟙_ PointedCGWH.{u, v})
  let cs := (Free.functor (j.obj b)).mapIso e
  have hstab : CurrentFree.stabilization (j.obj a) (j.obj b) S (D ≫ j.map a b) =
      (Free.functor (j.obj b)).map e.hom ≫
        CurrentFree.stabilization (j.obj a) (j.obj b) T E :=
    (congrArg (fun d : S ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) =>
      CurrentFree.stabilization (j.obj a) (j.obj b) S d) hD).trans
        (CurrentFree.stabilization_coefficient (j.obj a) (j.obj b) e.hom E).symm
  have hl : (leftKan j).map (CurrentFree.stabilization a b S D) ≫ et.hom =
      es.hom ≫ CurrentFree.stabilization (j.obj a) (j.obj b) S (D ≫ j.map a b) :=
    leftKan_stabilization j a b S D
  refine Arrow.isoMk (es ≪≫ cs) et ?_
  change (es.hom ≫ cs.hom) ≫ CurrentFree.stabilization (j.obj a) (j.obj b) T E =
    (leftKan j).map (CurrentFree.stabilization a b S D) ≫ et.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => es.hom ≫ f) hstab).symm.trans hl.symm)

end FreeArrows

section StabilizationComponents

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- Every original free stabilization component is its actual inclusion and full enriched
composition. -/
theorem stabilization_component (a b : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) (d : A) :
    component (CurrentFree.stabilization a b K D) d =
      (D ▷ (b ⟶[PointedCGWH.{u, v}] d)) ≫ eComp PointedCGWH.{u, v} a b d ≫
        (λ_ (a ⟶[PointedCGWH.{u, v}] d)).inv := by
  let H := a ⟶[PointedCGWH.{u, v}] b
  let P := b ⟶[PointedCGWH.{u, v}] d
  let Q := a ⟶[PointedCGWH.{u, v}] d
  let F := Free.object a (𝟙_ PointedCGWH.{u, v})
  have hs : CurrentFree.stabilization a b K D =
      Free.extend b K F (D ≫ (λ_ H).inv) := by
    rw [CurrentFree.stabilization, Free.adjunction_homEquiv]
    rfl
  have hAction : Free.action a (𝟙_ PointedCGWH.{u, v}) b d ≫ (λ_ Q).hom =
      (λ_ H).hom ▷ P ≫ eComp PointedCGWH.{u, v} a b d := by
    dsimp only [Free.action]
    simp only [Category.assoc]
    rw [leftUnitor_naturality, leftUnitor_tensor_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  apply (cancel_mono (λ_ Q).hom).1
  simp only [Q, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hs, Free.extend_component]
  dsimp only [Free.extensionComponent]
  rw [tensorHom_id, Free.object_uncurry_map, Category.assoc, hAction,
    ← comp_whiskerRight_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end StabilizationComponents

section FreeIndex

variable {A : Type} [Category A] [EnrichedOrdinaryCategory PointedCGWH.{u, v} A]

private theorem freeIndexMap_naturality {b c : A} (q : b ⟶ c)
    (K : PointedCGWH.{u, v}) (d e : A) :
    MonoidalClosed.uncurry ((Free.object c K).toEnrichedFunctor.map d e) ≫
        (K ◁ eHomWhiskerRight PointedCGWH.{u, v} q e) =
      ((K ◁ eHomWhiskerRight PointedCGWH.{u, v} q d) ⊗ₘ 𝟙 (d ⟶[PointedCGWH.{u, v}] e)) ≫
        MonoidalClosed.uncurry ((Free.object b K).toEnrichedFunctor.map d e) := by
  rw [Free.object_uncurry_map, Free.object_uncurry_map, tensorHom_id]
  dsimp only [Free.action]
  rw [Category.assoc, ← whiskerLeft_comp, eComp_eHomWhiskerRight, whiskerLeft_comp]
  exact (associator_naturality_middle_assoc K
    (eHomWhiskerRight PointedCGWH.{u, v} q d) (d ⟶[PointedCGWH.{u, v}] e) _).symm

/-- Contravariant index transport acts on every entire enriched Hom of the original free object. -/
def freeIndexMap {b c : A} (q : b ⟶ c) (K : PointedCGWH.{u, v}) :
    Free.object c K ⟶ Free.object b K :=
  GradedNatTrans.unitOfComponents (fun d => K ◁ eHomWhiskerRight PointedCGWH.{u, v} q d)
    (freeIndexMap_naturality q K)

/-- The original full Hom precomposition is retained at every free component. -/
theorem freeIndexMap_component {b c : A} (q : b ⟶ c) (K : PointedCGWH.{u, v}) (d : A) :
    component (freeIndexMap q K) d = K ◁ eHomWhiskerRight PointedCGWH.{u, v} q d :=
  GradedNatTrans.unitOfComponents_component _ _ d

/-- Actual contravariant free index transport keeps identities. -/
theorem freeIndexMap_id (b : A) (K : PointedCGWH.{u, v}) :
    freeIndexMap (𝟙 b) K = 𝟙 (Free.object b K) := by
  apply hom_ext
  intro d
  rw [freeIndexMap_component, component_id, eHomWhiskerRight_id, whiskerLeft_id]

/-- Actual contravariant free index transport keeps composition in its original order. -/
theorem freeIndexMap_comp {b c d : A} (q : b ⟶ c) (r : c ⟶ d)
    (K : PointedCGWH.{u, v}) :
    freeIndexMap (q ≫ r) K = freeIndexMap r K ≫ freeIndexMap q K := by
  apply hom_ext
  intro e
  rw [freeIndexMap_component, component_comp, freeIndexMap_component,
    freeIndexMap_component, eHomWhiskerRight_comp, whiskerLeft_comp]

/-- A genuine index isomorphism gives the contravariant isomorphism of whole original free
objects. -/
def freeIndexIso {b c : A} (q : b ≅ c) (K : PointedCGWH.{u, v}) :
    Free.object c K ≅ Free.object b K where
  hom := freeIndexMap q.hom K
  inv := freeIndexMap q.inv K
  hom_inv_id := by
    rw [← freeIndexMap_comp, q.inv_hom_id, freeIndexMap_id]
  inv_hom_id := by
    rw [← freeIndexMap_comp, q.hom_inv_id, freeIndexMap_id]

/-- The forward index isomorphism retains full original Hom precomposition. -/
theorem freeIndexIso_hom_component {b c : A} (q : b ≅ c)
    (K : PointedCGWH.{u, v}) (d : A) :
    component (freeIndexIso q K).hom d = K ◁ eHomWhiskerRight PointedCGWH.{u, v} q.hom d :=
  freeIndexMap_component q.hom K d

/-- The inverse index isomorphism retains full original Hom precomposition. -/
theorem freeIndexIso_inv_component {b c : A} (q : b ≅ c)
    (K : PointedCGWH.{u, v}) (d : A) :
    component (freeIndexIso q K).inv d = K ◁ eHomWhiskerRight PointedCGWH.{u, v} q.inv d :=
  freeIndexMap_component q.inv K d

@[reassoc]
private theorem eHom_middle_iso (a : A) {b c : A} (q : b ≅ c) (d : A) :
    (eHomWhiskerLeft PointedCGWH.{u, v} a q.hom ▷ (c ⟶[PointedCGWH.{u, v}] d)) ≫
      eComp PointedCGWH.{u, v} a c d =
    ((a ⟶[PointedCGWH.{u, v}] b) ◁ eHomWhiskerRight PointedCGWH.{u, v} q.hom d) ≫
      eComp PointedCGWH.{u, v} a b d := by
  have h := eHom_whisker_cancel_inv PointedCGWH.{u, v} q (X := a) (Z := d)
  have hp := congrArg
    (fun f => (eHomWhiskerLeft PointedCGWH.{u, v} a q.hom ▷
      (c ⟶[PointedCGWH.{u, v}] d)) ≫ f) h
  simp only [← comp_whiskerRight_assoc, ← eHomWhiskerLeft_comp,
    q.hom_inv_id, eHomWhiskerLeft_id, id_whiskerRight_assoc] at hp
  exact hp.symm

/-- The actual target-index isomorphism transports the entire original free stabilization. -/
theorem stabilization_target_iso (a : A) {b c : A} (q : b ≅ c)
    (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    freeIndexMap q.hom K ≫ CurrentFree.stabilization a b K D =
      CurrentFree.stabilization a c K (D ≫ eHomWhiskerLeft PointedCGWH.{u, v} a q.hom) := by
  apply hom_ext
  intro d
  rw [component_comp, freeIndexMap_component, stabilization_component,
    stabilization_component, comp_whiskerRight]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, eHom_middle_iso_assoc]

/-- Original target-index transport constructs the corresponding actual stabilization arrow
isomorphism. -/
def stabilizationTargetIso (a : A) {b c : A} (q : b ≅ c)
    (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    stabilizationArrow a c K (D ≫ eHomWhiskerLeft PointedCGWH.{u, v} a q.hom) ≅
      stabilizationArrow a b K D :=
  Arrow.isoMk'
    (CurrentFree.stabilization a c K (D ≫ eHomWhiskerLeft PointedCGWH.{u, v} a q.hom))
    (CurrentFree.stabilization a b K D) (freeIndexIso q K)
    (Iso.refl (Free.object a (𝟙_ PointedCGWH.{u, v}))) (by
    change freeIndexMap q.hom K ≫ CurrentFree.stabilization a b K D =
      CurrentFree.stabilization a c K (D ≫ eHomWhiskerLeft PointedCGWH.{u, v} a q.hom) ≫ 𝟙 _
    rw [Category.comp_id]
    exact stabilization_target_iso a q K D)

end FreeIndex

local notation "SymIndex" => Operad.SmallFinBijGroupoid

/-- The complete original symmetric free stabilization arrow at an arbitrary pair. -/
def symmetricStabilizationArrow (n a : SymIndex) : Arrow Actual.SymmetricCarrier.{u, v} :=
  stabilizationArrow (PointedCGWH.symmetricOperatorObj n)
    (PointedCGWH.symmetricOperatorObj (n ⊗ a))
    (PointedCGWH.sphereSequence.functor.obj a) (Actual.symmetricNu n a)

/-- The complete original orthogonal free stabilization arrow at the corresponding pair. -/
def orthogonalStabilizationArrow (n a : SymIndex) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  Arrow.mk (NativeK.stabilization Actual.orthogonalFamily (n.of.len, a.of.len))

/-- The whole actual prolongation of the original symmetric arrow. -/
def symmetricProlongedStabilizationArrow (n a : SymIndex) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  prolongedStabilizationArrow symmetricOrthogonalOperatorIndexFunctor
    (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj (n ⊗ a))
    (PointedCGWH.sphereSequence.functor.obj a) (Actual.symmetricNu n a)

/-- The original coefficient comparison and full Kan equation give the actual arrow isomorphism. -/
def symmetricOrthogonalStabilizationIso (n a : SymIndex) :
    symmetricProlongedStabilizationArrow.{u, v} n a ≅
      orthogonalStabilizationArrow.{u, v} n a := by
  dsimp only [orthogonalStabilizationArrow, NativeK.stabilization, Actual.orthogonalFamily]
  let j := symmetricOrthogonalOperatorIndexFunctor.{u, v}
  let b := PointedCGWH.symmetricOperatorObj.{u, v} n
  let c := PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ a)
  let K := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let T := PointedCGWH.orthogonalSphere.{u, v} a.of.len
  let e : K ≅ T := originalSymmetricOrthogonalCoefficientIso.{u, v} a
  let D : K ⟶ (b ⟶[PointedCGWH.{u, v}] c) := Actual.symmetricNu.{u, v} n a
  let E : T ⟶ (j.obj b ⟶[PointedCGWH.{u, v}] j.obj c) :=
    OrthogonalOperatorIndex.nu.{u, v} n.of.len a.of.len
  have h : D ≫ j.map b c = e.hom ≫ E := symmetricOrthogonal_inclusion.{u, v} n a
  exact leftKanCoefficientStabilizationIso j b c e D E h

section OriginalInterval

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B)

private theorem leftKan_unit_component_naturality
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (p : X ⟶ Y) (a : A) :
    component p a ≫ leftKanUnitComponent j Y a =
      leftKanUnitComponent j X a ≫ component ((leftKan j).map p) (j.obj a) := by
  have h := congrArg (fun q => component q a) (leftKanUnit_natural j p)
  rw [component_comp, component_comp, leftKanUnit_component,
    leftKanUnit_component, restrictionMap_component] at h
  exact h

/-- The actual Kan tensor comparison keeps the original scalar unit map. -/
theorem leftKan_scalarUnit (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    leftKanTensorHom j (𝟙_ PointedCGWH.{u, v}) X ≫
      (scalarUnitIso ((leftKan j).obj X)).hom =
        (leftKan j).map (scalarUnitIso X).hom := by
  apply (leftKanHomEquiv j (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) X)
    ((leftKan j).obj X)).injective
  apply hom_ext
  intro a
  rw [leftKanHomEquiv_apply, leftKanHomEquiv_apply,
    leftKanHomToRestriction_component, leftKanHomToRestriction_component,
    component_comp, scalarUnitIso_hom_component]
  have ht := leftKan_unit_component_naturality j (scalarUnitIso X).hom a
  rw [scalarUnitIso_hom_component] at ht
  let P := X.toEnrichedFunctor.obj a
  let Q := (leftKanObject j X).toEnrichedFunctor.obj (j.obj a)
  let R := (leftKanObject j (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) X)).toEnrichedFunctor.obj
    (j.obj a)
  let s : (𝟙_ PointedCGWH.{u, v}) ⊗ P ⟶ R :=
    leftKanUnitComponent j (tensorLeftObject (𝟙_ PointedCGWH.{u, v}) X) a
  let t : R ⟶ (𝟙_ PointedCGWH.{u, v}) ⊗ Q :=
    component (leftKanTensorHom j (𝟙_ PointedCGWH.{u, v}) X) (j.obj a)
  let eta : P ⟶ Q := leftKanUnitComponent j X a
  have hs : s ≫ t = (𝟙_ PointedCGWH.{u, v}) ◁ eta :=
    leftKanTensorHom_unit j (𝟙_ PointedCGWH.{u, v}) X a
  have h1 := congrArg (fun f => f ≫ (λ_ Q).hom) hs
  have h2 : ((𝟙_ PointedCGWH.{u, v}) ◁ eta) ≫ (λ_ Q).hom = (λ_ P).hom ≫ eta :=
    leftUnitor_naturality eta
  exact (Category.assoc s t (λ_ Q).hom).symm.trans (h1.trans (h2.trans ht))

/-- The actual Kan comparison also keeps the inverse original scalar unit. -/
theorem leftKan_scalarUnit_inv (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (leftKan j).map (scalarUnitIso X).inv ≫
      leftKanTensorHom j (𝟙_ PointedCGWH.{u, v}) X =
        (scalarUnitIso ((leftKan j).obj X)).inv := by
  apply (cancel_mono (scalarUnitIso ((leftKan j).obj X)).hom).1
  rw [Category.assoc, leftKan_scalarUnit, Iso.inv_hom_id,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Both literal original interval endpoints are transported by the actual Kan comparison. -/
theorem leftKan_interval_inclusion (i : Fin 2)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i X) ≫
      leftKanTensorHom j PointedCGWH.IntervalCoefficient.interval X =
        PointedCGWH.EnrichedIntervalCylinder.inclusion i ((leftKan j).obj X) := by
  rw [PointedCGWH.EnrichedIntervalCylinder.inclusion_eq,
    PointedCGWH.EnrichedIntervalCylinder.inclusion_eq, Functor.map_comp,
    Category.assoc, leftKanTensorHom_scalar_naturality, ← Category.assoc,
    leftKan_scalarUnit_inv]

/-- The literal original interval contraction is transported by the same actual Kan comparison. -/
theorem leftKan_interval_projection (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    leftKanTensorHom j PointedCGWH.IntervalCoefficient.interval X ≫
      PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj X) =
        (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection X) := by
  rw [PointedCGWH.EnrichedIntervalCylinder.projection_eq,
    PointedCGWH.EnrichedIntervalCylinder.projection_eq, Functor.map_comp,
    ← Category.assoc, ← leftKanTensorHom_scalar_naturality,
    Category.assoc, leftKan_scalarUnit]

end OriginalInterval

namespace CylinderTransport

open PointedCGWH.EnrichedIntervalMappingCylinder

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The existing whole mapping-cylinder functor transports every genuine arrow isomorphism. -/
def objectIso {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (e : f ≅ g) :
    object f ≅ object g := functor.mapIso e

/-- The original second-endpoint source factor is transported by the same whole functor. -/
def sourceIso {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (e : f ≅ g) :
    Arrow.mk (source f) ≅ Arrow.mk (source g) :=
  Arrow.isoMk (Arrow.leftFunc.mapIso e) (objectIso e) (source_map e.hom).symm

/-- The original retraction is transported by the same whole functor and target map. -/
def retractionIso {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (e : f ≅ g) :
    Arrow.mk (retraction f) ≅ Arrow.mk (retraction g) :=
  Arrow.isoMk (objectIso e) (Arrow.rightFunc.mapIso e) (map_retraction e.hom)

section LeftKan

variable {B : Type} [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B)

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.Construction.modelCategory

private theorem leftKan_mapped_isPushout
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    IsPushout ((leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left))
      ((leftKan j).map f.hom) ((leftKan j).map (intervalLeg f))
        ((leftKan j).map (targetLeg f)) := by
  let _ : PreservesColimitsOfSize.{0, 0} (leftKan j) :=
    (leftKanRestrictionAdjunction j).leftAdjoint_preservesColimits
  exact (IsPushout.of_hasPushout
    (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left) f.hom).map (leftKan j)

private theorem leftKan_isPushout
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    IsPushout
      (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 ((leftKan j).obj f.left))
      ((leftKan j).map f.hom)
      ((leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).inv ≫
        (leftKan j).map (intervalLeg f)) ((leftKan j).map (targetLeg f)) := by
  let e := leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left
  have hi : (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 f.left) ≫
      e.hom = PointedCGWH.EnrichedIntervalCylinder.inclusion 0 ((leftKan j).obj f.left) := by
    rw [leftKanTensorIso_hom]
    exact leftKan_interval_inclusion j 0 f.left
  refine (leftKan_mapped_isPushout j f).of_iso (Iso.refl _) e
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.id_comp] using hi
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id]
    change (leftKan j).map (intervalLeg f) =
      e.hom ≫ e.inv ≫ (leftKan j).map (intervalLeg f)
    exact (e.hom_inv_id_assoc _).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Actual prolongation preserves the chosen original interval mapping cylinder. -/
def leftKanIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).obj (object f) ≅ object ((leftKan j).mapArrow.obj f) :=
  (leftKan_isPushout j f).isoPushout

/-- The complete original interval leg retains the actual tensor comparison under prolongation. -/
theorem intervalLeg_leftKanIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (intervalLeg f) ≫ (leftKanIso j f).hom =
      (leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).hom ≫
        intervalLeg ((leftKan j).mapArrow.obj f) := by
  let e := leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left
  let t := (leftKan j).map (intervalLeg f) ≫ (leftKanIso j f).hom
  have h : (e.inv ≫ (leftKan j).map (intervalLeg f)) ≫ (leftKanIso j f).hom =
      intervalLeg ((leftKan j).mapArrow.obj f) :=
    (leftKan_isPushout j f).inl_isoPushout_hom
  have ht : e.inv ≫ t = intervalLeg ((leftKan j).mapArrow.obj f) :=
    (Category.assoc _ _ _).symm.trans h
  exact (e.hom_inv_id_assoc t).symm.trans (congrArg (fun q => e.hom ≫ q) ht)

/-- The complete original target leg is retained by the same Kan mapping-cylinder comparison. -/
theorem targetLeg_leftKanIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (targetLeg f) ≫ (leftKanIso j f).hom =
      targetLeg ((leftKan j).mapArrow.obj f) :=
  (leftKan_isPushout j f).inr_isoPushout_hom

/-- The original second endpoint, with its literal index `1`, is retained by prolongation. -/
theorem source_leftKanIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (source f) ≫ (leftKanIso j f).hom =
      source ((leftKan j).mapArrow.obj f) := by
  rw [source, source, CategoryTheory.Functor.map_comp, Category.assoc,
    intervalLeg_leftKanIso, ← Category.assoc, leftKanTensorIso_hom,
    leftKan_interval_inclusion]
  rfl

/-- The same original mapping-cylinder retraction is retained by actual prolongation. -/
theorem leftKanIso_retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKanIso j f).hom ≫ retraction ((leftKan j).mapArrow.obj f) =
      (leftKan j).map (retraction f) := by
  apply (leftKan_mapped_isPushout j f).hom_ext
  · rw [← Category.assoc, intervalLeg_leftKanIso, Category.assoc, intervalLeg_retraction,
      ← Category.assoc, leftKanTensorIso_hom]
    change (leftKanTensorHom j PointedCGWH.IntervalCoefficient.interval f.left ≫
      PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left)) ≫
      (leftKan j).map f.hom =
      (leftKan j).map (intervalLeg f) ≫ (leftKan j).map (retraction f)
    rw [leftKan_interval_projection, ← CategoryTheory.Functor.map_comp, ← intervalLeg_retraction,
      CategoryTheory.Functor.map_comp]
  · rw [← Category.assoc, targetLeg_leftKanIso, targetLeg_retraction,
      ← CategoryTheory.Functor.map_comp, targetLeg_retraction, CategoryTheory.Functor.map_id]
    rfl

/-- The cylinder comparison is natural in every full original arrow morphism. -/
theorem leftKanIso_naturality {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)}
    (h : f ⟶ g) :
    (leftKan j).map (map h) ≫ (leftKanIso j g).hom =
      (leftKanIso j f).hom ≫ map ((leftKan j).mapArrow.map h) := by
  apply (leftKan_mapped_isPushout j f).hom_ext
  · rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, intervalLeg_map,
      CategoryTheory.Functor.map_comp, Category.assoc, intervalLeg_leftKanIso,
      leftKanTensorIso_hom, ← Category.assoc, leftKanTensorHom_naturality,
      Category.assoc, ← leftKanTensorIso_hom]
    rw [← Category.assoc ((leftKan j).map (intervalLeg f)), intervalLeg_leftKanIso,
      Category.assoc, intervalLeg_map]
    rfl
  · rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, targetLeg_map,
      CategoryTheory.Functor.map_comp, Category.assoc, targetLeg_leftKanIso]
    rw [← Category.assoc ((leftKan j).map (targetLeg f)), targetLeg_leftKanIso,
      targetLeg_map]
    rfl

/-- The chosen original mapping-cylinder functors commute with prolongation on whole arrows. -/
def leftKanNatIso : functor (I := A) ⋙ leftKan j ≅
    (leftKan j).mapArrow ⋙ functor (I := B) :=
  NatIso.ofComponents (leftKanIso j) (by
    intro f g h
    exact leftKanIso_naturality j h)

/-- The original second-endpoint source arrow is transported by actual prolongation. -/
def leftKanSourceIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    Arrow.mk ((leftKan j).map (source f)) ≅
      Arrow.mk (source ((leftKan j).mapArrow.obj f)) :=
  Arrow.isoMk (Iso.refl _) (leftKanIso j f) (by
    rw [Iso.refl_hom, Category.id_comp]
    exact (source_leftKanIso j f).symm)

/-- The same original retraction arrow is transported by actual prolongation. -/
def leftKanRetractionIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    Arrow.mk ((leftKan j).map (retraction f)) ≅
      Arrow.mk (retraction ((leftKan j).mapArrow.obj f)) :=
  Arrow.isoMk (leftKanIso j f) (Iso.refl _) (by
    rw [Iso.refl_hom, Category.comp_id]
    exact leftKanIso_retraction j f)

/-- The actual prolongation of an original mapping-cylinder object. -/
abbrev prolongedObject (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    EnrichedFunctorCat PointedCGWH.{u, v} B := (leftKan j).obj (object f)

/-- The actual prolongation of the original second-endpoint source arrow. -/
abbrev prolongedSourceArrow (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
  (leftKan j).mapArrow.obj (Arrow.mk (source f))

/-- The actual prolongation of the same original retraction arrow. -/
abbrev prolongedRetractionArrow (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
  (leftKan j).mapArrow.obj (Arrow.mk (retraction f))

/-- Kan preservation followed by the existing cylinder functor acts on a genuine arrow
isomorphism. -/
def throughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) : prolongedObject j f ≅ object g :=
  leftKanIso j f ≪≫ objectIso e

/-- The same two functorial comparisons preserve the original second-endpoint source arrow. -/
def sourceThroughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    prolongedSourceArrow j f ≅ Arrow.mk (source g) :=
  leftKanSourceIso j f ≪≫ sourceIso e

/-- The same two functorial comparisons preserve the original retraction arrow. -/
def retractionThroughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    prolongedRetractionArrow j f ≅ Arrow.mk (retraction g) :=
  leftKanRetractionIso j f ≪≫ retractionIso e

/-- The original interval leg keeps both the actual Kan tensor map and full left arrow map. -/
theorem intervalLeg_throughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    (leftKan j).map (intervalLeg f) ≫ (throughIso j f e).hom =
      (leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).hom ≫
        tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫ intervalLeg g := by
  rw [throughIso, Iso.trans_hom, ← Category.assoc, intervalLeg_leftKanIso, Category.assoc]
  exact congrArg (fun q =>
    (leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).hom ≫ q)
      (intervalLeg_map e.hom)

/-- The original target leg retains the full right arrow map. -/
theorem targetLeg_throughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    (leftKan j).map (targetLeg f) ≫ (throughIso j f e).hom = e.hom.right ≫ targetLeg g := by
  rw [throughIso, Iso.trans_hom, ← Category.assoc, targetLeg_leftKanIso]
  exact targetLeg_map e.hom

/-- The literal original second endpoint retains the complete left arrow map. -/
theorem source_throughIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    (leftKan j).map (source f) ≫ (throughIso j f e).hom = e.hom.left ≫ source g := by
  rw [throughIso, Iso.trans_hom, ← Category.assoc, source_leftKanIso]
  exact source_map e.hom

/-- The original contraction and retraction retain the complete right arrow map. -/
theorem throughIso_retraction (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) :
    (throughIso j f e).hom ≫ retraction g = (leftKan j).map (retraction f) ≫ e.hom.right := by
  rw [throughIso, Iso.trans_hom, Category.assoc]
  change (leftKanIso j f).hom ≫ (map e.hom ≫ retraction g) = _
  rw [map_retraction, ← Category.assoc, leftKanIso_retraction]

section CylinderEquations

variable (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
  {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
  (e : (leftKan j).mapArrow.obj f ≅ g)

/-- Both original interval endpoints retain the complete forward source map. -/
theorem endpoint_throughIso (i : Fin 2) :
    (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f) ≫
      (CylinderTransport.throughIso j f e).hom =
    e.hom.left ≫ PointedCGWH.EnrichedIntervalCylinder.inclusion i g.left ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g := by
  let t := leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left
  have hi : (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫
      t.hom = PointedCGWH.EnrichedIntervalCylinder.inclusion i ((leftKan j).obj f.left) :=
    (congrArg (fun r => (leftKan j).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫ r)
        (leftKanTensorIso_hom j PointedCGWH.IntervalCoefficient.interval f.left)).trans
          (leftKan_interval_inclusion j i f.left)
  calc
    _ = ((leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫
        (leftKan j).map (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f)) ≫
          (CylinderTransport.throughIso j f e).hom :=
      congrArg (fun r => r ≫ (CylinderTransport.throughIso j f e).hom)
        ((leftKan j).map_comp (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left)
          (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f))
    _ = (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫
        ((leftKan j).map (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f) ≫
          (CylinderTransport.throughIso j f e).hom) := Category.assoc _ _ _
    _ = (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫
        (t.hom ≫ tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫
          PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g) :=
      congrArg (fun r => (leftKan j).map
        (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫ r)
          (CylinderTransport.intervalLeg_throughIso j f e)
    _ = ((leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left) ≫ t.hom) ≫
        tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫
          PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g := (Category.assoc _ _ _).symm
    _ = PointedCGWH.EnrichedIntervalCylinder.inclusion i ((leftKan j).obj f.left) ≫
        tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫
          PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g :=
      congrArg (fun r => r ≫ tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g) hi
    _ = _ := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun r => r ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g)
        (PointedCGWH.EnrichedIntervalCylinder.inclusion_naturality i e.hom.left)).trans
          (Category.assoc _ _ _))

/-- Both original interval endpoints retain the complete inverse source map. -/
theorem endpoint_throughIso_inv (i : Fin 2) :
    (PointedCGWH.EnrichedIntervalCylinder.inclusion i g.left ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g) ≫
      (CylinderTransport.throughIso j f e).inv =
    e.inv.left ≫ (leftKan j).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f) := by
  apply (Iso.comp_inv_eq (CylinderTransport.throughIso j f e)).mpr
  calc
    _ = e.inv.left ≫ (e.hom.left ≫
        (PointedCGWH.EnrichedIntervalCylinder.inclusion i g.left ≫
          PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg g)) :=
      (Arrow.inv_hom_id_left_assoc e _).symm
    _ = e.inv.left ≫ ((leftKan j).map
        (PointedCGWH.EnrichedIntervalCylinder.inclusion i f.left ≫
          PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg f) ≫
            (CylinderTransport.throughIso j f e).hom) :=
      congrArg (fun r => e.inv.left ≫ r) (endpoint_throughIso j f e i).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The inverse cylinder comparison retains the original retraction and inverse target map. -/
theorem throughIso_retraction_inv :
    (CylinderTransport.throughIso j f e).inv ≫
      (leftKan j).map (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f) =
    PointedCGWH.EnrichedIntervalMappingCylinder.retraction g ≫ e.inv.right := by
  let t := CylinderTransport.throughIso j f e
  let r := (leftKan j).map (PointedCGWH.EnrichedIntervalMappingCylinder.retraction f)
  let s := PointedCGWH.EnrichedIntervalMappingCylinder.retraction g
  have h : t.hom ≫ s = r ≫ e.hom.right := CylinderTransport.throughIso_retraction j f e
  calc
    t.inv ≫ r = (t.inv ≫ r) ≫ (e.hom.right ≫ e.inv.right) :=
      (Category.comp_id _).symm.trans
        (congrArg (fun p => (t.inv ≫ r) ≫ p) (Arrow.hom_inv_id_right e).symm)
    _ = t.inv ≫ (r ≫ e.hom.right) ≫ e.inv.right := by simp only [Category.assoc]
    _ = t.inv ≫ (t.hom ≫ s) ≫ e.inv.right :=
      congrArg (fun p => t.inv ≫ p ≫ e.inv.right) h.symm
    _ = s ≫ e.inv.right := by
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun p => p ≫ e.inv.right) (t.inv_hom_id_assoc s)))

/-- The forward tensor and source comparison retains the original interval contraction. -/
theorem projection_throughIso :
    (leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).hom ≫
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.hom.left ≫
      PointedCGWH.EnrichedIntervalCylinder.projection g.left =
    (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection f.left) ≫ e.hom.left := by
  let t := leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left
  have hp : t.hom ≫ PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left) =
      (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection f.left) :=
    (congrArg (fun r => r ≫ PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj
      f.left))
      (leftKanTensorIso_hom j PointedCGWH.IntervalCoefficient.interval f.left)).trans
        (leftKan_interval_projection j f.left)
  calc
    _ = t.hom ≫ (PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left) ≫
        e.hom.left) :=
      congrArg (fun r => t.hom ≫ r) (PointedCGWH.EnrichedIntervalCylinder.projection_naturality
        e.hom.left)
    _ = (t.hom ≫ PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left)) ≫
        e.hom.left := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun r => r ≫ e.hom.left) hp

/-- The inverse tensor and source comparison retains the original interval contraction. -/
theorem projection_throughIso_inv :
    tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.inv.left ≫
      (leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left).inv ≫
      (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection f.left) =
    PointedCGWH.EnrichedIntervalCylinder.projection g.left ≫ e.inv.left := by
  let t := leftKanTensorIso j PointedCGWH.IntervalCoefficient.interval f.left
  have hp : t.hom ≫ PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left) =
      (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection f.left) :=
    (congrArg (fun r => r ≫ PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj
      f.left))
      (leftKanTensorIso_hom j PointedCGWH.IntervalCoefficient.interval f.left)).trans
        (leftKan_interval_projection j f.left)
  have hi : t.inv ≫ (leftKan j).map (PointedCGWH.EnrichedIntervalCylinder.projection f.left) =
      PointedCGWH.EnrichedIntervalCylinder.projection ((leftKan j).obj f.left) :=
    (Iso.inv_comp_eq t).mpr hp.symm
  exact (congrArg (fun r => tensorLeftMap PointedCGWH.IntervalCoefficient.interval e.inv.left ≫ r)
    hi).trans
    (PointedCGWH.EnrichedIntervalCylinder.projection_naturality e.inv.left)

end CylinderEquations

end LeftKan

end CylinderTransport

/-- The whole prolongation of the original symmetric mapping cylinder. -/
def symmetricProlongedCylinder (n a : SymIndex) : Actual.OrthogonalCarrier.{u, v} :=
  CylinderTransport.prolongedObject symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a)

/-- The original orthogonal mapping cylinder at the corresponding complete block label. -/
def orthogonalCylinder (n a : SymIndex) : Actual.OrthogonalCarrier.{u, v} :=
  PointedCGWH.EnrichedIntervalMappingCylinder.object (orthogonalStabilizationArrow n a)

/-- The actual free-arrow comparison constructs the complete original cylinder isomorphism. -/
def symmetricOrthogonalCylinderIso (n a : SymIndex) :
    symmetricProlongedCylinder.{u, v} n a ≅ orthogonalCylinder.{u, v} n a :=
  CylinderTransport.throughIso symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a) (symmetricOrthogonalStabilizationIso n a)

/-- The whole prolongation of the original symmetric second-endpoint source arrow. -/
def symmetricProlongedCylinderSourceArrow (n a : SymIndex) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  CylinderTransport.prolongedSourceArrow symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a)

/-- The original orthogonal source arrow uses the literal same second interval endpoint. -/
def orthogonalCylinderSourceArrow (n a : SymIndex) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.source (orthogonalStabilizationArrow n a))

/-- The actual original stabilization comparison transports the literal second-endpoint arrow. -/
def symmetricOrthogonalCylinderSourceIso (n a : SymIndex) :
    symmetricProlongedCylinderSourceArrow.{u, v} n a ≅
      orthogonalCylinderSourceArrow.{u, v} n a :=
  CylinderTransport.sourceThroughIso symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a) (symmetricOrthogonalStabilizationIso n a)

/-- The whole prolongation of the same original symmetric retraction arrow. -/
def symmetricProlongedCylinderRetractionArrow (n a : SymIndex) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  CylinderTransport.prolongedRetractionArrow symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a)

/-- The original orthogonal retraction retains the same interval augmentation and target
identity. -/
def orthogonalCylinderRetractionArrow (n a : SymIndex) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.retraction
    (orthogonalStabilizationArrow n a))

/-- The actual original stabilization comparison transports the same original retraction arrow. -/
def symmetricOrthogonalCylinderRetractionIso (n a : SymIndex) :
    symmetricProlongedCylinderRetractionArrow.{u, v} n a ≅
      orthogonalCylinderRetractionArrow.{u, v} n a :=
  CylinderTransport.retractionThroughIso symmetricOrthogonalOperatorIndexFunctor
    (symmetricStabilizationArrow n a) (symmetricOrthogonalStabilizationIso n a)

namespace ScalarTransport

private theorem map_leg_naturality {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y P Q : C} {X' Y' P' Q' : D}
    (l : X ⟶ P) (r : Y ⟶ Q) (l' : X' ⟶ P') (r' : Y' ⟶ Q')
    (m : P ⟶ Q) (m' : P' ⟶ Q') (q : X ⟶ Y) (q' : X' ⟶ Y')
    (eP : F.obj P ⟶ P') (eQ : F.obj Q ⟶ Q')
    (tX : F.obj X ⟶ X') (tY : F.obj Y ⟶ Y')
    (hA : l ≫ m = q ≫ r) (hB : l' ≫ m' = q' ≫ r')
    (hX : F.map l ≫ eP = tX ≫ l') (hY : F.map r ≫ eQ = tY ≫ r')
    (hN : F.map q ≫ tY = tX ≫ q') :
    F.map l ≫ (F.map m ≫ eQ) = F.map l ≫ (eP ≫ m') := by
  calc
    _ = F.map (l ≫ m) ≫ eQ := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map (q ≫ r) ≫ eQ := congrArg (fun p => F.map p ≫ eQ) hA
    _ = F.map q ≫ (F.map r ≫ eQ) := by rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map q ≫ (tY ≫ r') := congrArg (fun p => F.map q ≫ p) hY
    _ = (F.map q ≫ tY) ≫ r' := (Category.assoc _ _ _).symm
    _ = (tX ≫ q') ≫ r' := congrArg (fun p => p ≫ r') hN
    _ = tX ≫ (q' ≫ r') := Category.assoc _ _ _
    _ = tX ≫ (l' ≫ m') := congrArg (fun p => tX ≫ p) hB.symm
    _ = (tX ≫ l') ≫ m' := (Category.assoc _ _ _).symm
    _ = (F.map l ≫ eP) ≫ m' := congrArg (fun p => p ≫ m') hX.symm
    _ = _ := Category.assoc _ _ _

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.Construction.modelCategory

/-- The actual chosen scalar Leibniz pushout retains both original caller arrows. -/
def square {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := C)).PushoutObjObj
      i.hom f.hom :=
  Functor.PushoutObjObj.ofHasPushout WeightedEndVariance.tensorBifunctor i.hom f.hom

/-- The actual scalar Leibniz inclusion is bundled as its whole original arrow. -/
def arrow {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C) := Arrow.mk (square i f).ι

/-- The existing scalar Leibniz functor acts on whole diagram arrows. -/
def diagramFunctor {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C) ⥤
      Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C) :=
  (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := C)).leibnizPushout.obj i

/-- Every whole original diagram-arrow map induces its actual scalar Leibniz map. -/
def diagramMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)}
    (h : f ⟶ g) : arrow i f ⟶ arrow i g := (diagramFunctor i).map h

/-- The first original pushout leg retains the full source arrow map. -/
@[reassoc]
theorem inl_diagramMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)}
    (h : f ⟶ g) :
    (square i f).inl ≫ (diagramMap i h).left = tensorLeftMap i.right h.left ≫ (square i g).inl :=
  (square i f).isPushout.inl_desc _ _ _

/-- The second original pushout leg retains the full target arrow map. -/
@[reassoc]
theorem inr_diagramMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)}
    (h : f ⟶ g) :
    (square i f).inr ≫ (diagramMap i h).left = tensorLeftMap i.left h.right ≫ (square i g).inr :=
  (square i f).isPushout.inr_desc _ _ _

/-- The target of a diagram-arrow map is its original full scalar tensor map. -/
theorem diagramMap_right {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (i : Arrow PointedCGWH.{u, v}) {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)}
    (h : f ⟶ g) : (diagramMap i h).right = tensorLeftMap i.right h.right := rfl

/-- The same original Leibniz construction is functorial in whole scalar arrows. -/
def scalarFunctor {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    Arrow PointedCGWH.{u, v} ⥤ Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C) :=
  (WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v}) (I := C)).leibnizPushout.flip.obj f

/-- Every whole original scalar-arrow map induces its actual scalar Leibniz map. -/
def scalarMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k)
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) : arrow i f ⟶ arrow k f :=
  (scalarFunctor f).map h

/-- The first original pushout leg retains the full scalar target map. -/
@[reassoc]
theorem inl_scalarMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k)
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    (square i f).inl ≫ (scalarMap h f).left = scalarTensorMap h.right f.left ≫ (square k f).inl :=
  (square i f).isPushout.inl_desc _ _ _

/-- The second original pushout leg retains the full scalar source map. -/
@[reassoc]
theorem inr_scalarMap {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k)
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    (square i f).inr ≫ (scalarMap h f).left = scalarTensorMap h.left f.right ≫ (square k f).inr :=
  (square i f).isPushout.inr_desc _ _ _

/-- The target of a scalar-arrow map retains its original full coefficient map. -/
theorem scalarMap_right {C : Type} [EnrichedCategory PointedCGWH.{u, v} C]
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k)
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} C)) :
    (scalarMap h f).right = scalarTensorMap h.right f.right := rfl

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B)

/-- The entire actual Kan functor prolongs the chosen original Leibniz arrow. -/
def prolongedArrow (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
  (leftKan j).mapArrow.obj (arrow i f)

private theorem leftKan_mapped_isPushout (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    IsPushout ((leftKan j).map (scalarTensorMap i.hom f.left))
      ((leftKan j).map (tensorLeftMap i.left f.hom))
      ((leftKan j).map (square i f).inl) ((leftKan j).map (square i f).inr) := by
  let _ : PreservesColimitsOfSize.{0, 0} (leftKan j) :=
    (leftKanRestrictionAdjunction j).leftAdjoint_preservesColimits
  exact (square i f).isPushout.map (leftKan j)

private theorem leftKan_isPushout (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    IsPushout (scalarTensorMap i.hom ((leftKan j).obj f.left))
      (tensorLeftMap i.left ((leftKan j).map f.hom))
      ((leftKanTensorIso j i.right f.left).inv ≫ (leftKan j).map (square i f).inl)
      ((leftKanTensorIso j i.left f.right).inv ≫ (leftKan j).map (square i f).inr) := by
  let e₀ := leftKanTensorIso j i.left f.left
  let e₁ := leftKanTensorIso j i.right f.left
  let e₂ := leftKanTensorIso j i.left f.right
  refine (leftKan_mapped_isPushout j i f).of_iso e₀ e₁ e₂ (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [e₀, e₁, leftKanTensorIso_hom] using
      leftKanTensorHom_scalar_naturality j i.hom f.left
  · simpa only [e₀, e₂, leftKanTensorIso_hom] using
      leftKanTensorHom_naturality j i.left f.hom
  · simp only [Iso.refl_hom, Category.comp_id]
    change (leftKan j).map (square i f).inl = e₁.hom ≫ e₁.inv ≫ (leftKan j).map (square i f).inl
    exact (e₁.hom_inv_id_assoc _).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change (leftKan j).map (square i f).inr = e₂.hom ≫ e₂.inv ≫ (leftKan j).map (square i f).inr
    exact (e₂.hom_inv_id_assoc _).symm

/-- Actual Kan preservation and both tensor comparisons identify the full chosen pushout source. -/
def leftKanSourceIso (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).obj (square i f).pt ≅ (square i ((leftKan j).mapArrow.obj f)).pt :=
  (leftKan_isPushout j i f).isoPushout

/-- The first original scalar pushout leg retains its actual Kan tensor comparison. -/
theorem inl_leftKanSourceIso (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (square i f).inl ≫ (leftKanSourceIso j i f).hom =
      (leftKanTensorIso j i.right f.left).hom ≫ (square i ((leftKan j).mapArrow.obj f)).inl := by
  let e := leftKanTensorIso j i.right f.left
  let t := (leftKan j).map (square i f).inl ≫ (leftKanSourceIso j i f).hom
  have h : (e.inv ≫ (leftKan j).map (square i f).inl) ≫ (leftKanSourceIso j i f).hom =
      (square i ((leftKan j).mapArrow.obj f)).inl :=
    (leftKan_isPushout j i f).inl_isoPushout_hom
  have ht : e.inv ≫ t = (square i ((leftKan j).mapArrow.obj f)).inl :=
    (Category.assoc _ _ _).symm.trans h
  exact (e.hom_inv_id_assoc t).symm.trans (congrArg (fun q => e.hom ≫ q) ht)

/-- The second original scalar pushout leg retains its actual Kan tensor comparison. -/
theorem inr_leftKanSourceIso (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (square i f).inr ≫ (leftKanSourceIso j i f).hom =
      (leftKanTensorIso j i.left f.right).hom ≫ (square i ((leftKan j).mapArrow.obj f)).inr := by
  let e := leftKanTensorIso j i.left f.right
  let t := (leftKan j).map (square i f).inr ≫ (leftKanSourceIso j i f).hom
  have h : (e.inv ≫ (leftKan j).map (square i f).inr) ≫ (leftKanSourceIso j i f).hom =
      (square i ((leftKan j).mapArrow.obj f)).inr :=
    (leftKan_isPushout j i f).inr_isoPushout_hom
  have ht : e.inv ≫ t = (square i ((leftKan j).mapArrow.obj f)).inr :=
    (Category.assoc _ _ _).symm.trans h
  exact (e.hom_inv_id_assoc t).symm.trans (congrArg (fun q => e.hom ≫ q) ht)

/-- The full actual Leibniz inclusion commutes with the original Kan tensor comparison. -/
theorem leftKan_arrow_comm (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKanSourceIso j i f).hom ≫ (square i ((leftKan j).mapArrow.obj f)).ι =
      (leftKan j).map (square i f).ι ≫ (leftKanTensorIso j i.right f.right).hom := by
  let P := (square i f).pt
  let Q := (square i ((leftKan j).mapArrow.obj f)).pt
  let a : P ⟶ tensorLeftObject i.right f.right := (square i f).ι
  let b : Q ⟶ tensorLeftObject i.right ((leftKan j).obj f.right) :=
    (square i ((leftKan j).mapArrow.obj f)).ι
  let d : (leftKan j).obj P ⟶ Q := (leftKanSourceIso j i f).hom
  let t : (leftKan j).obj (tensorLeftObject i.right f.right) ⟶
      tensorLeftObject i.right ((leftKan j).obj f.right) :=
    (leftKanTensorIso j i.right f.right).hom
  apply (leftKan_mapped_isPushout j i f).hom_ext
  · let al : tensorLeftObject i.right f.left ⟶ P := (square i f).inl
    let bl : tensorLeftObject i.right ((leftKan j).obj f.left) ⟶ Q :=
      (square i ((leftKan j).mapArrow.obj f)).inl
    let tx : (leftKan j).obj (tensorLeftObject i.right f.left) ⟶
        tensorLeftObject i.right ((leftKan j).obj f.left) :=
      (leftKanTensorIso j i.right f.left).hom
    have hl : (leftKan j).map al ≫ d = tx ≫ bl := inl_leftKanSourceIso j i f
    have ha : al ≫ a = tensorLeftMap i.right f.hom := (square i f).inl_ι
    have hb : bl ≫ b = tensorLeftMap i.right ((leftKan j).map f.hom) :=
      (square i ((leftKan j).mapArrow.obj f)).inl_ι
    have hn : (leftKan j).map (tensorLeftMap i.right f.hom) ≫ t =
        tx ≫ tensorLeftMap i.right ((leftKan j).map f.hom) := by
      dsimp only [tx, t]
      rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
      exact leftKanTensorHom_naturality j i.right f.hom
    change (leftKan j).map al ≫ (d ≫ b) = (leftKan j).map al ≫ ((leftKan j).map a ≫ t)
    have h₁ := congrArg (fun p => p ≫ b) hl
    have h₂ := congrArg (fun p => tx ≫ p) hb
    have h₃ := congrArg (fun p => (leftKan j).map p ≫ t) ha.symm
    have h₄ := congrArg (fun p => p ≫ t) ((leftKan j).map_comp al a)
    exact (Category.assoc _ _ _).symm.trans
      (h₁.trans ((Category.assoc _ _ _).trans
        (h₂.trans (hn.symm.trans (h₃.trans (h₄.trans (Category.assoc _ _ _)))))))
  · let ar : tensorLeftObject i.left f.right ⟶ P := (square i f).inr
    let br : tensorLeftObject i.left ((leftKan j).obj f.right) ⟶ Q :=
      (square i ((leftKan j).mapArrow.obj f)).inr
    let tx : (leftKan j).obj (tensorLeftObject i.left f.right) ⟶
        tensorLeftObject i.left ((leftKan j).obj f.right) :=
      (leftKanTensorIso j i.left f.right).hom
    have hl : (leftKan j).map ar ≫ d = tx ≫ br := inr_leftKanSourceIso j i f
    have ha : ar ≫ a = scalarTensorMap i.hom f.right := (square i f).inr_ι
    have hb : br ≫ b = scalarTensorMap i.hom ((leftKan j).obj f.right) :=
      (square i ((leftKan j).mapArrow.obj f)).inr_ι
    have hn : (leftKan j).map (scalarTensorMap i.hom f.right) ≫ t =
        tx ≫ scalarTensorMap i.hom ((leftKan j).obj f.right) := by
      dsimp only [tx, t]
      rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
      exact leftKanTensorHom_scalar_naturality j i.hom f.right
    change (leftKan j).map ar ≫ (d ≫ b) = (leftKan j).map ar ≫ ((leftKan j).map a ≫ t)
    have h₁ := congrArg (fun p => p ≫ b) hl
    have h₂ := congrArg (fun p => tx ≫ p) hb
    have h₃ := congrArg (fun p => (leftKan j).map p ≫ t) ha.symm
    have h₄ := congrArg (fun p => p ≫ t) ((leftKan j).map_comp ar a)
    exact (Category.assoc _ _ _).symm.trans
      (h₁.trans ((Category.assoc _ _ _).trans
        (h₂.trans (hn.symm.trans (h₃.trans (h₄.trans (Category.assoc _ _ _)))))))

/-- Actual Kan preservation constructs the entire original scalar Leibniz arrow isomorphism. -/
def leftKanIso (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    prolongedArrow j i f ≅ arrow i ((leftKan j).mapArrow.obj f) :=
  Arrow.isoMk' ((leftKan j).map (square i f).ι) (square i ((leftKan j).mapArrow.obj f)).ι
    (leftKanSourceIso j i f) (leftKanTensorIso j i.right f.right) (leftKan_arrow_comm j i f)

/-- The full pushout source comparison is natural in every original diagram-arrow map. -/
theorem leftKanSourceIso_diagram_naturality (i : Arrow PointedCGWH.{u, v})
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (h : f ⟶ g) :
    (leftKan j).map (diagramMap i h).left ≫ (leftKanSourceIso j i g).hom =
      (leftKanSourceIso j i f).hom ≫ (diagramMap i ((leftKan j).mapArrow.map h)).left := by
  apply (leftKan_mapped_isPushout j i f).hom_ext
  · exact map_leg_naturality (leftKan j) (square i f).inl (square i g).inl
      (square i ((leftKan j).mapArrow.obj f)).inl (square i ((leftKan j).mapArrow.obj g)).inl
      (diagramMap i h).left (diagramMap i ((leftKan j).mapArrow.map h)).left
      (tensorLeftMap i.right h.left) (tensorLeftMap i.right ((leftKan j).map h.left))
      (leftKanSourceIso j i f).hom (leftKanSourceIso j i g).hom
      (leftKanTensorIso j i.right f.left).hom (leftKanTensorIso j i.right g.left).hom
      (inl_diagramMap i h) (inl_diagramMap i ((leftKan j).mapArrow.map h))
      (inl_leftKanSourceIso j i f) (inl_leftKanSourceIso j i g) (by
        change (leftKan j).map (tensorLeftMap i.right h.left) ≫
            (leftKanTensorIso j i.right g.left).hom =
          (leftKanTensorIso j i.right f.left).hom ≫
            tensorLeftMap i.right ((leftKan j).map h.left)
        rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
        exact leftKanTensorHom_naturality j i.right h.left)
  · exact map_leg_naturality (leftKan j) (square i f).inr (square i g).inr
      (square i ((leftKan j).mapArrow.obj f)).inr (square i ((leftKan j).mapArrow.obj g)).inr
      (diagramMap i h).left (diagramMap i ((leftKan j).mapArrow.map h)).left
      (tensorLeftMap i.left h.right) (tensorLeftMap i.left ((leftKan j).map h.right))
      (leftKanSourceIso j i f).hom (leftKanSourceIso j i g).hom
      (leftKanTensorIso j i.left f.right).hom (leftKanTensorIso j i.left g.right).hom
      (inr_diagramMap i h) (inr_diagramMap i ((leftKan j).mapArrow.map h))
      (inr_leftKanSourceIso j i f) (inr_leftKanSourceIso j i g) (by
        change (leftKan j).map (tensorLeftMap i.left h.right) ≫
            (leftKanTensorIso j i.left g.right).hom =
          (leftKanTensorIso j i.left f.right).hom ≫
            tensorLeftMap i.left ((leftKan j).map h.right)
        rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
        exact leftKanTensorHom_naturality j i.left h.right)

/-- The complete Leibniz arrow comparison is natural in every original diagram-arrow map. -/
theorem leftKanIso_diagram_naturality (i : Arrow PointedCGWH.{u, v})
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (h : f ⟶ g) :
    (leftKan j).mapArrow.map (diagramMap i h) ≫ (leftKanIso j i g).hom =
      (leftKanIso j i f).hom ≫ diagramMap i ((leftKan j).mapArrow.map h) := by
  apply Arrow.hom_ext
  · change (leftKan j).map (diagramMap i h).left ≫ (leftKanSourceIso j i g).hom =
      (leftKanSourceIso j i f).hom ≫ (diagramMap i ((leftKan j).mapArrow.map h)).left
    exact leftKanSourceIso_diagram_naturality j i h
  · change (leftKan j).map (diagramMap i h).right ≫ (leftKanTensorIso j i.right g.right).hom =
      (leftKanTensorIso j i.right f.right).hom ≫ (diagramMap i ((leftKan j).mapArrow.map h)).right
    simp only [diagramMap_right, leftKanTensorIso_hom]
    exact leftKanTensorHom_naturality j i.right h.right

/-- The original scalar Leibniz functors commute with Kan on all whole diagram arrows. -/
def leftKanNatIso (i : Arrow PointedCGWH.{u, v}) :
    diagramFunctor i ⋙ (leftKan j).mapArrow ≅ (leftKan j).mapArrow ⋙ diagramFunctor i :=
  NatIso.ofComponents (leftKanIso j i) (by
    intro f g h
    exact leftKanIso_diagram_naturality j i h)

/-- The full pushout source comparison is natural in every original scalar-arrow map. -/
theorem leftKanSourceIso_scalar_naturality {i k : Arrow PointedCGWH.{u, v}}
    (h : i ⟶ k) (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).map (scalarMap h f).left ≫ (leftKanSourceIso j k f).hom =
      (leftKanSourceIso j i f).hom ≫ (scalarMap h ((leftKan j).mapArrow.obj f)).left := by
  apply (leftKan_mapped_isPushout j i f).hom_ext
  · exact map_leg_naturality (leftKan j) (square i f).inl (square k f).inl
      (square i ((leftKan j).mapArrow.obj f)).inl (square k ((leftKan j).mapArrow.obj f)).inl
      (scalarMap h f).left (scalarMap h ((leftKan j).mapArrow.obj f)).left
      (scalarTensorMap h.right f.left) (scalarTensorMap h.right ((leftKan j).obj f.left))
      (leftKanSourceIso j i f).hom (leftKanSourceIso j k f).hom
      (leftKanTensorIso j i.right f.left).hom (leftKanTensorIso j k.right f.left).hom
      (inl_scalarMap h f) (inl_scalarMap h ((leftKan j).mapArrow.obj f))
      (inl_leftKanSourceIso j i f) (inl_leftKanSourceIso j k f) (by
        change (leftKan j).map (scalarTensorMap h.right f.left) ≫
            (leftKanTensorIso j k.right f.left).hom =
          (leftKanTensorIso j i.right f.left).hom ≫
            scalarTensorMap h.right ((leftKan j).obj f.left)
        rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
        exact leftKanTensorHom_scalar_naturality j h.right f.left)
  · exact map_leg_naturality (leftKan j) (square i f).inr (square k f).inr
      (square i ((leftKan j).mapArrow.obj f)).inr (square k ((leftKan j).mapArrow.obj f)).inr
      (scalarMap h f).left (scalarMap h ((leftKan j).mapArrow.obj f)).left
      (scalarTensorMap h.left f.right) (scalarTensorMap h.left ((leftKan j).obj f.right))
      (leftKanSourceIso j i f).hom (leftKanSourceIso j k f).hom
      (leftKanTensorIso j i.left f.right).hom (leftKanTensorIso j k.left f.right).hom
      (inr_scalarMap h f) (inr_scalarMap h ((leftKan j).mapArrow.obj f))
      (inr_leftKanSourceIso j i f) (inr_leftKanSourceIso j k f) (by
        change (leftKan j).map (scalarTensorMap h.left f.right) ≫
            (leftKanTensorIso j k.left f.right).hom =
          (leftKanTensorIso j i.left f.right).hom ≫
            scalarTensorMap h.left ((leftKan j).obj f.right)
        rw [leftKanTensorIso_hom, leftKanTensorIso_hom]
        exact leftKanTensorHom_scalar_naturality j h.left f.right)

/-- The complete Leibniz arrow comparison is natural in every original scalar-arrow map. -/
theorem leftKanIso_scalar_naturality {i k : Arrow PointedCGWH.{u, v}}
    (h : i ⟶ k) (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    (leftKan j).mapArrow.map (scalarMap h f) ≫ (leftKanIso j k f).hom =
      (leftKanIso j i f).hom ≫ scalarMap h ((leftKan j).mapArrow.obj f) := by
  apply Arrow.hom_ext
  · change (leftKan j).map (scalarMap h f).left ≫ (leftKanSourceIso j k f).hom =
      (leftKanSourceIso j i f).hom ≫ (scalarMap h ((leftKan j).mapArrow.obj f)).left
    exact leftKanSourceIso_scalar_naturality j h f
  · change (leftKan j).map (scalarMap h f).right ≫ (leftKanTensorIso j k.right f.right).hom =
      (leftKanTensorIso j i.right f.right).hom ≫ (scalarMap h ((leftKan j).mapArrow.obj f)).right
    simp only [scalarMap_right, leftKanTensorIso_hom]
    exact leftKanTensorHom_scalar_naturality j h.right f.right

/-- The original scalar Leibniz functors commute with Kan on all whole scalar arrows. -/
def leftKanScalarNatIso (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    scalarFunctor f ⋙ (leftKan j).mapArrow ≅ scalarFunctor ((leftKan j).mapArrow.obj f) :=
  NatIso.ofComponents (fun i => leftKanIso j i f) (by
    intro i k h
    exact leftKanIso_scalar_naturality j h f)

/-- Kan preservation and the original Leibniz functor transport a genuine diagram-arrow
isomorphism. -/
def throughIso (i : Arrow PointedCGWH.{u, v})
    (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A))
    {g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B)}
    (e : (leftKan j).mapArrow.obj f ≅ g) : prolongedArrow j i f ≅ arrow i g :=
  leftKanIso j i f ≪≫
    ((WeightedEndVariance.tensorBifunctor (V := PointedCGWH.{u, v})
      (I := B)).leibnizPushout.obj i).mapIso e

end ScalarTransport

section FreeArrowTransport

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

/-- The original free functor acts on the entire caller coefficient arrow. -/
def freeArrow {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (a : A) (i : Arrow PointedCGWH.{u, v}) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A) := (Free.functor a).mapArrow.obj i

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B)

/-- The actual Kan functor prolongs the whole original free arrow. -/
def prolongedFreeArrow (a : A) (i : Arrow PointedCGWH.{u, v}) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} B) :=
  (leftKan j).mapArrow.obj (freeArrow a i)

/-- The genuine free Kan natural isomorphism transports every entire original coefficient arrow. -/
def leftKanFreeArrowIso (a : A) (i : Arrow PointedCGWH.{u, v}) :
    prolongedFreeArrow j a i ≅ freeArrow (j.obj a) i :=
  Arrow.isoMk' ((leftKan j).map ((Free.functor a).map i.hom))
    ((Free.functor (j.obj a)).map i.hom) ((Kan.leftKanFreeIso j a).app i.left)
    ((Kan.leftKanFreeIso j a).app i.right) ((Kan.leftKanFreeIso j a).hom.naturality i.hom).symm

section FreeArrowComponents

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a : A) (i : Arrow PointedCGWH.{u, v})

/-- The forward source map is the original free Kan comparison on the left coefficient. -/
theorem leftKanFreeArrowIso_hom_left :
    (leftKanFreeArrowIso j a i).hom.left =
      (Kan.leftKanFreeIso j a).hom.app i.left := by
  unfold leftKanFreeArrowIso
  exact (Arrow.isoMk_hom_left _ _ _).trans
    (Iso.app_hom (Kan.leftKanFreeIso j a) i.left)

/-- The forward target map is the original free Kan comparison on the right coefficient. -/
theorem leftKanFreeArrowIso_hom_right :
    (leftKanFreeArrowIso j a i).hom.right =
      (Kan.leftKanFreeIso j a).hom.app i.right := by
  unfold leftKanFreeArrowIso
  exact (Arrow.isoMk_hom_right _ _ _).trans
    (Iso.app_hom (Kan.leftKanFreeIso j a) i.right)

/-- The inverse source map is the original free Kan inverse on the left coefficient. -/
theorem leftKanFreeArrowIso_inv_left :
    (leftKanFreeArrowIso j a i).inv.left =
      (Kan.leftKanFreeIso j a).inv.app i.left := by
  unfold leftKanFreeArrowIso
  exact (Arrow.isoMk_inv_left _ _ _).trans
    (Iso.app_inv (Kan.leftKanFreeIso j a) i.left)

/-- The inverse target map is the original free Kan inverse on the right coefficient. -/
theorem leftKanFreeArrowIso_inv_right :
    (leftKanFreeArrowIso j a i).inv.right =
      (Kan.leftKanFreeIso j a).inv.app i.right := by
  unfold leftKanFreeArrowIso
  exact (Arrow.isoMk_inv_right _ _ _).trans
    (Iso.app_inv (Kan.leftKanFreeIso j a) i.right)

/-- The whole free-arrow comparison is natural in every coefficient-arrow morphism. -/
theorem leftKanFreeArrowIso_naturality (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a : A) {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (leftKan j).mapArrow.map ((Free.functor (V := PointedCGWH.{u, v}) a).mapArrow.map h) ≫
      (leftKanFreeArrowIso j a k).hom =
    (leftKanFreeArrowIso j a i).hom ≫
      (Free.functor (V := PointedCGWH.{u, v}) (j.obj a)).mapArrow.map h := by
  apply Arrow.hom_ext
  · change (leftKan j).map ((Free.functor a).map h.left) ≫
        (leftKanFreeArrowIso j a k).hom.left =
      (leftKanFreeArrowIso j a i).hom.left ≫ (Free.functor (j.obj a)).map h.left
    rw [leftKanFreeArrowIso_hom_left, leftKanFreeArrowIso_hom_left]
    exact (Kan.leftKanFreeIso j a).hom.naturality h.left
  · change (leftKan j).map ((Free.functor a).map h.right) ≫
        (leftKanFreeArrowIso j a k).hom.right =
      (leftKanFreeArrowIso j a i).hom.right ≫ (Free.functor (j.obj a)).map h.right
    rw [leftKanFreeArrowIso_hom_right, leftKanFreeArrowIso_hom_right]
    exact (Kan.leftKanFreeIso j a).hom.naturality h.right

/-- The whole inverse free-arrow comparison is natural in every coefficient-arrow morphism. -/
theorem leftKanFreeArrowIso_inv_naturality (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a : A) {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (Free.functor (V := PointedCGWH.{u, v}) (j.obj a)).mapArrow.map h ≫
      (leftKanFreeArrowIso j a k).inv =
    (leftKanFreeArrowIso j a i).inv ≫
      (leftKan j).mapArrow.map ((Free.functor (V := PointedCGWH.{u, v}) a).mapArrow.map h) := by
  apply Arrow.hom_ext
  · change (Free.functor (j.obj a)).map h.left ≫ (leftKanFreeArrowIso j a k).inv.left =
      (leftKanFreeArrowIso j a i).inv.left ≫ (leftKan j).map ((Free.functor a).map h.left)
    rw [leftKanFreeArrowIso_inv_left, leftKanFreeArrowIso_inv_left]
    exact (Kan.leftKanFreeIso j a).inv.naturality h.left
  · change (Free.functor (j.obj a)).map h.right ≫ (leftKanFreeArrowIso j a k).inv.right =
      (leftKanFreeArrowIso j a i).inv.right ≫ (leftKan j).map ((Free.functor a).map h.right)
    rw [leftKanFreeArrowIso_inv_right, leftKanFreeArrowIso_inv_right]
    exact (Kan.leftKanFreeIso j a).inv.naturality h.right

/-- The original Kan unit retains every full Hom map at the left coefficient. -/
theorem leftKanFreeArrowIso_left_full_component (b : A) :
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object a i.left)) b ≫
      component (leftKanFreeArrowIso j a i).hom.left (j.obj b) = i.left ◁ j.map a b :=
  (congrArg (fun r : (leftKan j).obj (Free.object a i.left) ⟶
      Free.object (j.obj a) i.left =>
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object a i.left)) b ≫
      component r (j.obj b)) (leftKanFreeArrowIso_hom_left j a i)).trans
        (leftKanFreeIso_full_component j a b i.left)

/-- The original Kan unit retains every full Hom map at the right coefficient. -/
theorem leftKanFreeArrowIso_right_full_component (b : A) :
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object a i.right)) b ≫
      component (leftKanFreeArrowIso j a i).hom.right (j.obj b) = i.right ◁ j.map a b :=
  (congrArg (fun r : (leftKan j).obj (Free.object a i.right) ⟶
      Free.object (j.obj a) i.right =>
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object a i.right)) b ≫
      component r (j.obj b)) (leftKanFreeArrowIso_hom_right j a i)).trans
        (leftKanFreeIso_full_component j a b i.right)

end FreeArrowComponents

/-- The original free-arrow functors commute with prolongation naturally in every arrow. -/
def leftKanFreeArrowNatIso (a : A) :
    (Free.functor (V := PointedCGWH.{u, v}) a).mapArrow ⋙ (leftKan j).mapArrow ≅
      (Free.functor (V := PointedCGWH.{u, v}) (j.obj a)).mapArrow :=
  NatIso.ofComponents (leftKanFreeArrowIso j a) (by
    intro i k h
    exact leftKanFreeArrowIso_naturality j a h)

/-- The original morphism-property image under the actual Kan functor, including arrow
isomorphisms. -/
abbrev leftKanImage (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} B) := P.map (leftKan j)

/-- All original free-generator arrows map into the target free family after closure by actual
isomorphisms. -/
theorem leftKan_generators_le (P : MorphismProperty PointedCGWH.{u, v}) :
    leftKanImage j (HomotopicalAlgebra.EnrichedProjective.generators (A := A) P) ≤
      (HomotopicalAlgebra.EnrichedProjective.generators (A := B) P).isoClosure := by
  apply (MorphismProperty.map_le_iff
    (HomotopicalAlgebra.EnrichedProjective.generators (A := A) P)
    (HomotopicalAlgebra.EnrichedProjective.generators (A := B) P).isoClosure).mpr
  intro X Y f hf
  let U : A → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} A :=
    fun a => Free.functor a
  let V : B → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} B :=
    fun b => Free.functor b
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff U P f).mp hf
  let g := (Free.functor (j.obj q.1)).map q.2.1.hom
  have hg : HomotopicalAlgebra.EnrichedProjective.generators (A := B) P g :=
    MorphismProperty.map_mem_adjointFamilyGenerators V P (j.obj q.1) q.2.1.hom q.2.2
  have hm : (HomotopicalAlgebra.EnrichedProjective.generators (A := B) P).isoClosure
      ((leftKan j).map ((Free.functor q.1).map q.2.1.hom)) :=
    ⟨_, _, g, hg, ⟨(leftKanFreeArrowIso j q.1 q.2.1).symm⟩⟩
  have hL := congrArg (fun a => (leftKan j).mapArrow.obj a) hq
  exact ((HomotopicalAlgebra.EnrichedProjective.generators (A := B) P).isoClosure.arrow_mk_iso_iff
    (eqToIso hL)).mpr hm

/-- Surjectivity on index objects identifies the entire original free families up to actual
arrow isomorphisms. -/
theorem leftKan_generators_eq_isoClosure (hobj : Function.Surjective j.obj)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    leftKanImage j (HomotopicalAlgebra.EnrichedProjective.generators (A := A) P) =
      (HomotopicalAlgebra.EnrichedProjective.generators (A := B) P).isoClosure := by
  apply le_antisymm (leftKan_generators_le j P)
  apply (MorphismProperty.isoClosure_le_iff
    (HomotopicalAlgebra.EnrichedProjective.generators (A := B) P)
    (leftKanImage j (HomotopicalAlgebra.EnrichedProjective.generators (A := A) P))).mpr
  intro X Y f hf
  let U : A → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} A :=
    fun a => Free.functor a
  let V : B → PointedCGWH.{u, v} ⥤ EnrichedFunctorCat PointedCGWH.{u, v} B :=
    fun b => Free.functor b
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff V P f).mp hf
  obtain ⟨a, ha⟩ := hobj q.1
  let g := (Free.functor a).map q.2.1.hom
  have hg : HomotopicalAlgebra.EnrichedProjective.generators (A := A) P g :=
    MorphismProperty.map_mem_adjointFamilyGenerators U P a q.2.1.hom q.2.2
  let ei : freeArrow (j.obj a) q.2.1 ≅ freeArrow q.1 q.2.1 :=
    eqToIso (congrArg (fun b => freeArrow b q.2.1) ha)
  let et : freeArrow q.1 q.2.1 ≅ Arrow.mk f := eqToIso hq.symm
  let e : Arrow.mk ((leftKan j).map g) ≅ Arrow.mk f :=
    leftKanFreeArrowIso j a q.2.1 ≪≫ ei ≪≫ et
  exact ⟨_, _, g, hg, ⟨e⟩⟩

/-- Every original symmetric free arrow retains its actual index and coefficient arrow. -/
def symmetricFreeArrow (n : SymIndex) (i : Arrow PointedCGWH.{u, v}) :
    Arrow Actual.SymmetricCarrier.{u, v} := freeArrow (PointedCGWH.symmetricOperatorObj n) i

/-- Every original orthogonal free arrow retains its actual dimension and coefficient arrow. -/
def orthogonalFreeArrow (n : SymIndex) (i : Arrow PointedCGWH.{u, v}) :
    Arrow Actual.OrthogonalCarrier.{u, v} := freeArrow (OrthogonalOperatorIndex.ofIndex n.of.len) i

/-- The whole actual prolongation of the original symmetric free arrow. -/
def symmetricProlongedFreeArrow (n : SymIndex) (i : Arrow PointedCGWH.{u, v}) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  prolongedFreeArrow symmetricOrthogonalOperatorIndexFunctor (PointedCGWH.symmetricOperatorObj n) i

/-- The actual original free Kan comparison transports every symmetric coefficient arrow to its
orthogonal arrow. -/
def symmetricOrthogonalFreeArrowIso (n : SymIndex) (i : Arrow PointedCGWH.{u, v}) :
    symmetricProlongedFreeArrow.{u, v} n i ≅ orthogonalFreeArrow.{u, v} n i :=
  leftKanFreeArrowIso symmetricOrthogonalOperatorIndexFunctor (PointedCGWH.symmetricOperatorObj n) i

/-- Every original freely pointed realized boundary is transported as its full free arrow. -/
def symmetricOrthogonalFreeBoundaryIso (n : SymIndex) (m : ℕ) :
    symmetricProlongedFreeArrow.{u, v} n (Arrow.mk (NativeK.boundaryMap.{u, v} m)) ≅
      orthogonalFreeArrow.{u, v} n (Arrow.mk (NativeK.boundaryMap.{u, v} m)) :=
  symmetricOrthogonalFreeArrowIso n (Arrow.mk (NativeK.boundaryMap m))

/-- The literal original freely pointed realized horn, with every positive dimension and horn
label. -/
def originalHornArrow (m : ℕ) (i : Fin (m + 2)) : Arrow PointedCGWH.{u, v} :=
  Arrow.mk ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} m i))

/-- Every original horn and original symmetric free index has the actual full orthogonal arrow
comparison. -/
def symmetricOrthogonalFreeHornIso (n : SymIndex) (m : ℕ) (i : Fin (m + 2)) :
    symmetricProlongedFreeArrow.{u, v} n (originalHornArrow m i) ≅
      orthogonalFreeArrow.{u, v} n (originalHornArrow m i) :=
  symmetricOrthogonalFreeArrowIso n (originalHornArrow m i)

/-- Every original orthogonal operator object is the actual image of an original
finite-bijection operator object. -/
theorem symmetricOrthogonal_obj_surjective :
    Function.Surjective symmetricOrthogonalOperatorIndexFunctor.{u, v}.obj := by
  intro b
  let n : SymIndex := ⟨FintypeCat.Skeleton.mk b.asIndex⟩
  refine ⟨PointedCGWH.symmetricOperatorObj n, ?_⟩
  cases b
  rfl

/-- The whole original free-horn families agree under actual Kan image after closure by arrow
isomorphisms. -/
theorem symmetricOrthogonal_levelJ_image :
    leftKanImage symmetricOrthogonalOperatorIndexFunctor.{u, v}
      (NativeK.levelJ (I := PointedCGWH.SymmetricOperatorIndex.{u, v})) =
        (NativeK.levelJ (I := OrthogonalOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure symmetricOrthogonalOperatorIndexFunctor
    symmetricOrthogonal_obj_surjective PointedCGWH.realizedHornInclusions

/-- The whole original free-boundary families agree under actual Kan image after closure by
arrow isomorphisms. -/
theorem symmetricOrthogonal_levelI_image :
    leftKanImage symmetricOrthogonalOperatorIndexFunctor.{u, v}
      (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})) =
        (NativeK.levelI (I := OrthogonalOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure symmetricOrthogonalOperatorIndexFunctor
    symmetricOrthogonal_obj_surjective PointedCGWH.realizedBoundaryInclusions

end FreeArrowTransport

section OriginalGenerators

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.Construction.modelCategory

/-- The complete original correlated boundary and second-endpoint cylinder generator. -/
def nativeGeneratorArrow {J L : Type} [EnrichedCategory PointedCGWH.{u, v} J]
    (s : NativeStabilizationFamily.{u, v} J L) (l : L) (m : ℕ) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} J) :=
  ScalarTransport.arrow (Arrow.mk (NativeK.boundaryMap m)) (Arrow.mk (NativeK.cylinderSource s l))

/-- The entire chosen scalar Leibniz arrow is the literal original native generator. -/
theorem nativeGeneratorArrow_eq {J L : Type} [EnrichedCategory PointedCGWH.{u, v} J]
    (s : NativeStabilizationFamily.{u, v} J L) (l : L) (m : ℕ) :
    nativeGeneratorArrow s l m = Arrow.mk (NativeK.generatorMap s l m) := rfl

/-- The whole actual Kan functor acts on the original correlated native generator. -/
def prolongedNativeGeneratorArrow {J H L : Type} [EnrichedCategory PointedCGWH.{u, v} J]
    [EnrichedCategory PointedCGWH.{u, v} H] (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (l : L) (m : ℕ) :
    Arrow (EnrichedFunctorCat PointedCGWH.{u, v} H) :=
  (leftKan k).mapArrow.obj (nativeGeneratorArrow s l m)

/-- Actual stabilization transport, the original cylinder and its scalar boundary construct the
generator isomorphism. -/
def leftKanNativeGeneratorIso {J H L M : Type} [EnrichedCategory PointedCGWH.{u, v} J]
    [EnrichedCategory PointedCGWH.{u, v} H] (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (t : NativeStabilizationFamily.{u, v} H M)
    (l : L) (h : M)
    (e : prolongedStabilizationArrow k (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅
      stabilizationArrow (t.source h) (t.target h) (t.coefficient h) (t.inclusion h)) (m : ℕ) :
    prolongedNativeGeneratorArrow k s l m ≅ nativeGeneratorArrow t h m :=
  ScalarTransport.throughIso k (Arrow.mk (NativeK.boundaryMap m))
    (Arrow.mk (NativeK.cylinderSource s l))
    (CylinderTransport.sourceThroughIso k
      (stabilizationArrow (s.source l) (s.target l) (s.coefficient l) (s.inclusion l)) e)

/-- The entire original symmetric generator retains both block labels and its boundary label. -/
def symmetricGeneratorArrow (n a : SymIndex) (m : ℕ) : Arrow Actual.SymmetricCarrier.{u, v} :=
  nativeGeneratorArrow Actual.symmetricFamily (n, a) m

/-- The entire original orthogonal generator retains both dimensions and its boundary label. -/
def orthogonalGeneratorArrow (n a m : ℕ) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  nativeGeneratorArrow Actual.orthogonalFamily (n, a) m

/-- The whole original symmetric correlated generator is prolonged by the actual Kan functor. -/
def symmetricProlongedGeneratorArrow (n a : SymIndex) (m : ℕ) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  prolongedNativeGeneratorArrow symmetricOrthogonalOperatorIndexFunctor
    Actual.symmetricFamily (n, a) m

/-- Every actual original symmetric correlated generator has its constructed orthogonal arrow
isomorphism. -/
def symmetricOrthogonalGeneratorIso (n a : SymIndex) (m : ℕ) :
    symmetricProlongedGeneratorArrow.{u, v} n a m ≅
      orthogonalGeneratorArrow.{u, v} n.of.len a.of.len m := by
  let j := symmetricOrthogonalOperatorIndexFunctor.{u, v}
  let s := Actual.symmetricFamily.{u, v}
  let t := Actual.orthogonalFamily.{u, v}
  let l := (n, a)
  let h := (n.of.len, a.of.len)
  let e : prolongedStabilizationArrow j (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅
        stabilizationArrow (t.source h) (t.target h) (t.coefficient h) (t.inclusion h) := by
    dsimp only [s, t, l, h, Actual.symmetricFamily, Actual.orthogonalFamily]
    exact symmetricOrthogonalStabilizationIso.{u, v} n a
  exact leftKanNativeGeneratorIso j s t l h e m

private theorem nativeGenerator_transport_mem {J H L M : Type}
    [EnrichedCategory PointedCGWH.{u, v} J] [EnrichedCategory PointedCGWH.{u, v} H]
    (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (t : NativeStabilizationFamily.{u, v} H M)
    (l : L) (h : M)
    (e : prolongedStabilizationArrow k (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅
      stabilizationArrow (t.source h) (t.target h) (t.coefficient h) (t.inclusion h)) (m : ℕ) :
    (NativeK.additionalGenerators t).isoClosure ((leftKan k).map (NativeK.generatorMap s l m)) :=
  ⟨_, _, NativeK.generatorMap t h m, NativeK.generatorMap_mem t h m,
    ⟨(leftKanNativeGeneratorIso k s t l h e m).symm⟩⟩

private theorem nativeGenerator_mem_image {J H L M : Type}
    [EnrichedCategory PointedCGWH.{u, v} J] [EnrichedCategory PointedCGWH.{u, v} H]
    (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (t : NativeStabilizationFamily.{u, v} H M)
    (l : L) (h : M)
    (e : prolongedStabilizationArrow k (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅
      stabilizationArrow (t.source h) (t.target h) (t.coefficient h) (t.inclusion h)) (m : ℕ) :
    leftKanImage k (NativeK.additionalGenerators s) (NativeK.generatorMap t h m) :=
  ⟨_, _, NativeK.generatorMap s l m, NativeK.generatorMap_mem s l m,
    ⟨leftKanNativeGeneratorIso k s t l h e m⟩⟩

private theorem additionalGenerators_image_le {J H L M : Type}
    [EnrichedCategory PointedCGWH.{u, v} J] [EnrichedCategory PointedCGWH.{u, v} H]
    (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (t : NativeStabilizationFamily.{u, v} H M)
    (q : L → M)
    (e : ∀ l, prolongedStabilizationArrow k (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅ stabilizationArrow
      (t.source (q l)) (t.target (q l)) (t.coefficient (q l)) (t.inclusion (q l))) :
    leftKanImage k (NativeK.additionalGenerators s) ≤
      (NativeK.additionalGenerators t).isoClosure := by
  apply (MorphismProperty.map_le_iff
    (NativeK.additionalGenerators s) (NativeK.additionalGenerators t).isoClosure).mpr
  intro X Y f hf
  rcases hf with ⟨⟨l, m⟩⟩
  exact nativeGenerator_transport_mem k s t l (q l) (e l) m

private theorem additionalGenerators_image_eq {J H L M : Type}
    [EnrichedCategory PointedCGWH.{u, v} J] [EnrichedCategory PointedCGWH.{u, v} H]
    (k : EnrichedFunctor PointedCGWH.{u, v} J H)
    (s : NativeStabilizationFamily.{u, v} J L) (t : NativeStabilizationFamily.{u, v} H M)
    (q : L → M) (hq : Function.Surjective q)
    (e : ∀ l, prolongedStabilizationArrow k (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅ stabilizationArrow
      (t.source (q l)) (t.target (q l)) (t.coefficient (q l)) (t.inclusion (q l))) :
    leftKanImage k (NativeK.additionalGenerators s) =
      (NativeK.additionalGenerators t).isoClosure := by
  apply le_antisymm (additionalGenerators_image_le k s t q e)
  apply (MorphismProperty.isoClosure_le_iff
    (NativeK.additionalGenerators t) (leftKanImage k (NativeK.additionalGenerators s))).mpr
  intro X Y f hf
  rcases hf with ⟨⟨h, m⟩⟩
  obtain ⟨l, rfl⟩ := hq h
  exact nativeGenerator_mem_image k s t l (q l) (e l) m

private theorem map_sup {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P Q : MorphismProperty C) : (P ⊔ Q).map F = P.map F ⊔ Q.map F := by
  ext X Y f
  constructor
  · rintro ⟨A, B, g, hg, he⟩
    rcases hg with hg | hg
    · exact Or.inl ⟨A, B, g, hg, he⟩
    · exact Or.inr ⟨A, B, g, hg, he⟩
  · rintro (h | h)
    · rcases h with ⟨A, B, g, hg, he⟩
      exact ⟨A, B, g, Or.inl hg, he⟩
    · rcases h with ⟨A, B, g, hg, he⟩
      exact ⟨A, B, g, Or.inr hg, he⟩

private theorem isoClosure_sup {C : Type*} [Category C] (P Q : MorphismProperty C) :
    (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure := by
  ext X Y f
  constructor
  · rintro ⟨A, B, g, hg, he⟩
    rcases hg with hg | hg
    · exact Or.inl ⟨A, B, g, hg, he⟩
    · exact Or.inr ⟨A, B, g, hg, he⟩
  · rintro (h | h)
    · rcases h with ⟨A, B, g, hg, he⟩
      exact ⟨A, B, g, Or.inl hg, he⟩
    · rcases h with ⟨A, B, g, hg, he⟩
      exact ⟨A, B, g, Or.inr hg, he⟩

/-- Actual Kan image identifies all original correlated extra generators after closure by arrow
isomorphisms. -/
theorem symmetricOrthogonal_additionalGenerators_image :
    leftKanImage symmetricOrthogonalOperatorIndexFunctor.{u, v}
      (NativeK.additionalGenerators Actual.symmetricFamily) =
        (NativeK.additionalGenerators Actual.orthogonalFamily).isoClosure := by
  let q : SymIndex × SymIndex → ℕ × ℕ := fun na => (na.1.of.len, na.2.of.len)
  have hq : Function.Surjective q := by
    rintro ⟨n, a⟩
    exact ⟨(⟨FintypeCat.Skeleton.mk n⟩, ⟨FintypeCat.Skeleton.mk a⟩), rfl⟩
  exact additionalGenerators_image_eq symmetricOrthogonalOperatorIndexFunctor
    Actual.symmetricFamily Actual.orthogonalFamily q hq
    (fun na => symmetricOrthogonalStabilizationIso na.1 na.2)

/-- Actual Kan image identifies the complete original K families after closure by arrow
isomorphisms. -/
theorem symmetricOrthogonal_K_image :
    leftKanImage symmetricOrthogonalOperatorIndexFunctor.{u, v} Actual.symmetricK =
      Actual.orthogonalK.isoClosure := by
  change leftKanImage symmetricOrthogonalOperatorIndexFunctor
    (NativeK.levelJ ⊔ NativeK.additionalGenerators Actual.symmetricFamily) =
      (NativeK.levelJ ⊔ NativeK.additionalGenerators Actual.orthogonalFamily).isoClosure
  rw [leftKanImage, map_sup, isoClosure_sup]
  exact congrArg₂ (fun P Q => P ⊔ Q)
    symmetricOrthogonal_levelJ_image symmetricOrthogonal_additionalGenerators_image

end OriginalGenerators

section Coefficient
variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A)
  {S T : PointedCGWH.{u, v}} (e : S ≅ T)
  (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))

/-- The forward source map is the genuine free Kan comparison followed by the original free
coefficient map. -/
theorem leftKanCoefficientStabilizationIso_hom_left :
    let sourceIndex := j.obj a
    let targetIndex := j.obj b
    let H := sourceIndex ⟶[PointedCGWH.{u, v}] targetIndex
    ∀ (E : T ⟶ H) (hD : D ≫ j.map a b = e.hom ≫ E),
    (leftKanCoefficientStabilizationIso j a b e D E hD).hom.left =
      (Kan.leftKanFreeIso j b).hom.app S ≫ (Free.functor (j.obj b)).map e.hom := by
  dsimp only
  intro E hD
  unfold leftKanCoefficientStabilizationIso
  refine (Arrow.isoMk_hom_left _ _ _).trans ?_
  exact (Iso.trans_hom _ _).trans
    (congrArg₂ (fun f g => f ≫ g) (Iso.app_hom (Kan.leftKanFreeIso j b) S)
      ((Free.functor (j.obj b)).mapIso_hom e))

/-- The forward target map is the genuine unit-coefficient free Kan comparison. -/
theorem leftKanCoefficientStabilizationIso_hom_right :
    let sourceIndex := j.obj a
    let targetIndex := j.obj b
    let H := sourceIndex ⟶[PointedCGWH.{u, v}] targetIndex
    ∀ (E : T ⟶ H) (hD : D ≫ j.map a b = e.hom ≫ E),
    (leftKanCoefficientStabilizationIso j a b e D E hD).hom.right =
      (Kan.leftKanFreeIso j a).hom.app (𝟙_ PointedCGWH.{u, v}) := by
  dsimp only
  intro E hD
  unfold leftKanCoefficientStabilizationIso
  exact (Arrow.isoMk_hom_right _ _ _).trans
    (Iso.app_hom (Kan.leftKanFreeIso j a) (𝟙_ PointedCGWH.{u, v}))

/-- The inverse source map retains the original coefficient inverse followed by the free Kan
inverse. -/
theorem leftKanCoefficientStabilizationIso_inv_left :
    let sourceIndex := j.obj a
    let targetIndex := j.obj b
    let H := sourceIndex ⟶[PointedCGWH.{u, v}] targetIndex
    ∀ (E : T ⟶ H) (hD : D ≫ j.map a b = e.hom ≫ E),
    (leftKanCoefficientStabilizationIso j a b e D E hD).inv.left =
      (Free.functor (j.obj b)).map e.inv ≫ (Kan.leftKanFreeIso j b).inv.app S := by
  dsimp only
  intro E hD
  unfold leftKanCoefficientStabilizationIso
  refine (Arrow.isoMk_inv_left _ _ _).trans ?_
  exact (Iso.trans_inv _ _).trans
    (congrArg₂ (fun f g => f ≫ g) ((Free.functor (j.obj b)).mapIso_inv e)
      (Iso.app_inv (Kan.leftKanFreeIso j b) S))

/-- The inverse target map is the genuine unit-coefficient free Kan inverse. -/
theorem leftKanCoefficientStabilizationIso_inv_right :
    let sourceIndex := j.obj a
    let targetIndex := j.obj b
    let H := sourceIndex ⟶[PointedCGWH.{u, v}] targetIndex
    ∀ (E : T ⟶ H) (hD : D ≫ j.map a b = e.hom ≫ E),
    (leftKanCoefficientStabilizationIso j a b e D E hD).inv.right =
      (Kan.leftKanFreeIso j a).inv.app (𝟙_ PointedCGWH.{u, v}) := by
  dsimp only
  intro E hD
  unfold leftKanCoefficientStabilizationIso
  exact (Arrow.isoMk_inv_right _ _ _).trans
    (Iso.app_inv (Kan.leftKanFreeIso j a) (𝟙_ PointedCGWH.{u, v}))

end Coefficient

section Target
variable {A : Type} [Category A] [EnrichedOrdinaryCategory PointedCGWH.{u, v} A]
  (a : A) {b c : A} (q : b ≅ c) (K : PointedCGWH.{u, v})
  (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))

/-- The forward target-index transport is the original whole contravariant free map. -/
theorem stabilizationTargetIso_hom_left :
    (stabilizationTargetIso a q K D).hom.left = freeIndexMap q.hom K := by
  unfold stabilizationTargetIso
  simp only [Arrow.isoMk', Arrow.isoMk_hom_left]
  rfl

/-- Target-index transport retains the identical original unit-coefficient target object. -/
theorem stabilizationTargetIso_hom_right :
    (stabilizationTargetIso a q K D).hom.right = 𝟙 (Free.object a (𝟙_ PointedCGWH.{u, v})) := by
  unfold stabilizationTargetIso
  simp only [Arrow.isoMk', Arrow.isoMk_hom_right, Iso.refl_hom]
  rfl

/-- The inverse target-index transport is the original whole inverse contravariant free map. -/
theorem stabilizationTargetIso_inv_left :
    (stabilizationTargetIso a q K D).inv.left = freeIndexMap q.inv K := by
  unfold stabilizationTargetIso
  simp only [Arrow.isoMk', Arrow.isoMk_inv_left]
  rfl

/-- Inverse target-index transport retains the identical original unit-coefficient target object. -/
theorem stabilizationTargetIso_inv_right :
    (stabilizationTargetIso a q K D).inv.right = 𝟙 (Free.object a (𝟙_ PointedCGWH.{u, v})) := by
  unfold stabilizationTargetIso
  simp only [Arrow.isoMk', Arrow.isoMk_inv_right, Iso.refl_inv]
  rfl

end Target

end HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
