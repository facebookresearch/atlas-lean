/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexStabilizationArrowTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationTransport

/-!
# Original sequential free stabilization arrow transport

The literal original one-circle sequential stabilization is prolonged through
both complete native index functors. The source comparison retains its circle
unitor, full sphere coefficient isomorphism and genuine inverse target block
permutation. Every forward and inverse endpoint map and full enriched Hom
component is exposed.

The same comparison transports the original mapping cylinder, both literal
interval endpoints, its contraction and retraction. The original free boundary
and every realized horn retain their full labels and naturalities. Every
original correlated sequential K generator maps into the unchanged full native
symmetric or orthogonal K family up to a whole arrow isomorphism.

The primary source is MMSS, *Model Categories of Diagram Spectra*, author
version dated December 30, 1999, Definition 8.4 and Lemma 8.5 (p. 25) and
Definition 9.3 (p. 29):
https://www.math.uchicago.edu/~may/PAPERS/mmssLMSDec30.pdf.
Here the original generators are the project's fixed freely pointed realized
simplicial boundary and horn families, with its native mapping-cylinder
choices. The symmetric and orthogonal families retain all original block
labels; this sequential comparison uses their original one-step members.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open PointedCGWH.SequentialSpectrum.StableK
  (stabilizationFamily_stabilization_eq_unitStabilizationMap)
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private def prolongedArrowEqIso {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (h : f = g) :
    (leftKan j).mapArrow.obj f ≅ (leftKan j).mapArrow.obj g :=
  eqToIso (congrArg (leftKan j).mapArrow.obj h)

private def coefficientTargetStabilizationIso {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (c : B)
    {S T : PointedCGWH.{u, v}} (e : S ≅ T)
    (q : ForgetEnrichment.of PointedCGWH.{u, v} c ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (j.obj b))
    (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (E : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] c))
    (hD : D ≫ j.map a b = e.hom ≫ E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom) :
    prolongedStabilizationArrow j a b S D ≅ stabilizationArrow (j.obj a) c T E := by
  let P : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) :=
    E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom
  let e1 := leftKanCoefficientStabilizationIso j a b e D P hD
  let e2 : stabilizationArrow (j.obj a) (j.obj b) T P ≅
      stabilizationArrow (j.obj a) c T E :=
    stabilizationTargetIso (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q T E
  exact e1 ≪≫ e2

section OriginalArrow

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]
  (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (c : B)
  {S T : PointedCGWH.{u, v}} (e : S ≅ T)
  (q : ForgetEnrichment.of PointedCGWH.{u, v} c ≅
    ForgetEnrichment.of PointedCGWH.{u, v} (j.obj b))
  (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
  (E : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] c))
  (hD : D ≫ j.map a b = e.hom ≫ E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
    (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom)
  (f : Free.object b S ⟶ Free.object a (𝟙_ PointedCGWH.{u, v}))
  (hf : f = CurrentFree.stabilization a b S D)

private def originalStabilizationSourceIso :
    (leftKan j).obj (Free.object b S) ≅ Free.object c T :=
  (Kan.leftKanFreeIso j b).app S ≪≫
    (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).mapIso e ≪≫ freeIndexIso q T

private def originalStabilizationTargetIso :
    (leftKan j).obj (Free.object a (𝟙_ PointedCGWH.{u, v})) ≅
      Free.object (j.obj a) (𝟙_ PointedCGWH.{u, v}) :=
  (Kan.leftKanFreeIso j a).app (𝟙_ PointedCGWH.{u, v})

include D hD hf in
private theorem originalStabilizationSquare :
    (originalStabilizationSourceIso j b c e q).hom ≫ CurrentFree.stabilization (j.obj a) c T E =
      (leftKan j).map f ≫ (originalStabilizationTargetIso j a).hom := by
  let P : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) :=
    E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom
  let es := (Kan.leftKanFreeIso j b).app S
  let cs := (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).mapIso e
  let qi : Free.object (j.obj b) T ≅ Free.object c T := freeIndexIso q T
  let et := (Kan.leftKanFreeIso j a).app (𝟙_ PointedCGWH.{u, v})
  have hi : qi.hom ≫ CurrentFree.stabilization (j.obj a) c T E =
      CurrentFree.stabilization (j.obj a) (j.obj b) T P :=
    stabilization_target_iso (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q T E
  have hs : CurrentFree.stabilization (j.obj a) (j.obj b) S (D ≫ j.map a b) =
      cs.hom ≫ CurrentFree.stabilization (j.obj a) (j.obj b) T P :=
    (congrArg (fun d : S ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) =>
      CurrentFree.stabilization (j.obj a) (j.obj b) S d) hD).trans
        (CurrentFree.stabilization_coefficient (j.obj a) (j.obj b) e.hom P).symm
  have hl : (leftKan j).map (CurrentFree.stabilization a b S D) ≫ et.hom =
      es.hom ≫ CurrentFree.stabilization (j.obj a) (j.obj b) S (D ≫ j.map a b) :=
    leftKan_stabilization j a b S D
  have hf' := congrArg (fun t : Free.object b S ⟶ Free.object a (𝟙_ PointedCGWH.{u, v}) =>
    (leftKan j).map t) hf
  change (es.hom ≫ cs.hom ≫ qi.hom) ≫ CurrentFree.stabilization (j.obj a) c T E =
    (leftKan j).map f ≫ et.hom
  calc
    _ = es.hom ≫ cs.hom ≫ (qi.hom ≫ CurrentFree.stabilization (j.obj a) c T E) := by
      simp only [Category.assoc]
    _ = es.hom ≫ cs.hom ≫ CurrentFree.stabilization (j.obj a) (j.obj b) T P :=
      congrArg (fun r => es.hom ≫ cs.hom ≫ r) hi
    _ = es.hom ≫ CurrentFree.stabilization (j.obj a) (j.obj b) S (D ≫ j.map a b) :=
      congrArg (fun r => es.hom ≫ r) hs.symm
    _ = (leftKan j).map (CurrentFree.stabilization a b S D) ≫ et.hom := hl.symm
    _ = (leftKan j).map f ≫ et.hom := congrArg (fun r => r ≫ et.hom) hf'.symm

private def originalStabilizationIso
    {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (c : B)
    {S T : PointedCGWH.{u, v}} (e : S ≅ T)
    (q : ForgetEnrichment.of PointedCGWH.{u, v} c ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (j.obj b))
    (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (E : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] c))
    (hD : D ≫ j.map a b = e.hom ≫ E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom)
    (f : Free.object b S ⟶ Free.object a (𝟙_ PointedCGWH.{u, v}))
    (hf : f = CurrentFree.stabilization a b S D) :
    (leftKan j).mapArrow.obj (Arrow.mk f) ≅ stabilizationArrow (j.obj a) c T E :=
  Arrow.isoMk' ((leftKan j).map f) (CurrentFree.stabilization (j.obj a) c T E)
    (originalStabilizationSourceIso j b c e q) (originalStabilizationTargetIso j a)
    (originalStabilizationSquare (j := j) (a := a) (b := b) (c := c)
      (e := e) (q := q) (D := D) (E := E) (hD := hD) (f := f) (hf := hf))

private theorem originalStabilizationIso_hom_left :
    (originalStabilizationIso j a b c e q D E hD f hf).hom.left =
      (Kan.leftKanFreeIso j b).hom.app S ≫
        (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).map e.hom ≫ freeIndexMap q.hom T := by
  unfold originalStabilizationIso originalStabilizationSourceIso originalStabilizationTargetIso
  refine (Arrow.isoMk_hom_left _ _ _).trans ?_
  refine (Iso.trans_hom _ _).trans ?_
  exact congrArg₂ (fun r s => r ≫ s) (Iso.app_hom (Kan.leftKanFreeIso j b) S)
    ((Iso.trans_hom _ _).trans (congrArg₂ (fun r s => r ≫ s)
      ((Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).mapIso_hom e)
      (show (freeIndexIso q T).hom = freeIndexMap q.hom T from rfl)))

private theorem originalStabilizationIso_hom_right :
    (originalStabilizationIso j a b c e q D E hD f hf).hom.right =
      (Kan.leftKanFreeIso j a).hom.app (𝟙_ PointedCGWH.{u, v}) := by
  unfold originalStabilizationIso originalStabilizationSourceIso originalStabilizationTargetIso
  exact (Arrow.isoMk_hom_right _ _ _).trans
    (Iso.app_hom (Kan.leftKanFreeIso j a) (𝟙_ PointedCGWH.{u, v}))

private theorem originalStabilizationIso_inv_left :
    (originalStabilizationIso j a b c e q D E hD f hf).inv.left =
      freeIndexMap q.inv T ≫ (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).map e.inv ≫
        (Kan.leftKanFreeIso j b).inv.app S := by
  unfold originalStabilizationIso originalStabilizationSourceIso originalStabilizationTargetIso
  refine (Arrow.isoMk_inv_left _ _ _).trans ?_
  refine (Iso.trans_inv _ _).trans ?_
  exact (congrArg₂ (fun r s => r ≫ s)
    ((Iso.trans_inv _ _).trans (congrArg₂ (fun r s => r ≫ s)
      (show (freeIndexIso q T).inv = freeIndexMap q.inv T from rfl)
      ((Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).mapIso_inv e)))
    (Iso.app_inv (Kan.leftKanFreeIso j b) S)).trans (Category.assoc _ _ _)

private theorem originalStabilizationIso_inv_right :
    (originalStabilizationIso j a b c e q D E hD f hf).inv.right =
      (Kan.leftKanFreeIso j a).inv.app (𝟙_ PointedCGWH.{u, v}) := by
  unfold originalStabilizationIso originalStabilizationSourceIso originalStabilizationTargetIso
  exact (Arrow.isoMk_inv_right _ _ _).trans
    (Iso.app_inv (Kan.leftKanFreeIso j a) (𝟙_ PointedCGWH.{u, v}))

private theorem originalStabilizationIso_hom_left_component (d : B) :
    component (originalStabilizationIso j a b c e q D E hD f hf).hom.left d =
      component ((Kan.leftKanFreeIso j b).hom.app S) d ≫
      (e.hom ▷ (j.obj b ⟶[PointedCGWH.{u, v}] d)) ≫
      T ◁ eHomWhiskerRight PointedCGWH.{u, v} q.hom (ForgetEnrichment.of PointedCGWH.{u, v} d) := by
  let k : (leftKan j).obj (Free.object b S) ⟶ Free.object (j.obj b) S :=
    (Kan.leftKanFreeIso j b).hom.app S
  let ce : Free.object (j.obj b) S ⟶ Free.object (j.obj b) T :=
    (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).map e.hom
  let qi : Free.object (j.obj b) T ⟶ Free.object c T := freeIndexMap q.hom T
  have ht : (originalStabilizationIso j a b c e q D E hD f hf).hom.left = k ≫ ce ≫ qi :=
    originalStabilizationIso_hom_left j a b c e q D E hD f hf
  have hc : component ce d = e.hom ▷ (j.obj b ⟶[PointedCGWH.{u, v}] d) :=
    Free.coefficientMap_component (j.obj b) e.hom d
  have hq : component qi d = T ◁ eHomWhiskerRight PointedCGWH.{u, v}
      q.hom (ForgetEnrichment.of PointedCGWH.{u, v} d) :=
    freeIndexMap_component q.hom T (ForgetEnrichment.of PointedCGWH.{u, v} d)
  exact (congrArg (fun r => component r d) ht).trans
    ((component_comp k (ce ≫ qi) d).trans
      (congrArg (fun r => component k d ≫ r)
        ((component_comp ce qi d).trans (congrArg₂ (fun r s => r ≫ s) hc hq))))

private theorem originalStabilizationIso_inv_left_component (d : B) :
    component (originalStabilizationIso j a b c e q D E hD f hf).inv.left d =
      T ◁ eHomWhiskerRight PointedCGWH.{u, v} q.inv (ForgetEnrichment.of PointedCGWH.{u, v} d) ≫
      (e.inv ▷ (j.obj b ⟶[PointedCGWH.{u, v}] d)) ≫
      component ((Kan.leftKanFreeIso j b).inv.app S) d := by
  let k : Free.object (j.obj b) S ⟶ (leftKan j).obj (Free.object b S) :=
    (Kan.leftKanFreeIso j b).inv.app S
  let ce : Free.object (j.obj b) T ⟶ Free.object (j.obj b) S :=
    (Free.functor (V := PointedCGWH.{u, v}) (j.obj b)).map e.inv
  let qi : Free.object c T ⟶ Free.object (j.obj b) T := freeIndexMap q.inv T
  have ht : (originalStabilizationIso j a b c e q D E hD f hf).inv.left = qi ≫ ce ≫ k :=
    originalStabilizationIso_inv_left j a b c e q D E hD f hf
  have hc : component ce d = e.inv ▷ (j.obj b ⟶[PointedCGWH.{u, v}] d) :=
    Free.coefficientMap_component (j.obj b) e.inv d
  have hq : component qi d = T ◁ eHomWhiskerRight PointedCGWH.{u, v}
      q.inv (ForgetEnrichment.of PointedCGWH.{u, v} d) :=
    freeIndexMap_component q.inv T (ForgetEnrichment.of PointedCGWH.{u, v} d)
  exact (congrArg (fun r => component r d) ht).trans
    ((component_comp qi (ce ≫ k) d).trans
      (congrArg₂ (fun r s => r ≫ s) hq
        ((component_comp ce k d).trans (congrArg (fun r => r ≫ component k d) hc))))

private theorem originalStabilizationIso_full_component (m : A) :
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object b S)) m ≫
      component (originalStabilizationIso j a b c e q D E hD f hf).hom.left (j.obj m) =
    S ◁ j.map b m ≫ (e.hom ▷ (j.obj b ⟶[PointedCGWH.{u, v}] j.obj m)) ≫
      T ◁ eHomWhiskerRight PointedCGWH.{u, v} q.hom
        (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj m)) := by
  let eta := component ((leftKanRestrictionAdjunction j).unit.app (Free.object b S)) m
  let k := component ((Kan.leftKanFreeIso j b).hom.app S) (j.obj m)
  let ce := e.hom ▷ (j.obj b ⟶[PointedCGWH.{u, v}] j.obj m)
  let qi := T ◁ eHomWhiskerRight PointedCGWH.{u, v} q.hom
    (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj m))
  have hcomp : component (originalStabilizationIso j a b c e q D E hD f hf).hom.left
      (j.obj m) = k ≫ ce ≫ qi :=
    originalStabilizationIso_hom_left_component j a b c e q D E hD f hf (j.obj m)
  have hk : eta ≫ k = S ◁ j.map b m := leftKanFreeIso_full_component j b m S
  calc
    _ = eta ≫ k ≫ ce ≫ qi := congrArg (fun r => eta ≫ r) hcomp
    _ = (eta ≫ k) ≫ ce ≫ qi := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun r => r ≫ ce ≫ qi) hk

end OriginalArrow

/-- The actual original unit-normalized sequential free stabilization arrow. -/
def sequentialStabilizationArrow (n : ℕ) : Arrow PointedCGWH.SequentialSpectrum.{u, v} :=
  Arrow.mk (PointedCGWH.SequentialSpectrum.unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)

/-- The original sequential arrow is the unchanged native family's original whole Free adjunct. -/
theorem sequentialStabilizationArrow_eq (n : ℕ) :
    sequentialStabilizationArrow.{u, v} n =
      stabilizationArrow (sequentialDegree n) (sequentialDegree (n + 1)) PointedCGWH.sphereOne
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
          n).inv :=
  (congrArg Arrow.mk
    (stabilizationFamily_stabilization_eq_unitStabilizationMap n)).symm

/-- The actual native symmetric one-step member of the unchanged full family. -/
def symmetricOneStepStabilizationArrow (n : ℕ) : Arrow Actual.SymmetricCarrier.{u, v} :=
  symmetricStabilizationArrow (finiteIndex n) (finiteIndex 1)

/-- The original sequential free stabilization is prolonged by the whole actual Kan functor. -/
def sequentialSymmetricProlongedStabilizationArrow (n : ℕ) : Arrow Actual.SymmetricCarrier.{u, v} :=
  (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow.obj
    (sequentialStabilizationArrow n)

private def rawSequentialSymmetricStabilizationIso (n : ℕ) :=
  coefficientTargetStabilizationIso sequentialSymmetricOperatorIndexFunctor.{u, v}
      (sequentialDegree n) (sequentialDegree (n + 1))
      (PointedCGWH.symmetricOperatorObj (finiteIndex n ⊗ finiteIndex 1))
      circleToPowerOneIso (successorIndexIso n)
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
        n).inv
      (Actual.symmetricNu (finiteIndex n) (finiteIndex 1)) (sequential_inclusion_factor n)

/-- The actual prolongation is compared with the original symmetric map by the coefficient
unitor and the real contravariant target-index map. -/
def sequentialSymmetricStabilizationIso (n : ℕ) :
    sequentialSymmetricProlongedStabilizationArrow.{u, v} n ≅
      symmetricOneStepStabilizationArrow.{u, v} n :=
  originalStabilizationIso sequentialSymmetricOperatorIndexFunctor
    (sequentialDegree n) (sequentialDegree (n + 1))
    (PointedCGWH.symmetricOperatorObj (finiteIndex n ⊗ finiteIndex 1))
    circleToPowerOneIso (successorIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
      n).inv
    (Actual.symmetricNu (finiteIndex n) (finiteIndex 1)) (sequential_inclusion_factor n)
    (PointedCGWH.SequentialSpectrum.unitStabilizationMap PointedCGWH.sphereOne n)
    (stabilizationFamily_stabilization_eq_unitStabilizationMap n).symm

/-- The full forward source map retains the Kan comparison, circle unitor and target permutation. -/
theorem sequentialSymmetricStabilizationIso_hom_left (n : ℕ) :
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.left =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor
        (sequentialDegree (n + 1))).hom.app PointedCGWH.sphereOne ≫
      (Free.functor (V := PointedCGWH.{u, v}) (symmetricDegree (n + 1))).map
        circleToPowerOneIso.hom ≫
      freeIndexMap (successorIndexIso n).hom
        (PointedCGWH.sphereSequence.functor.obj (finiteIndex 1)) :=
  originalStabilizationIso_hom_left ..

/-- The full forward target map is the original free Kan unit-coefficient comparison. -/
theorem sequentialSymmetricStabilizationIso_hom_right (n : ℕ) :
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.right =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor
        (sequentialDegree n)).hom.app (𝟙_ PointedCGWH.{u, v}) :=
  originalStabilizationIso_hom_right ..

/-- The full inverse source uses the genuine inverse target permutation and inverse circle unitor.
-/
theorem sequentialSymmetricStabilizationIso_inv_left (n : ℕ) :
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.left =
      freeIndexMap (successorIndexIso n).inv
        (PointedCGWH.sphereSequence.functor.obj (finiteIndex 1)) ≫
      (Free.functor (V := PointedCGWH.{u, v}) (symmetricDegree (n + 1))).map
        circleToPowerOneIso.inv ≫
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor
        (sequentialDegree (n + 1))).inv.app PointedCGWH.sphereOne :=
  originalStabilizationIso_inv_left ..

/-- The full inverse target map retains the original free Kan inverse. -/
theorem sequentialSymmetricStabilizationIso_inv_right (n : ℕ) :
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.right =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor
        (sequentialDegree n)).inv.app (𝟙_ PointedCGWH.{u, v}) :=
  originalStabilizationIso_inv_right ..

/-- The same whole original free-arrow comparison transports the entire original cylinder. -/
def sequentialSymmetricCylinderIso (n : ℕ) :
    CylinderTransport.prolongedObject sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialStabilizationArrow n) ≅
      PointedCGWH.EnrichedIntervalMappingCylinder.object (symmetricOneStepStabilizationArrow n) :=
  CylinderTransport.throughIso sequentialSymmetricOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialSymmetricStabilizationIso n)

/-- The original second-endpoint source arrow is transported as an entire arrow. -/
def sequentialSymmetricCylinderSourceIso (n : ℕ) :
    CylinderTransport.prolongedSourceArrow sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialStabilizationArrow n) ≅
      Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.source
        (symmetricOneStepStabilizationArrow n)) :=
  CylinderTransport.sourceThroughIso sequentialSymmetricOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialSymmetricStabilizationIso n)

/-- The original cylinder retraction is transported as an entire arrow. -/
def sequentialSymmetricCylinderRetractionIso (n : ℕ) :
    CylinderTransport.prolongedRetractionArrow sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialStabilizationArrow n) ≅
      Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.retraction
        (symmetricOneStepStabilizationArrow n)) :=
  CylinderTransport.retractionThroughIso sequentialSymmetricOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialSymmetricStabilizationIso n)

/-- The original circle unitor followed by the complete original orthogonal sphere Iso. -/
def sequentialOrthogonalCoefficientIso : PointedCGWH.sphereOne.{u, v} ≅
  PointedCGWH.orthogonalSphere.{u, v} 1 :=
  circleToPowerOneIso ≪≫ originalSymmetricOrthogonalCoefficientIso (finiteIndex 1)

/-- The real native target permutation mapped into the original orthogonal operator index. -/
def successorOrthogonalIndexIso (n : ℕ) :
    ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex (n + 1)) ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex (n + 1)) :=
  symmetricOrthogonalOperatorIndexFunctor.forget.mapIso (successorIndexIso n)

private theorem indexInclusion_comp {A B C : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    [EnrichedCategory PointedCGWH.{u, v} C]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (l : EnrichedFunctor PointedCGWH.{u, v} B C)
    (a b : A) (c : B) {S T U : PointedCGWH.{u, v}} (e : S ≅ T) (f : T ≅ U)
    (q : ForgetEnrichment.of PointedCGWH.{u, v} c ≅ ForgetEnrichment.of PointedCGWH.{u, v} (j.obj
      b))
    (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (E : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] c))
    (N : U ⟶ (l.obj (j.obj a) ⟶[PointedCGWH.{u, v}] l.obj c))
    (hD : D ≫ j.map a b = e.hom ≫ E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom)
    (hE : E ≫ l.map (j.obj a) c = f.hom ≫ N) :
    D ≫ (j.comp PointedCGWH.{u, v} l).map a b = (e ≪≫ f).hom ≫ N ≫
      eHomWhiskerLeft PointedCGWH.{u, v} (ForgetEnrichment.of PointedCGWH.{u, v} (l.obj (j.obj a)))
        (l.forget.mapIso q).hom := by
  let P : (j.obj a ⟶[PointedCGWH.{u, v}] c) ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) :=
    eHomWhiskerLeft PointedCGWH.{u, v} (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom
  let Q : (l.obj (j.obj a) ⟶[PointedCGWH.{u, v}] l.obj c) ⟶
      (l.obj (j.obj a) ⟶[PointedCGWH.{u, v}] l.obj (j.obj b)) :=
    eHomWhiskerLeft PointedCGWH.{u, v} (ForgetEnrichment.of PointedCGWH.{u, v} (l.obj (j.obj a)))
      (l.forget.map q.hom)
  have hP : P ≫ l.map (j.obj a) (j.obj b) = l.map (j.obj a) c ≫ Q :=
    EnrichedFunctor.map_eHomWhiskerLeft_forget l (j.obj a) c (j.obj b) q.hom
  change D ≫ (j.map a b ≫ l.map (j.obj a) (j.obj b)) = (e.hom ≫ f.hom) ≫ N ≫ Q
  calc
    _ = (D ≫ j.map a b) ≫ l.map (j.obj a) (j.obj b) := (Category.assoc _ _ _).symm
    _ = (e.hom ≫ E ≫ P) ≫ l.map (j.obj a) (j.obj b) := congrArg (fun h => h ≫ _) hD
    _ = e.hom ≫ E ≫ (P ≫ l.map (j.obj a) (j.obj b)) := by simp only [Category.assoc]
    _ = e.hom ≫ E ≫ (l.map (j.obj a) c ≫ Q) := congrArg (fun h => e.hom ≫ E ≫ h) hP
    _ = e.hom ≫ (E ≫ l.map (j.obj a) c) ≫ Q := by simp only [Category.assoc]
    _ = e.hom ≫ (f.hom ≫ N) ≫ Q := congrArg (fun h => e.hom ≫ h ≫ Q) hE
    _ = (e.hom ≫ f.hom) ≫ N ≫ Q := by simp only [Category.assoc]

/-- The original successor inclusion through both full native Hom maps. -/
def sequentialOrthogonalInclusion (n : ℕ) : PointedCGWH.sphereOne.{u, v} ⟶
    (OrthogonalOperatorIndex.ofIndex n ⟶[PointedCGWH.{u, v}] OrthogonalOperatorIndex.ofIndex (n +
      1)) :=
  (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
    n).inv ≫
    sequentialOrthogonalOperatorIndexFunctor.map (sequentialDegree n) (sequentialDegree (n + 1))

/-- Full target-Hom postcomposition by the genuine mapped target permutation. -/
def successorOrthogonalHomMap (n : ℕ) :
    (OrthogonalOperatorIndex.ofIndex n ⟶[PointedCGWH.{u, v}] OrthogonalOperatorIndex.ofIndex (n +
      1)) ⟶
    (OrthogonalOperatorIndex.ofIndex n ⟶[PointedCGWH.{u, v}] OrthogonalOperatorIndex.ofIndex (n +
      1)) :=
  eHomWhiskerLeft PointedCGWH.{u, v}
    (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex n))
      (successorOrthogonalIndexIso n).hom

/-- Direct composite inclusion transport retains the real coefficient and target-index maps. -/
theorem sequentialOrthogonal_inclusion_factor (n : ℕ) :
    sequentialOrthogonalInclusion.{u, v} n = sequentialOrthogonalCoefficientIso.hom ≫
      OrthogonalOperatorIndex.nu.{u, v} n 1 ≫ successorOrthogonalHomMap n :=
  indexInclusion_comp
    (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
    (B := PointedCGWH.SymmetricOperatorIndex.{u, v})
    (C := OrthogonalOperatorIndex.{u, v})
    (S := PointedCGWH.sphereOne.{u, v})
    (T := PointedCGWH.sphereSequence.functor.obj (finiteIndex 1))
    (U := PointedCGWH.orthogonalSphere.{u, v} 1)
    sequentialSymmetricOperatorIndexFunctor.{u, v}
    symmetricOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree n) (sequentialDegree (n + 1))
    (PointedCGWH.symmetricOperatorObj (finiteIndex n ⊗ finiteIndex 1))
    circleToPowerOneIso (originalSymmetricOrthogonalCoefficientIso (finiteIndex 1))
      (successorIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
      n).inv
    (Actual.symmetricNu (finiteIndex n) (finiteIndex 1)) (OrthogonalOperatorIndex.nu n 1)
    (sequential_inclusion_factor n) (symmetricOrthogonal_inclusion (finiteIndex n) (finiteIndex 1))


/-- The original orthogonal one-step member of the complete original native family. -/
def orthogonalOneStepStabilizationArrow (n : ℕ) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  orthogonalStabilizationArrow (finiteIndex n) (finiteIndex 1)

/-- Actual direct prolongation applies both full index maps to the original sequential arrow. -/
def sequentialOrthogonalProlongedStabilizationArrow (n : ℕ) : Arrow Actual.OrthogonalCarrier.{u, v}
  :=
  (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow.obj
    (sequentialStabilizationArrow n)

/-- The actual direct original free-arrow comparison retains the coefficient and real target
  permutation. -/
def sequentialOrthogonalStabilizationIso (n : ℕ) :
    sequentialOrthogonalProlongedStabilizationArrow.{u, v} n ≅
      orthogonalOneStepStabilizationArrow.{u, v} n :=
  originalStabilizationIso
    (A := PointedCGWH.Spectra.Sequential.Index.{u, v})
    (B := OrthogonalOperatorIndex.{u, v})
    (S := PointedCGWH.sphereOne.{u, v})
    (T := PointedCGWH.orthogonalSphere.{u, v} 1)
    sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree n) (sequentialDegree (n + 1)) (OrthogonalOperatorIndex.ofIndex (n + 1))
    sequentialOrthogonalCoefficientIso (successorOrthogonalIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
      n).inv
    (OrthogonalOperatorIndex.nu n 1) (sequentialOrthogonal_inclusion_factor n)
    (PointedCGWH.SequentialSpectrum.unitStabilizationMap PointedCGWH.sphereOne n)
    (stabilizationFamily_stabilization_eq_unitStabilizationMap n).symm

/-- The direct forward source keeps both native index maps, the coefficient and actual permutation.
-/
theorem sequentialOrthogonalStabilizationIso_hom_left (n : ℕ) :
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor
        (sequentialDegree (n + 1))).hom.app PointedCGWH.sphereOne ≫
      (Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex (n + 1))).map
        sequentialOrthogonalCoefficientIso.hom ≫
      freeIndexMap (successorOrthogonalIndexIso n).hom (PointedCGWH.orthogonalSphere 1) := by
  rfl

/-- The direct forward target is the full original unit-coefficient free Kan map. -/
theorem sequentialOrthogonalStabilizationIso_hom_right (n : ℕ) :
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor
        (sequentialDegree n)).hom.app (𝟙_ PointedCGWH.{u, v}) :=
  originalStabilizationIso_hom_right ..

/-- Every full native Hom component retains the actual coefficient and target-index inverse maps. -/
theorem sequentialOrthogonalStabilizationIso_inv_left_component (n : ℕ) (d :
  OrthogonalOperatorIndex.{u, v}) :
    component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left d =
      (PointedCGWH.orthogonalSphere.{u, v} 1) ◁ eHomWhiskerRight PointedCGWH.{u, v}
        (successorOrthogonalIndexIso.{u, v} n).inv (ForgetEnrichment.of PointedCGWH.{u, v} d) ≫
      (sequentialOrthogonalCoefficientIso.{u, v}.inv ▷ ((OrthogonalOperatorIndex.ofIndex (n + 1))
        ⟶[PointedCGWH.{u, v}] d)) ≫
      component ((Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialDegree (n + 1))).inv.app PointedCGWH.sphereOne) d := by
  exact originalStabilizationIso_inv_left_component ..

/-- The direct inverse source keeps the inverse continuous target action and coefficient. -/
theorem sequentialOrthogonalStabilizationIso_inv_left (n : ℕ) :
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left =
      (show Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))
          (PointedCGWH.orthogonalSphere.{u, v} 1) ⟶
        (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj
          (Free.object (sequentialDegree.{u, v} (n + 1)) PointedCGWH.sphereOne.{u, v}) from
        freeIndexMap (successorOrthogonalIndexIso.{u, v} n).inv
          (PointedCGWH.orthogonalSphere.{u, v} 1) ≫
        (Free.functor (V := PointedCGWH.{u, v})
          (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj (sequentialDegree (n + 1)))).map
          sequentialOrthogonalCoefficientIso.{u, v}.inv ≫
        (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
          (sequentialDegree (n + 1))).inv.app PointedCGWH.sphereOne) := by
  unfold sequentialOrthogonalStabilizationIso originalStabilizationIso
    originalStabilizationSourceIso originalStabilizationTargetIso
  exact Category.assoc _ _ _

/-- The direct inverse target is the full original free Kan inverse. -/
theorem sequentialOrthogonalStabilizationIso_inv_right (n : ℕ) :
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor
        (sequentialDegree n)).inv.app (𝟙_ PointedCGWH.{u, v}) :=
  originalStabilizationIso_inv_right ..

/-- The same direct comparison transports the original whole mapping cylinder. -/
def sequentialOrthogonalCylinderIso (n : ℕ) :
    CylinderTransport.prolongedObject sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialStabilizationArrow n) ≅
      PointedCGWH.EnrichedIntervalMappingCylinder.object (orthogonalOneStepStabilizationArrow n) :=
  CylinderTransport.throughIso sequentialOrthogonalOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialOrthogonalStabilizationIso n)

/-- The actual original second-endpoint source retains both full Arrow endpoint maps. -/
def sequentialOrthogonalCylinderSourceIso (n : ℕ) :
    CylinderTransport.prolongedSourceArrow sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialStabilizationArrow n) ≅
      Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.source
        (orthogonalOneStepStabilizationArrow n)) :=
  CylinderTransport.sourceThroughIso sequentialOrthogonalOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialOrthogonalStabilizationIso n)

/-- The original direct mapping-cylinder contraction and retraction retain the full target map. -/
def sequentialOrthogonalCylinderRetractionIso (n : ℕ) :
    Arrow.mk ((leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n)) ≅
      Arrow.mk (PointedCGWH.EnrichedIntervalMappingCylinder.retraction
        (Arrow.mk (NativeK.stabilization Actual.orthogonalFamily.{u, v} (n, 1)))) :=
  CylinderTransport.retractionThroughIso sequentialOrthogonalOperatorIndexFunctor
    (sequentialStabilizationArrow n) (sequentialOrthogonalStabilizationIso n)

/-- The literal original paired realized-boundary generator of the sequential construction. -/
def sequentialGeneratorArrow (n m : ℕ) : Arrow PointedCGWH.SequentialSpectrum.{u, v} :=
  Arrow.mk (PointedCGWH.SequentialSpectrum.StableK.generatorMap n m)

/-- The whole shared-family generator is the same literal original sequential n,m arrow. -/
theorem sequentialGeneratorArrow_eq_native (n m : ℕ) :
    sequentialGeneratorArrow.{u, v} n m =
      nativeGeneratorArrow PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily n m :=
  (PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily_generatorArrow_eq n m).symm.trans
    (nativeGeneratorArrow_eq PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily n m).symm

/-- The original symmetric n,m paired generator at the actual full-family one-step member. -/
def symmetricOneStepGeneratorArrow (n m : ℕ) : Arrow Actual.SymmetricCarrier.{u, v} :=
  nativeGeneratorArrow Actual.symmetricFamily (finiteIndex n, finiteIndex 1) m

/-- The literal symmetric native generator map is recovered as a whole arrow. -/
theorem symmetricOneStepGeneratorArrow_eq_original (n m : ℕ) :
    symmetricOneStepGeneratorArrow.{u, v} n m =
      Arrow.mk (NativeK.generatorMap Actual.symmetricFamily (finiteIndex n, finiteIndex 1) m) :=
  nativeGeneratorArrow_eq Actual.symmetricFamily (finiteIndex n, finiteIndex 1) m

/-- The original orthogonal n,m paired generator at the same one-step family member. -/
def orthogonalOneStepGeneratorArrow (n m : ℕ) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  nativeGeneratorArrow Actual.orthogonalFamily (n, 1) m

/-- The literal original orthogonal generator map is recovered as a whole arrow. -/
theorem orthogonalOneStepGeneratorArrow_eq_original (n m : ℕ) :
    orthogonalOneStepGeneratorArrow.{u, v} n m =
      Arrow.mk (NativeK.generatorMap Actual.orthogonalFamily (n, 1) m) :=
  nativeGeneratorArrow_eq Actual.orthogonalFamily (n, 1) m

/-- The complete actual sequential generator Arrow is prolonged through the original index map. -/
def sequentialSymmetricProlongedGeneratorArrow (n m : ℕ) : Arrow Actual.SymmetricCarrier.{u, v} :=
  (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow.obj (sequentialGeneratorArrow n
    m)

/-- Every original correlated n,m boundary generator is transported through the whole
  tensor/pushout map. -/
def sequentialSymmetricGeneratorIso (n m : ℕ) :
    sequentialSymmetricProlongedGeneratorArrow.{u, v} n m ≅ symmetricOneStepGeneratorArrow.{u, v} n
      m :=
  prolongedArrowEqIso sequentialSymmetricOperatorIndexFunctor (sequentialGeneratorArrow_eq_native n
    m) ≪≫
    leftKanNativeGeneratorIso sequentialSymmetricOperatorIndexFunctor
      PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily Actual.symmetricFamily
      n (finiteIndex n, finiteIndex 1) (rawSequentialSymmetricStabilizationIso n) m

/-- The complete actual paired generator is prolonged through both full original index maps. -/
def sequentialOrthogonalProlongedGeneratorArrow (n m : ℕ) : Arrow Actual.OrthogonalCarrier.{u, v} :=
  (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow.obj (sequentialGeneratorArrow
    n m)

/-- Every original correlated n,m boundary generator has the actual direct orthogonal transport. -/
private def rawSequentialOrthogonalStabilizationIso (n : ℕ) :=
  coefficientTargetStabilizationIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree n) (sequentialDegree (n + 1)) (OrthogonalOperatorIndex.ofIndex (n + 1))
    sequentialOrthogonalCoefficientIso (successorOrthogonalIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso PointedCGWH.sphereOne
      n).inv
    (OrthogonalOperatorIndex.nu n 1) (sequentialOrthogonal_inclusion_factor n)

/-- Every original n,m generator is compared by the actual direct Lan/cylinder/boundary maps. -/
def sequentialOrthogonalGeneratorIso (n m : ℕ) :
    sequentialOrthogonalProlongedGeneratorArrow.{u, v} n m ≅ orthogonalOneStepGeneratorArrow.{u, v}
      n m := by
  let j := sequentialOrthogonalOperatorIndexFunctor.{u, v}
  let s := PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily.{u, v}
  let t := Actual.orthogonalFamily.{u, v}
  let l := n
  let h := (n, 1)
  let e : prolongedStabilizationArrow j (s.source l) (s.target l)
      (s.coefficient l) (s.inclusion l) ≅
        stabilizationArrow (t.source h) (t.target h) (t.coefficient h) (t.inclusion h) := by
    dsimp only [s, t, l, h, PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily,
      Actual.orthogonalFamily]
    exact rawSequentialOrthogonalStabilizationIso.{u, v} n
  exact prolongedArrowEqIso j (sequentialGeneratorArrow_eq_native n m) ≪≫
    leftKanNativeGeneratorIso j s t l h e m


section StabilizationHomComponents

/-- Every full native Hom component retains the actual coefficient and target-index maps. -/
theorem sequentialSymmetricStabilizationIso_hom_left_component (n : ℕ) (d :
  PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    component (sequentialSymmetricStabilizationIso.{u, v} n).hom.left d =
      component ((Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialDegree (n + 1))).hom.app PointedCGWH.sphereOne) d ≫
      (circleToPowerOneIso.{u, v}.hom ▷ ((symmetricDegree.{u, v} (n + 1)) ⟶[PointedCGWH.{u, v}] d))
        ≫
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1)) ◁ eHomWhiskerRight
        PointedCGWH.{u, v}
        (successorIndexIso.{u, v} n).hom (ForgetEnrichment.of PointedCGWH.{u, v} d) := by
  exact originalStabilizationIso_hom_left_component ..

/-- The original unit-coefficient target comparison retains its full component. -/
theorem sequentialSymmetricStabilizationIso_hom_right_component (n : ℕ) (d :
  PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    component (sequentialSymmetricStabilizationIso.{u, v} n).hom.right d =
      component ((Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialDegree n)).hom.app (𝟙_ PointedCGWH.{u, v})) d :=
  congrArg (fun r => component r d) (sequentialSymmetricStabilizationIso_hom_right n)

/-- Every full native Hom component retains the actual coefficient and target-index inverse maps. -/
theorem sequentialSymmetricStabilizationIso_inv_left_component (n : ℕ) (d :
  PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    component (sequentialSymmetricStabilizationIso.{u, v} n).inv.left d =
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1)) ◁ eHomWhiskerRight
        PointedCGWH.{u, v}
        (successorIndexIso.{u, v} n).inv (ForgetEnrichment.of PointedCGWH.{u, v} d) ≫
      (circleToPowerOneIso.{u, v}.inv ▷ ((symmetricDegree.{u, v} (n + 1)) ⟶[PointedCGWH.{u, v}] d))
        ≫
      component ((Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialDegree (n + 1))).inv.app PointedCGWH.sphereOne) d := by
  exact originalStabilizationIso_inv_left_component ..

/-- The original unit-coefficient target comparison retains its full inverse component. -/
theorem sequentialSymmetricStabilizationIso_inv_right_component (n : ℕ) (d :
  PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    component (sequentialSymmetricStabilizationIso.{u, v} n).inv.right d =
      component ((Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v}
        (sequentialDegree n)).inv.app (𝟙_ PointedCGWH.{u, v})) d :=
  congrArg (fun r => component r d) (sequentialSymmetricStabilizationIso_inv_right n)

/-- The whole left map is natural in every complete enriched Hom object. -/
theorem sequentialSymmetricStabilizationIso_hom_left_naturality
    (n : ℕ) (d k : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((sequentialSymmetricProlongedStabilizationArrow.{u, v}
      n).left).toEnrichedFunctor.map d k) ≫
      component (sequentialSymmetricStabilizationIso.{u, v} n).hom.left k =
    (component (sequentialSymmetricStabilizationIso.{u, v} n).hom.left d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((symmetricOneStepStabilizationArrow.{u, v}
        n).left).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.left d k

/-- The whole right map is natural in every complete enriched Hom object. -/
theorem sequentialSymmetricStabilizationIso_hom_right_naturality
    (n : ℕ) (d k : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((sequentialSymmetricProlongedStabilizationArrow.{u, v}
      n).right).toEnrichedFunctor.map d k) ≫
      component (sequentialSymmetricStabilizationIso.{u, v} n).hom.right k =
    (component (sequentialSymmetricStabilizationIso.{u, v} n).hom.right d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((symmetricOneStepStabilizationArrow.{u, v}
        n).right).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.right d k

/-- The whole inverse left map is natural in every complete enriched Hom object. -/
theorem sequentialSymmetricStabilizationIso_inv_left_naturality
    (n : ℕ) (d k : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((symmetricOneStepStabilizationArrow.{u, v}
      n).left).toEnrichedFunctor.map d k) ≫
      component (sequentialSymmetricStabilizationIso.{u, v} n).inv.left k =
    (component (sequentialSymmetricStabilizationIso.{u, v} n).inv.left d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((sequentialSymmetricProlongedStabilizationArrow.{u, v}
        n).left).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.left d k

/-- The whole inverse right map is natural in every complete enriched Hom object. -/
theorem sequentialSymmetricStabilizationIso_inv_right_naturality
    (n : ℕ) (d k : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((symmetricOneStepStabilizationArrow.{u, v}
      n).right).toEnrichedFunctor.map d k) ≫
      component (sequentialSymmetricStabilizationIso.{u, v} n).inv.right k =
    (component (sequentialSymmetricStabilizationIso.{u, v} n).inv.right d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((sequentialSymmetricProlongedStabilizationArrow.{u, v}
        n).right).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.right d k

/-- Every full native Hom component retains the actual coefficient and target-index maps. -/
theorem sequentialOrthogonalStabilizationIso_hom_left_component (n : ℕ) (d :
  OrthogonalOperatorIndex.{u, v}) :
    component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left d =
      component ((Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialDegree (n + 1))).hom.app PointedCGWH.sphereOne) d ≫
      (sequentialOrthogonalCoefficientIso.{u, v}.hom ▷ ((OrthogonalOperatorIndex.ofIndex (n + 1))
        ⟶[PointedCGWH.{u, v}] d)) ≫
      (PointedCGWH.orthogonalSphere.{u, v} 1) ◁ eHomWhiskerRight PointedCGWH.{u, v}
        (successorOrthogonalIndexIso.{u, v} n).hom (ForgetEnrichment.of PointedCGWH.{u, v} d) := by
  exact originalStabilizationIso_hom_left_component ..

/-- The original unit-coefficient target comparison retains its full component. -/
theorem sequentialOrthogonalStabilizationIso_hom_right_component (n : ℕ) (d :
  OrthogonalOperatorIndex.{u, v}) :
    component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right d =
      component ((Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialDegree n)).hom.app (𝟙_ PointedCGWH.{u, v})) d :=
  congrArg (fun r => component r d) (sequentialOrthogonalStabilizationIso_hom_right n)

/-- The original unit-coefficient target comparison retains its full inverse component. -/
theorem sequentialOrthogonalStabilizationIso_inv_right_component (n : ℕ) (d :
  OrthogonalOperatorIndex.{u, v}) :
    component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right d =
      component ((Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (sequentialDegree n)).inv.app (𝟙_ PointedCGWH.{u, v})) d :=
  congrArg (fun r => component r d) (sequentialOrthogonalStabilizationIso_inv_right n)

/-- The whole left map is natural in every complete enriched Hom object. -/
theorem sequentialOrthogonalStabilizationIso_hom_left_naturality
    (n : ℕ) (d k : OrthogonalOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((sequentialOrthogonalProlongedStabilizationArrow.{u, v}
      n).left).toEnrichedFunctor.map d k) ≫
      component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left k =
    (component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((orthogonalOneStepStabilizationArrow.{u, v}
        n).left).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left d k

/-- The whole right map is natural in every complete enriched Hom object. -/
theorem sequentialOrthogonalStabilizationIso_hom_right_naturality
    (n : ℕ) (d k : OrthogonalOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((sequentialOrthogonalProlongedStabilizationArrow.{u, v}
      n).right).toEnrichedFunctor.map d k) ≫
      component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right k =
    (component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((orthogonalOneStepStabilizationArrow.{u, v}
        n).right).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right d k

/-- The whole inverse left map is natural in every complete enriched Hom object. -/
theorem sequentialOrthogonalStabilizationIso_inv_left_naturality
    (n : ℕ) (d k : OrthogonalOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((orthogonalOneStepStabilizationArrow.{u, v}
      n).left).toEnrichedFunctor.map d k) ≫
      component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left k =
    (component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((sequentialOrthogonalProlongedStabilizationArrow.{u, v}
        n).left).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left d k

/-- The whole inverse right map is natural in every complete enriched Hom object. -/
theorem sequentialOrthogonalStabilizationIso_inv_right_naturality
    (n : ℕ) (d k : OrthogonalOperatorIndex.{u, v}) :
    MonoidalClosed.uncurry (((orthogonalOneStepStabilizationArrow.{u, v}
      n).right).toEnrichedFunctor.map d k) ≫
      component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right k =
    (component (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right d ▷
      (d ⟶[PointedCGWH.{u, v}] k)) ≫
      MonoidalClosed.uncurry (((sequentialOrthogonalProlongedStabilizationArrow.{u, v}
        n).right).toEnrichedFunctor.map d k) := by
  simpa only [tensorHom_id] using GradedNatTrans.uncurriedNaturality
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right d k

/-- The actual free/Lan unit transports every entire original sequential Hom through both source
  maps. -/
theorem sequentialSymmetricStabilizationIso_full_component (n m : ℕ) :
    component ((leftKanRestrictionAdjunction sequentialSymmetricOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} (n + 1))
        PointedCGWH.sphereOne.{u, v})) (sequentialDegree.{u, v} m) ≫
      component (sequentialSymmetricStabilizationIso.{u, v} n).hom.left
        (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    PointedCGWH.sphereOne.{u, v} ◁ sequentialSymmetricOperatorIndexFunctor.{u, v}.map
      (sequentialDegree.{u, v} (n
      + 1)) (sequentialDegree.{u, v} m) ≫
      (circleToPowerOneIso.{u, v}.hom ▷ ((symmetricDegree.{u, v} (n + 1)) ⟶[PointedCGWH.{u, v}]
        (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)))) ≫
      (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1)) ◁ eHomWhiskerRight
        PointedCGWH.{u, v} (successorIndexIso.{u, v} n).hom
        (ForgetEnrichment.of PointedCGWH.{u, v} (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj
          (sequentialDegree.{u, v} m))) :=
  originalStabilizationIso_full_component sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) (sequentialDegree.{u, v} (n + 1))
    (PointedCGWH.symmetricOperatorObj (finiteIndex n ⊗ finiteIndex 1)) circleToPowerOneIso
      (successorIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne.{u, v} n).inv
    (Actual.symmetricNu (finiteIndex n) (finiteIndex 1)) (sequential_inclusion_factor n)
    (PointedCGWH.SequentialSpectrum.unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)
    (stabilizationFamily_stabilization_eq_unitStabilizationMap n).symm
    (sequentialDegree.{u, v} m)

/-- The actual free/Lan unit transports every entire original sequential Hom through both source
  maps. -/
theorem sequentialOrthogonalStabilizationIso_full_component (n m : ℕ) :
    component ((leftKanRestrictionAdjunction sequentialOrthogonalOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} (n + 1))
        PointedCGWH.sphereOne.{u, v})) (sequentialDegree.{u, v} m) ≫
      component (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left
        (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    PointedCGWH.sphereOne.{u, v} ◁ sequentialOrthogonalOperatorIndexFunctor.{u, v}.map
      (sequentialDegree.{u, v}
      (n + 1)) (sequentialDegree.{u, v} m) ≫
      (sequentialOrthogonalCoefficientIso.{u, v}.hom ▷ ((OrthogonalOperatorIndex.ofIndex (n + 1))
        ⟶[PointedCGWH.{u, v}] (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj
          (sequentialDegree.{u, v} m)))) ≫
      (PointedCGWH.orthogonalSphere.{u, v} 1) ◁ eHomWhiskerRight PointedCGWH.{u, v}
        (successorOrthogonalIndexIso.{u, v} n).hom
        (ForgetEnrichment.of PointedCGWH.{u, v} (sequentialOrthogonalOperatorIndexFunctor.{u,
          v}.obj (sequentialDegree.{u, v} m))) :=
  originalStabilizationIso_full_component sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) (sequentialDegree.{u, v} (n + 1))
    (OrthogonalOperatorIndex.ofIndex (n + 1)) sequentialOrthogonalCoefficientIso
      (successorOrthogonalIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne.{u, v} n).inv
    (OrthogonalOperatorIndex.nu n 1) (sequentialOrthogonal_inclusion_factor n)
    (PointedCGWH.SequentialSpectrum.unitStabilizationMap PointedCGWH.sphereOne.{u, v} n)
    (stabilizationFamily_stabilization_eq_unitStabilizationMap n).symm
    (sequentialDegree.{u, v} m)

end StabilizationHomComponents

section OriginalFreeArrows


/-- The original sequential free functor retains the entire caller coefficient arrow. -/
def sequentialFreeArrow (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    Arrow PointedCGWH.SequentialSpectrum.{u, v} := freeArrow (sequentialDegree.{u, v} n) i

/-- This is the literal original sequential free functor applied to the same whole arrow. -/
theorem sequentialFreeArrow_eq_original (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    sequentialFreeArrow.{u, v} n i =
      (CategoryTheory.Spectra.Sequential.freeAt PointedCGWH.sphereOne n).mapArrow.obj i := rfl

/-- The actual Lan of the original sequential free arrow, with both endpoints and maps. -/
def sequentialSymmetricProlongedFreeArrow (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    Arrow Actual.SymmetricCarrier.{u, v} :=
  (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow.obj (sequentialFreeArrow.{u, v}
    n i)

/-- The whole original free arrow is compared by the genuine Kan/free isomorphism. -/
def sequentialSymmetricFreeArrowIso (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    sequentialSymmetricProlongedFreeArrow.{u, v} n i ≅
      freeArrow (symmetricDegree.{u, v} n) i :=
  leftKanFreeArrowIso sequentialSymmetricOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v} n) i

/-- The forward left map is the actual free Kan comparison on the original left coefficient. -/
theorem sequentialSymmetricFreeArrowIso_hom_left (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeArrowIso.{u, v} n i).hom.left =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).hom.app i.left :=
  leftKanFreeArrowIso_hom_left ..

/-- The forward right map is the actual free Kan comparison on the original right coefficient. -/
theorem sequentialSymmetricFreeArrowIso_hom_right (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeArrowIso.{u, v} n i).hom.right =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).hom.app i.right :=
  leftKanFreeArrowIso_hom_right ..

/-- The inverse left map retains the original inverse free Kan comparison. -/
theorem sequentialSymmetricFreeArrowIso_inv_left (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeArrowIso.{u, v} n i).inv.left =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).inv.app i.left :=
  leftKanFreeArrowIso_inv_left ..

/-- The inverse right map retains the original inverse free Kan comparison. -/
theorem sequentialSymmetricFreeArrowIso_inv_right (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialSymmetricFreeArrowIso.{u, v} n i).inv.right =
      (Kan.leftKanFreeIso sequentialSymmetricOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).inv.app i.right :=
  leftKanFreeArrowIso_inv_right ..

/-- Every original coefficient-arrow morphism satisfies the complete forward naturality square. -/
theorem sequentialSymmetricFreeArrowIso_naturality (n : ℕ)
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow.map
        ((Free.functor (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n)).mapArrow.map h) ≫
      (sequentialSymmetricFreeArrowIso.{u, v} n k).hom =
    (sequentialSymmetricFreeArrowIso.{u, v} n i).hom ≫
      (Free.functor (V := PointedCGWH.{u, v}) (symmetricDegree.{u, v} n)).mapArrow.map h :=
  leftKanFreeArrowIso_naturality sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) h

/-- Every original coefficient-arrow morphism satisfies the complete inverse naturality square. -/
theorem sequentialSymmetricFreeArrowIso_inv_naturality (n : ℕ)
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (Free.functor (V := PointedCGWH.{u, v}) (symmetricDegree.{u, v} n)).mapArrow.map h ≫
      (sequentialSymmetricFreeArrowIso.{u, v} n k).inv =
    (sequentialSymmetricFreeArrowIso.{u, v} n i).inv ≫
      (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow.map
        ((Free.functor (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n)).mapArrow.map h) :=
  leftKanFreeArrowIso_inv_naturality sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) h

/-- The complete original free-arrow functors commute with prolongation naturally in every arrow. -/
def sequentialSymmetricFreeArrowNatIso (n : ℕ) :
    (Free.functor (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n)).mapArrow ⋙
      (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow ≅
    (Free.functor (V := PointedCGWH.{u, v}) (symmetricDegree.{u, v} n)).mapArrow :=
  leftKanFreeArrowNatIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n)

/-- Every original realized boundary is transported with its full free source and target. -/
def sequentialSymmetricFreeBoundaryIso (n m : ℕ) :
    sequentialSymmetricProlongedFreeArrow.{u, v} n (Arrow.mk (NativeK.boundaryMap m)) ≅
      freeArrow (symmetricDegree.{u, v} n) (Arrow.mk (NativeK.boundaryMap m)) :=
  sequentialSymmetricFreeArrowIso.{u, v} n (Arrow.mk (NativeK.boundaryMap m))

/-- Every original realized horn, in every dimension and at every label, is transported whole. -/
def sequentialSymmetricFreeHornIso (n m : ℕ) (i : Fin (m + 2)) :
    sequentialSymmetricProlongedFreeArrow.{u, v} n (originalHornArrow m i) ≅
      freeArrow (symmetricDegree.{u, v} n) (originalHornArrow m i) :=
  sequentialSymmetricFreeArrowIso.{u, v} n (originalHornArrow m i)

/-- The actual Lan of the original sequential free arrow, with both endpoints and maps. -/
def sequentialOrthogonalProlongedFreeArrow (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    Arrow Actual.OrthogonalCarrier.{u, v} :=
  (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow.obj (sequentialFreeArrow.{u,
    v} n i)

/-- The whole original free arrow is compared by the genuine Kan/free isomorphism. -/
def sequentialOrthogonalFreeArrowIso (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    sequentialOrthogonalProlongedFreeArrow.{u, v} n i ≅
      freeArrow (OrthogonalOperatorIndex.ofIndex n) i :=
  leftKanFreeArrowIso sequentialOrthogonalOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v} n) i

/-- The forward left map is the actual free Kan comparison on the original left coefficient. -/
theorem sequentialOrthogonalFreeArrowIso_hom_left (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).hom.left =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).hom.app i.left :=
  leftKanFreeArrowIso_hom_left ..

/-- The forward right map is the actual free Kan comparison on the original right coefficient. -/
theorem sequentialOrthogonalFreeArrowIso_hom_right (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).hom.right =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).hom.app i.right :=
  leftKanFreeArrowIso_hom_right ..

/-- The inverse left map retains the original inverse free Kan comparison. -/
theorem sequentialOrthogonalFreeArrowIso_inv_left (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).inv.left =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).inv.app i.left :=
  leftKanFreeArrowIso_inv_left ..

/-- The inverse right map retains the original inverse free Kan comparison. -/
theorem sequentialOrthogonalFreeArrowIso_inv_right (n : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).inv.right =
      (Kan.leftKanFreeIso sequentialOrthogonalOperatorIndexFunctor.{u, v} (sequentialDegree.{u, v}
        n)).inv.app i.right :=
  leftKanFreeArrowIso_inv_right ..

/-- Every original coefficient-arrow morphism satisfies the complete forward naturality square. -/
theorem sequentialOrthogonalFreeArrowIso_naturality (n : ℕ)
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow.map
        ((Free.functor (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n)).mapArrow.map h) ≫
      (sequentialOrthogonalFreeArrowIso.{u, v} n k).hom =
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).hom ≫
      (Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex n)).mapArrow.map h :=
  leftKanFreeArrowIso_naturality sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) h

/-- Every original coefficient-arrow morphism satisfies the complete inverse naturality square. -/
theorem sequentialOrthogonalFreeArrowIso_inv_naturality (n : ℕ)
    {i k : Arrow PointedCGWH.{u, v}} (h : i ⟶ k) :
    (Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex n)).mapArrow.map h ≫
      (sequentialOrthogonalFreeArrowIso.{u, v} n k).inv =
    (sequentialOrthogonalFreeArrowIso.{u, v} n i).inv ≫
      (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow.map
        ((CategoryTheory.Spectra.Sequential.freeAt PointedCGWH.sphereOne.{u, v} n).mapArrow.map h) := by
  let e : (CategoryTheory.Spectra.Sequential.freeAt PointedCGWH.sphereOne.{u, v} n).mapArrow ⋙
        (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow ≅
      (Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex n)).mapArrow :=
    leftKanFreeArrowNatIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
      (sequentialDegree.{u, v} n)
  exact e.inv.naturality h

/-- The complete original free-arrow functors commute with prolongation naturally in every arrow. -/
def sequentialOrthogonalFreeArrowNatIso (n : ℕ) :
    (Free.functor (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n)).mapArrow ⋙
      (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow ≅
    (Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex n)).mapArrow :=
  leftKanFreeArrowNatIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n)

/-- Every original realized boundary is transported with its full free source and target. -/
def sequentialOrthogonalFreeBoundaryIso (n m : ℕ) :
    sequentialOrthogonalProlongedFreeArrow.{u, v} n (Arrow.mk (NativeK.boundaryMap m)) ≅
      freeArrow (OrthogonalOperatorIndex.ofIndex n) (Arrow.mk (NativeK.boundaryMap m)) :=
  sequentialOrthogonalFreeArrowIso.{u, v} n (Arrow.mk (NativeK.boundaryMap m))

/-- Every original realized horn, in every dimension and at every label, is transported whole. -/
def sequentialOrthogonalFreeHornIso (n m : ℕ) (i : Fin (m + 2)) :
    sequentialOrthogonalProlongedFreeArrow.{u, v} n (originalHornArrow m i) ≅
      freeArrow (OrthogonalOperatorIndex.ofIndex n) (originalHornArrow m i) :=
  sequentialOrthogonalFreeArrowIso.{u, v} n (originalHornArrow m i)

/-- Every native symmetric index object is the actual image of an original sequential degree. -/
theorem sequentialSymmetric_obj_surjective :
    Function.Surjective sequentialSymmetricOperatorIndexFunctor.{u, v}.obj := by
  intro b
  let a : Operad.SmallFinBijGroupoid := b.asIndex
  refine ⟨sequentialDegree.{u, v} a.of.len, ?_⟩
  cases b
  rfl

/-- The actual direct composite reaches every original orthogonal operator object. -/
theorem sequentialOrthogonal_obj_surjective :
    Function.Surjective sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj :=
  symmetricOrthogonal_obj_surjective.comp sequentialSymmetric_obj_surjective

/-- Actual Kan image identifies every original full free-I member up to whole arrow isomorphism. -/
theorem sequentialSymmetric_levelI_image :
    leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
      (NativeK.levelI (I := PointedCGWH.Spectra.Sequential.Index.{u, v})) =
    (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure sequentialSymmetricOperatorIndexFunctor.{u, v}
    sequentialSymmetric_obj_surjective PointedCGWH.realizedBoundaryInclusions

/-- Actual Kan image identifies every original full free-J member up to whole arrow isomorphism. -/
theorem sequentialSymmetric_levelJ_image :
    leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
      (NativeK.levelJ (I := PointedCGWH.Spectra.Sequential.Index.{u, v})) =
    (NativeK.levelJ (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure sequentialSymmetricOperatorIndexFunctor.{u, v}
    sequentialSymmetric_obj_surjective PointedCGWH.realizedHornInclusions

/-- Actual Kan image identifies every original full free-I member up to whole arrow isomorphism. -/
theorem sequentialOrthogonal_levelI_image :
    leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
      (NativeK.levelI (I := PointedCGWH.Spectra.Sequential.Index.{u, v})) =
    (NativeK.levelI (I := OrthogonalOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure sequentialOrthogonalOperatorIndexFunctor.{u, v}
    sequentialOrthogonal_obj_surjective PointedCGWH.realizedBoundaryInclusions

/-- Actual Kan image identifies every original full free-J member up to whole arrow isomorphism. -/
theorem sequentialOrthogonal_levelJ_image :
    leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
      (NativeK.levelJ (I := PointedCGWH.Spectra.Sequential.Index.{u, v})) =
    (NativeK.levelJ (I := OrthogonalOperatorIndex.{u, v})).isoClosure :=
  leftKan_generators_eq_isoClosure sequentialOrthogonalOperatorIndexFunctor.{u, v}
    sequentialOrthogonal_obj_surjective PointedCGWH.realizedHornInclusions

/-- Every full original Hom acts through the actual free Kan unit at the original left coefficient.
-/
theorem sequentialSymmetricFreeArrowIso_left_full_component
    (n m : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    component ((leftKanRestrictionAdjunction sequentialSymmetricOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n) i.left))
        (sequentialDegree.{u, v} m) ≫
      component (sequentialSymmetricFreeArrowIso.{u, v} n i).hom.left
        (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    i.left ◁ sequentialSymmetricOperatorIndexFunctor.{u, v}.map (sequentialDegree.{u, v} n)
      (sequentialDegree.{u, v} m) :=
  leftKanFreeArrowIso_left_full_component sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) i (sequentialDegree.{u, v} m)

/-- Every full original Hom acts through the actual free Kan unit at the original right
  coefficient. -/
theorem sequentialSymmetricFreeArrowIso_right_full_component
    (n m : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    component ((leftKanRestrictionAdjunction sequentialSymmetricOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n) i.right))
        (sequentialDegree.{u, v} m) ≫
      component (sequentialSymmetricFreeArrowIso.{u, v} n i).hom.right
        (sequentialSymmetricOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    i.right ◁ sequentialSymmetricOperatorIndexFunctor.{u, v}.map (sequentialDegree.{u, v} n)
      (sequentialDegree.{u, v} m) :=
  leftKanFreeArrowIso_right_full_component sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) i (sequentialDegree.{u, v} m)

/-- Every full original Hom acts through the actual free Kan unit at the original left coefficient.
-/
theorem sequentialOrthogonalFreeArrowIso_left_full_component
    (n m : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    component ((leftKanRestrictionAdjunction sequentialOrthogonalOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n) i.left))
        (sequentialDegree.{u, v} m) ≫
      component (sequentialOrthogonalFreeArrowIso.{u, v} n i).hom.left
        (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    i.left ◁ sequentialOrthogonalOperatorIndexFunctor.{u, v}.map (sequentialDegree.{u, v} n)
      (sequentialDegree.{u, v} m) :=
  leftKanFreeArrowIso_left_full_component sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) i (sequentialDegree.{u, v} m)

/-- Every full original Hom acts through the actual free Kan unit at the original right
  coefficient. -/
theorem sequentialOrthogonalFreeArrowIso_right_full_component
    (n m : ℕ) (i : Arrow PointedCGWH.{u, v}) :
    component ((leftKanRestrictionAdjunction sequentialOrthogonalOperatorIndexFunctor.{u,
      v}).unit.app
      (Free.object (V := PointedCGWH.{u, v}) (sequentialDegree.{u, v} n) i.right))
        (sequentialDegree.{u, v} m) ≫
      component (sequentialOrthogonalFreeArrowIso.{u, v} n i).hom.right
        (sequentialOrthogonalOperatorIndexFunctor.{u, v}.obj (sequentialDegree.{u, v} m)) =
    i.right ◁ sequentialOrthogonalOperatorIndexFunctor.{u, v}.map (sequentialDegree.{u, v} n)
      (sequentialDegree.{u, v} m) :=
  leftKanFreeArrowIso_right_full_component sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialDegree.{u, v} n) i (sequentialDegree.{u, v} m)

end OriginalFreeArrows

section OriginalKImages

/-- Every literal original paired sequential generator maps into the unchanged full native family.
-/
theorem sequentialSymmetric_additionalGenerators_image_le :
    leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
      PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v} ≤
    (NativeK.additionalGenerators Actual.symmetricFamily.{u, v}).isoClosure := by
  apply (MorphismProperty.map_le_iff
    PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v}
      (NativeK.additionalGenerators Actual.symmetricFamily.{u, v}).isoClosure).mpr
  intro X Y f hf
  rcases hf with ⟨⟨n, m⟩⟩
  exact ⟨_, _, NativeK.generatorMap Actual.symmetricFamily.{u, v} (finiteIndex n, finiteIndex 1) m,
    NativeK.generatorMap_mem Actual.symmetricFamily (finiteIndex n, finiteIndex 1) m,
      ⟨(sequentialSymmetricGeneratorIso.{u, v} n m).symm⟩⟩

/-- The complete original sequential K family maps into the full unchanged target K family. -/
theorem sequentialSymmetric_K_image_le :
    leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
      PointedCGWH.SequentialSpectrum.StableK.generators.{u, v} ≤
    Actual.symmetricK.{u, v}.isoClosure := by
  apply (MorphismProperty.map_le_iff
    PointedCGWH.SequentialSpectrum.StableK.generators.{u, v}
      Actual.symmetricK.{u, v}.isoClosure).mpr
  intro X Y f hf
  rcases (PointedCGWH.SequentialSpectrum.StableK.generators_iff f).mp hf with hJ | hG
  · have hmem : leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
        (NativeK.levelJ (I := PointedCGWH.Spectra.Sequential.Index.{u, v}))
          ((leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map f) :=
      MorphismProperty.map_mem_map _ _ _ hJ
    have htarget := leftKan_generators_le sequentialSymmetricOperatorIndexFunctor.{u, v}
      PointedCGWH.realizedHornInclusions _ hmem
    exact MorphismProperty.monotone_isoClosure (show NativeK.levelJ ≤ Actual.symmetricK.{u, v} from
      le_sup_left) _ htarget
  · have hmem : leftKanImage sequentialSymmetricOperatorIndexFunctor.{u, v}
        PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v}
          ((leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map f) :=
      MorphismProperty.map_mem_map _ _ _ hG
    have htarget := sequentialSymmetric_additionalGenerators_image_le.{u, v} _ hmem
    exact MorphismProperty.monotone_isoClosure
      (show NativeK.additionalGenerators Actual.symmetricFamily.{u, v} ≤ Actual.symmetricK.{u, v}
        from
        le_sup_right) _ htarget

/-- Every literal original paired sequential generator maps into the unchanged full native family.
-/
theorem sequentialOrthogonal_additionalGenerators_image_le :
    leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
      PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v} ≤
    (NativeK.additionalGenerators Actual.orthogonalFamily.{u, v}).isoClosure := by
  apply (MorphismProperty.map_le_iff
    PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v}
      (NativeK.additionalGenerators Actual.orthogonalFamily.{u, v}).isoClosure).mpr
  intro X Y f hf
  rcases hf with ⟨⟨n, m⟩⟩
  exact ⟨_, _, NativeK.generatorMap Actual.orthogonalFamily.{u, v} (n, 1) m,
    NativeK.generatorMap_mem Actual.orthogonalFamily (n, 1) m,
      ⟨(sequentialOrthogonalGeneratorIso.{u, v} n m).symm⟩⟩

/-- The complete original sequential K family maps into the full unchanged target K family. -/
theorem sequentialOrthogonal_K_image_le :
    leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
      PointedCGWH.SequentialSpectrum.StableK.generators.{u, v} ≤
    Actual.orthogonalK.{u, v}.isoClosure := by
  apply (MorphismProperty.map_le_iff
    PointedCGWH.SequentialSpectrum.StableK.generators.{u, v}
      Actual.orthogonalK.{u, v}.isoClosure).mpr
  intro X Y f hf
  rcases (PointedCGWH.SequentialSpectrum.StableK.generators_iff f).mp hf with hJ | hG
  · have hmem : leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
        (NativeK.levelJ (I := PointedCGWH.Spectra.Sequential.Index.{u, v}))
          ((leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map f) :=
      MorphismProperty.map_mem_map _ _ _ hJ
    have htarget := leftKan_generators_le sequentialOrthogonalOperatorIndexFunctor.{u, v}
      PointedCGWH.realizedHornInclusions _ hmem
    exact MorphismProperty.monotone_isoClosure (show NativeK.levelJ ≤ Actual.orthogonalK.{u, v} from
      le_sup_left) _ htarget
  · have hmem : leftKanImage sequentialOrthogonalOperatorIndexFunctor.{u, v}
        PointedCGWH.SequentialSpectrum.StableK.additionalGenerators.{u, v}
          ((leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map f) :=
      MorphismProperty.map_mem_map _ _ _ hG
    have htarget := sequentialOrthogonal_additionalGenerators_image_le.{u, v} _ hmem
    exact MorphismProperty.monotone_isoClosure
      (show NativeK.additionalGenerators Actual.orthogonalFamily.{u, v} ≤ Actual.orthogonalK.{u, v}
        from
        le_sup_right) _ htarget

end OriginalKImages

section OriginalCylinders


/-- The cylinder object is the literal original sequential stabilization cylinder. -/
theorem sequentialCylinderObject_eq_original (n : ℕ) :
    PointedCGWH.EnrichedIntervalMappingCylinder.object (sequentialStabilizationArrow.{u, v} n) =
      PointedCGWH.SequentialSpectrum.stabilizationCylinder n := rfl

/-- The second-endpoint source is the literal original sequential stabilization source. -/
theorem sequentialCylinderSource_eq_original (n : ℕ) :
    PointedCGWH.EnrichedIntervalMappingCylinder.source (sequentialStabilizationArrow.{u, v} n) =
      PointedCGWH.SequentialSpectrum.stabilizationCylinderSource n := rfl

/-- The retraction is the same original sequential stabilization retraction. -/
theorem sequentialCylinderRetraction_eq_original (n : ℕ) :
    PointedCGWH.EnrichedIntervalMappingCylinder.retraction (sequentialStabilizationArrow.{u, v} n) =
      PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n := rfl

/-- The full original interval leg retains the genuine Kan tensor and complete source map. -/
theorem sequentialSymmetricCylinder_intervalLeg (n : ℕ) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg (sequentialStabilizationArrow.{u, v}
      n)) ≫ (sequentialSymmetricCylinderIso.{u, v} n).hom =
    (leftKanTensorIso sequentialSymmetricOperatorIndexFunctor.{u, v}
      PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).hom ≫
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval
        (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
        (symmetricOneStepStabilizationArrow.{u, v} n) :=
  CylinderTransport.intervalLeg_throughIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- The complete original target leg retains the actual free Kan target map. -/
theorem sequentialSymmetricCylinder_targetLeg (n : ℕ) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (sequentialStabilizationArrow.{u, v}
      n)) ≫ (sequentialSymmetricCylinderIso.{u, v} n).hom =
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.right ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (symmetricOneStepStabilizationArrow.{u,
      v} n) :=
  CylinderTransport.targetLeg_throughIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- Both literal native interval endpoints are transported with the complete source map. -/
theorem sequentialSymmetricCylinder_endpoint (n : ℕ) (i : Fin 2) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i (sequentialStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (sequentialStabilizationArrow.{u, v} n)) ≫
      (sequentialSymmetricCylinderIso.{u, v} n).hom =
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫
      PointedCGWH.EnrichedIntervalCylinder.inclusion i (symmetricOneStepStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (symmetricOneStepStabilizationArrow.{u, v} n) :=
  CylinderTransport.endpoint_throughIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n) i

/-- Both literal native interval endpoints retain the entire inverse source map. -/
theorem sequentialSymmetricCylinder_endpoint_inv (n : ℕ) (i : Fin 2) :
    (PointedCGWH.EnrichedIntervalCylinder.inclusion i (symmetricOneStepStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (symmetricOneStepStabilizationArrow.{u, v} n)) ≫ (sequentialSymmetricCylinderIso.{u, v}
      n).inv =
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.left ≫ (leftKan
      sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i (sequentialStabilizationArrow.{u, v}
        n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
        (sequentialStabilizationArrow.{u, v} n)) :=
  CylinderTransport.endpoint_throughIso_inv sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n) i

/-- The original zero endpoint is the actual original stabilization followed by its target leg. -/
theorem sequentialSymmetricCylinder_endpoint_zero (n : ℕ) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (sequentialStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (sequentialStabilizationArrow.{u, v} n)) ≫
      (sequentialSymmetricCylinderIso.{u, v} n).hom =
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫
      (symmetricOneStepStabilizationArrow.{u, v} n).hom ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (symmetricOneStepStabilizationArrow.{u,
      v} n) :=
  (sequentialSymmetricCylinder_endpoint n 0).trans
    (congrArg (fun r => (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫ r)
      (pushout.condition (f := PointedCGWH.EnrichedIntervalCylinder.inclusion 0
        (symmetricOneStepStabilizationArrow.{u, v} n).left) (g :=
        (symmetricOneStepStabilizationArrow.{u, v} n).hom)))

/-- The literal original second-endpoint source is transported as a whole map. -/
theorem sequentialSymmetricCylinder_source (n : ℕ) :
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderSource n) ≫
      (sequentialSymmetricCylinderIso.{u, v} n).hom =
    (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.source (symmetricOneStepStabilizationArrow.{u, v}
      n) :=
  CylinderTransport.source_throughIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- The literal second endpoint is recovered by the original complete inverse source map. -/
theorem sequentialSymmetricCylinder_source_inv (n : ℕ) :
    PointedCGWH.EnrichedIntervalMappingCylinder.source (symmetricOneStepStabilizationArrow.{u, v}
      n) ≫ (sequentialSymmetricCylinderIso.{u, v} n).inv =
    (sequentialSymmetricStabilizationIso.{u, v} n).inv.left ≫ (leftKan
      sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderSource n) :=
  CylinderTransport.endpoint_throughIso_inv sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n) 1

/-- The actual interval contraction is retained by the whole tensor/source comparison. -/
theorem sequentialSymmetricCylinder_projection (n : ℕ) :
    (leftKanTensorIso sequentialSymmetricOperatorIndexFunctor.{u, v}
      PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).hom ≫
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval
        (sequentialSymmetricStabilizationIso.{u, v} n).hom.left ≫
        PointedCGWH.EnrichedIntervalCylinder.projection (symmetricOneStepStabilizationArrow.{u, v}
        n).left =
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.projection (sequentialStabilizationArrow.{u, v}
      n).left) ≫ (sequentialSymmetricStabilizationIso.{u, v} n).hom.left :=
  CylinderTransport.projection_throughIso sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- The inverse tensor/source comparison retains the original interval contraction. -/
theorem sequentialSymmetricCylinder_projection_inv (n : ℕ) :
    tensorLeftMap PointedCGWH.IntervalCoefficient.interval (sequentialSymmetricStabilizationIso.{u,
      v} n).inv.left ≫
      (leftKanTensorIso sequentialSymmetricOperatorIndexFunctor.{u, v}
        PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).inv ≫
      (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
        (PointedCGWH.EnrichedIntervalCylinder.projection (sequentialStabilizationArrow.{u, v}
        n).left) =
    PointedCGWH.EnrichedIntervalCylinder.projection (symmetricOneStepStabilizationArrow.{u, v}
      n).left ≫ (sequentialSymmetricStabilizationIso.{u, v} n).inv.left :=
  CylinderTransport.projection_throughIso_inv sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- The original mapping-cylinder retraction retains the complete forward target map. -/
theorem sequentialSymmetricCylinder_retraction (n : ℕ) :
    (sequentialSymmetricCylinderIso.{u, v} n).hom ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction
      (symmetricOneStepStabilizationArrow.{u, v} n) =
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n) ≫
      (sequentialSymmetricStabilizationIso.{u, v} n).hom.right :=
  CylinderTransport.throughIso_retraction sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- The entire inverse cylinder comparison recovers the same original retraction. -/
theorem sequentialSymmetricCylinder_retraction_inv (n : ℕ) :
    (sequentialSymmetricCylinderIso.{u, v} n).inv ≫ (leftKan
      sequentialSymmetricOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n) =
    PointedCGWH.EnrichedIntervalMappingCylinder.retraction (symmetricOneStepStabilizationArrow.{u,
      v} n) ≫ (sequentialSymmetricStabilizationIso.{u, v} n).inv.right :=
  CylinderTransport.throughIso_retraction_inv sequentialSymmetricOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialSymmetricStabilizationIso.{u, v} n)

/-- Every whole original Arrow morphism has the actual natural Kan mapping-cylinder comparison. -/
def sequentialSymmetricCylinderNatIso :
    PointedCGWH.EnrichedIntervalMappingCylinder.functor (I :=
      PointedCGWH.Spectra.Sequential.Index.{u, v}) ⋙ leftKan
      sequentialSymmetricOperatorIndexFunctor.{u, v} ≅
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow ⋙
      PointedCGWH.EnrichedIntervalMappingCylinder.functor (I :=
      PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  CylinderTransport.leftKanNatIso sequentialSymmetricOperatorIndexFunctor.{u, v}

/-- Original scalar Leibniz transport is natural in every entire original diagram arrow. -/
def sequentialSymmetricScalarNatIso (i : Arrow PointedCGWH.{u, v}) :
    ScalarTransport.diagramFunctor (C := PointedCGWH.Spectra.Sequential.Index.{u, v}) i ⋙
      (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow ≅
    (leftKan sequentialSymmetricOperatorIndexFunctor.{u, v}).mapArrow ⋙
      ScalarTransport.diagramFunctor (C := PointedCGWH.SymmetricOperatorIndex.{u, v}) i :=
  ScalarTransport.leftKanNatIso sequentialSymmetricOperatorIndexFunctor.{u, v} i

/-- Original scalar Leibniz transport is natural in every entire original scalar arrow. -/
def sequentialSymmetricScalarCoefficientNatIso
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    ScalarTransport.scalarFunctor f ⋙ (leftKan sequentialSymmetricOperatorIndexFunctor.{u,
      v}).mapArrow ≅
      ScalarTransport.scalarFunctor ((leftKan sequentialSymmetricOperatorIndexFunctor.{u,
        v}).mapArrow.obj f) :=
  ScalarTransport.leftKanScalarNatIso sequentialSymmetricOperatorIndexFunctor.{u, v} f

/-- The full original interval leg retains the genuine Kan tensor and complete source map. -/
theorem sequentialOrthogonalCylinder_intervalLeg (n : ℕ) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg (sequentialStabilizationArrow.{u, v}
      n)) ≫ (sequentialOrthogonalCylinderIso.{u, v} n).hom =
    (leftKanTensorIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
      PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).hom ≫
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval
        (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫
        PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
        (orthogonalOneStepStabilizationArrow.{u, v} n) :=
  CylinderTransport.intervalLeg_throughIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- The complete original target leg retains the actual free Kan target map. -/
theorem sequentialOrthogonalCylinder_targetLeg (n : ℕ) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg (sequentialStabilizationArrow.{u, v}
      n)) ≫ (sequentialOrthogonalCylinderIso.{u, v} n).hom =
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg
      (orthogonalOneStepStabilizationArrow.{u, v} n) :=
  CylinderTransport.targetLeg_throughIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- Both literal native interval endpoints are transported with the complete source map. -/
theorem sequentialOrthogonalCylinder_endpoint (n : ℕ) (i : Fin 2) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i (sequentialStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (sequentialStabilizationArrow.{u, v} n)) ≫
      (sequentialOrthogonalCylinderIso.{u, v} n).hom =
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫
      PointedCGWH.EnrichedIntervalCylinder.inclusion i (orthogonalOneStepStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (orthogonalOneStepStabilizationArrow.{u, v} n) :=
  CylinderTransport.endpoint_throughIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n) i

/-- Both literal native interval endpoints retain the entire inverse source map. -/
theorem sequentialOrthogonalCylinder_endpoint_inv (n : ℕ) (i : Fin 2) :
    (PointedCGWH.EnrichedIntervalCylinder.inclusion i (orthogonalOneStepStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (orthogonalOneStepStabilizationArrow.{u, v} n)) ≫ (sequentialOrthogonalCylinderIso.{u, v}
      n).inv =
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left ≫ (leftKan
      sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion i (sequentialStabilizationArrow.{u, v}
        n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
        (sequentialStabilizationArrow.{u, v} n)) :=
  CylinderTransport.endpoint_throughIso_inv sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n) i

/-- The original zero endpoint is the actual original stabilization followed by its target leg. -/
theorem sequentialOrthogonalCylinder_endpoint_zero (n : ℕ) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (sequentialStabilizationArrow.{u, v}
      n).left ≫ PointedCGWH.EnrichedIntervalMappingCylinder.intervalLeg
      (sequentialStabilizationArrow.{u, v} n)) ≫
      (sequentialOrthogonalCylinderIso.{u, v} n).hom =
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫
      (orthogonalOneStepStabilizationArrow.{u, v} n).hom ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.targetLeg
      (orthogonalOneStepStabilizationArrow.{u, v} n) :=
  (sequentialOrthogonalCylinder_endpoint n 0).trans
    (congrArg (fun r => (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫ r)
      (pushout.condition (f := PointedCGWH.EnrichedIntervalCylinder.inclusion 0
        (orthogonalOneStepStabilizationArrow.{u, v} n).left) (g :=
        (orthogonalOneStepStabilizationArrow.{u, v} n).hom)))

/-- The literal original second-endpoint source is transported as a whole map. -/
theorem sequentialOrthogonalCylinder_source (n : ℕ) :
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderSource n) ≫
      (sequentialOrthogonalCylinderIso.{u, v} n).hom =
    (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.source (orthogonalOneStepStabilizationArrow.{u,
      v} n) :=
  CylinderTransport.source_throughIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- The literal second endpoint is recovered by the original complete inverse source map. -/
theorem sequentialOrthogonalCylinder_source_inv (n : ℕ) :
    PointedCGWH.EnrichedIntervalMappingCylinder.source (orthogonalOneStepStabilizationArrow.{u, v}
      n) ≫ (sequentialOrthogonalCylinderIso.{u, v} n).inv =
    (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left ≫ (leftKan
      sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderSource n) :=
  CylinderTransport.endpoint_throughIso_inv sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n) 1

/-- The actual interval contraction is retained by the whole tensor/source comparison. -/
theorem sequentialOrthogonalCylinder_projection (n : ℕ) :
    (leftKanTensorIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
      PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).hom ≫
      tensorLeftMap PointedCGWH.IntervalCoefficient.interval
        (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left ≫
        PointedCGWH.EnrichedIntervalCylinder.projection (orthogonalOneStepStabilizationArrow.{u, v}
        n).left =
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.EnrichedIntervalCylinder.projection (sequentialStabilizationArrow.{u, v}
      n).left) ≫ (sequentialOrthogonalStabilizationIso.{u, v} n).hom.left :=
  CylinderTransport.projection_throughIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- The inverse tensor/source comparison retains the original interval contraction. -/
theorem sequentialOrthogonalCylinder_projection_inv (n : ℕ) :
    tensorLeftMap PointedCGWH.IntervalCoefficient.interval
      (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left ≫
      (leftKanTensorIso sequentialOrthogonalOperatorIndexFunctor.{u, v}
        PointedCGWH.IntervalCoefficient.interval (sequentialStabilizationArrow.{u, v} n).left).inv ≫
      (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
        (PointedCGWH.EnrichedIntervalCylinder.projection (sequentialStabilizationArrow.{u, v}
        n).left) =
    PointedCGWH.EnrichedIntervalCylinder.projection (orthogonalOneStepStabilizationArrow.{u, v}
      n).left ≫ (sequentialOrthogonalStabilizationIso.{u, v} n).inv.left :=
  CylinderTransport.projection_throughIso_inv sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- The original mapping-cylinder retraction retains the complete forward target map. -/
theorem sequentialOrthogonalCylinder_retraction (n : ℕ) :
    (sequentialOrthogonalCylinderIso.{u, v} n).hom ≫
      PointedCGWH.EnrichedIntervalMappingCylinder.retraction
      (orthogonalOneStepStabilizationArrow.{u, v} n) =
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n) ≫
      (sequentialOrthogonalStabilizationIso.{u, v} n).hom.right :=
  CylinderTransport.throughIso_retraction sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- The entire inverse cylinder comparison recovers the same original retraction. -/
theorem sequentialOrthogonalCylinder_retraction_inv (n : ℕ) :
    (sequentialOrthogonalCylinderIso.{u, v} n).inv ≫ (leftKan
      sequentialOrthogonalOperatorIndexFunctor.{u, v}).map
      (PointedCGWH.SequentialSpectrum.stabilizationCylinderRetraction n) =
    PointedCGWH.EnrichedIntervalMappingCylinder.retraction (orthogonalOneStepStabilizationArrow.{u,
      v} n) ≫ (sequentialOrthogonalStabilizationIso.{u, v} n).inv.right :=
  CylinderTransport.throughIso_retraction_inv sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (sequentialStabilizationArrow.{u, v} n) (sequentialOrthogonalStabilizationIso.{u, v} n)

/-- Every whole original Arrow morphism has the actual natural Kan mapping-cylinder comparison. -/
def sequentialOrthogonalCylinderNatIso :
    PointedCGWH.EnrichedIntervalMappingCylinder.functor (I :=
      PointedCGWH.Spectra.Sequential.Index.{u, v}) ⋙ leftKan
      sequentialOrthogonalOperatorIndexFunctor.{u, v} ≅
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow ⋙
      PointedCGWH.EnrichedIntervalMappingCylinder.functor (I := OrthogonalOperatorIndex.{u, v}) :=
  CylinderTransport.leftKanNatIso sequentialOrthogonalOperatorIndexFunctor.{u, v}

/-- Original scalar Leibniz transport is natural in every entire original diagram arrow. -/
def sequentialOrthogonalScalarNatIso (i : Arrow PointedCGWH.{u, v}) :
    ScalarTransport.diagramFunctor (C := PointedCGWH.Spectra.Sequential.Index.{u, v}) i ⋙
      (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow ≅
    (leftKan sequentialOrthogonalOperatorIndexFunctor.{u, v}).mapArrow ⋙
      ScalarTransport.diagramFunctor (C := OrthogonalOperatorIndex.{u, v}) i :=
  ScalarTransport.leftKanNatIso sequentialOrthogonalOperatorIndexFunctor.{u, v} i

/-- Original scalar Leibniz transport is natural in every entire original scalar arrow. -/
def sequentialOrthogonalScalarCoefficientNatIso
    (f : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    ScalarTransport.scalarFunctor f ⋙ (leftKan sequentialOrthogonalOperatorIndexFunctor.{u,
      v}).mapArrow ≅
      ScalarTransport.scalarFunctor ((leftKan sequentialOrthogonalOperatorIndexFunctor.{u,
        v}).mapArrow.obj f) :=
  ScalarTransport.leftKanScalarNatIso sequentialOrthogonalOperatorIndexFunctor.{u, v} f

end OriginalCylinders

end HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
