/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKPuppeHom
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StrictFiber
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberHomSequence

/-!
# Original native chosen-fiber and Q-cofiber maps

The original native zero, arbitrary chosen fiber cones, both projections,
realized-generator cardinal and caller's bottom are retained. The original
I replacement and cone give the actual suspended-fiber to Q-cofiber
comparison on every K-right arrow. Its complete Arrow naturality uses
the constructed weak corner-resolution and cofiber zigzags.

The scalar sphere adjunction also constructs the original fiber map
to the scalar loop of this same cofiber and retains its Arrow naturality.
Omega-test equivalence of these maps requires the native spectrum
successor and source-shift comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberComparison

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory
attribute [local instance] Native.allObjectsFibrant Replacement.isCofibrant_cofibrantReplacement

private instance originalJFactorization :
    MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations (D (I := I))) (fibrations (D (I := I))) :=
  (Native.functorialFactorizations (B := B) (A := I)).2

omit B in
private instance nativeZero : HasZeroObject (D (I := I)) := Diagrams.nativeHasZeroObject

local notation "Q" => Replacement.cofibrantReplacement (B := B) (A := I)
local notation "ε" => Replacement.cofibrantReplacementCounit (B := B) (A := I)
local notation "cone" => OriginalICone.cone (B := B) (I := I)
local notation "ι" => OriginalICone.inclusion (B := B) (I := I)
local notation "c" => OriginalISuspension.cocone (B := B) (I := I)
local notation "hc" => OriginalISuspension.coconeIsColimit (B := B) (I := I)
local notation "H" => toHomotopyCategory (D (I := I))
local notation "P" => OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := D (I := I))

private theorem coneCollapse_weak (X : D (I := I)) :
    weakEquivalences (D (I := I))
      (OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X)) := by
  have h : (OriginalICone.contraction (B := B)).app X =
      OrdinaryHoChosenPuppe.toZero Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        ((cone).obj X) := Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact h ▸ (OriginalICone.contraction_trivialFibration X).2

/-- The whole actual original native Q/corner resolution acts on every input Arrow. -/
def resolution : Arrow (D (I := I)) ⥤ Arrow (D (I := I)) :=
  OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.resolutionFunctor (Q) (ε)

/-- Both original corner projections give its full natural Arrow comparison to the caller. -/
def resolutionToOriginal : resolution (B := B) (I := I) ⟶ 𝟭 (Arrow (D (I := I))) :=
  OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.toOriginalNatTrans (Q) (ε)

/-- The original Q cofiber and resolved cofiber are naturally joined by their actual weak legs. -/
def QCofiberToResolutionHoIso :
    CofiberNullity.cofiberQ (B := B) (I := I) ⋙ (H) ≅
      resolution (B := B) ⋙ OrdinaryHoChosenPuppe.cofiberFunctor (cone) (ι) (c) (hc) ⋙ (H) :=
  OrdinaryHoChosenFiberHomSequence.OriginalJoin.QCofiberToResolutionHoIso
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (Q) (ε)
    (Replacement.isCofibrant_cofibrantReplacement (B := B))
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
    (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => coneCollapse_weak X)

variable (a : ∀ F : Arrow (D (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

omit B in
/-- Both original projection functions identify the entire native and generic chosen-fiber maps. -/
theorem chosenFiberMap_eq_generic {F G : Arrow (D (I := I))} (q : F ⟶ G) :
    Diagrams.FiberGeometry.chosenFiberMap q (a F) (a G) (ha G) =
      OrdinaryHoChosenFiberMaps.chosenMap Diagrams.zeroDiagram
        Diagrams.zeroDiagram_isZero a ha q := by
  apply PullbackCone.IsLimit.hom_ext (ha G)
  · rw [Diagrams.FiberGeometry.chosenFiberMap_fst, OrdinaryHoChosenFiberMaps.chosenMap_fst]
  · rw [Diagrams.FiberGeometry.chosenFiberMap_snd, OrdinaryHoChosenFiberMaps.chosenMap_snd]

/-- The original native chosen-fiber functor retains the same carriers and both full projections. -/
def chosenFiberFunctorNatIso :
    OrdinaryHoChosenFiberMaps.chosenFunctor Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha ≅ Diagrams.FiberGeometry.chosenFiberFunctor a ha :=
  NatIso.ofComponents (fun F => Iso.refl (a F).pt) (fun {F G} q => by
    change OrdinaryHoChosenFiberMaps.chosenMap Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha q ≫ 𝟙 (a G).pt =
        𝟙 (a F).pt ≫ Diagrams.FiberGeometry.chosenFiberMap q (a F) (a G) (ha G)
    rw [Category.comp_id, Category.id_comp, chosenFiberMap_eq_generic a ha q])

/-- The full comparison retains every original chosen fiber and both actual projections. -/
def originalFibrationComparison :
    (P).ι ⋙ OrdinaryHoChosenFiberMaps.chosenFunctor
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha ⋙ (Q) ⋙
        OriginalISuspension.suspension (B := B) ⋙ (H) ⟶
      (P).ι ⋙ CofiberNullity.cofiberQ (B := B) ⋙ (H) :=
  OrdinaryHoChosenFiberHomSequence.OriginalJoin.originalSuspendedFiberToQCofiber
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (Q) (ε)
    (Replacement.isCofibrant_cofibrantReplacement (B := B))
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
    (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => coneCollapse_weak X)

/-- The comparison is transported through the identity-carrier full native fiber functor Iso. -/
def nativeFibrationComparison :
    (P).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (Q) ⋙
      OriginalISuspension.suspension (B := B) ⋙ (H) ⟶
        (P).ι ⋙ CofiberNullity.cofiberQ (B := B) ⋙ (H) :=
  (Functor.isoWhiskerLeft (P).ι (Functor.isoWhiskerRight (chosenFiberFunctorNatIso a ha).symm
    ((Q) ⋙ OriginalISuspension.suspension (B := B) ⋙ (H)))).hom ≫
      originalFibrationComparison (B := B) a ha

/-- The native comparison component is the original constructed fiber/cofiber function. -/
theorem nativeFibrationComparison_app (F : (P).FullSubcategory) :
    (nativeFibrationComparison (B := B) a ha).app F =
      (originalFibrationComparison (B := B) a ha).app F := by
  change (H).map ((OriginalISuspension.suspension (B := B)).map ((Q).map (𝟙 (a F.obj).pt))) ≫
    (originalFibrationComparison (B := B) a ha).app F = _
  have hi : (H).map ((OriginalISuspension.suspension (B := B)).map
      ((Q).map (𝟙 (a F.obj).pt))) =
      𝟙 ((H).obj ((OriginalISuspension.suspension (B := B)).obj ((Q).obj (a F.obj).pt))) :=
    ((H).congr_map
      (((OriginalISuspension.suspension (B := B)).congr_map ((Q).map_id (a F.obj).pt)).trans
        ((OriginalISuspension.suspension (B := B)).map_id _))).trans ((H).map_id _)
  exact (congrArg (fun m => m ≫ (originalFibrationComparison (B := B) a ha).app F) hi).trans
    (Category.id_comp _)

omit B in
/-- This property retains every actual original K-right arrow of the same full family. -/
def rightArrowProperty (s : NativeStabilizationFamily.{u, v} I L) :
    ObjectProperty (Arrow (D (I := I))) := fun F => (generators s).rlp F.hom

omit B in
/-- Original K-rightness supplies the actual level fibration and original fibrant target. -/
def rightArrowAsFibrantFibration (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) : (P).FullSubcategory :=
  ⟨F.obj, ⟨(fibration_iff _).mpr (right_le_fibrations s _ F.property),
    Native.allObjectsFibrant F.obj.right⟩⟩

/-- The constructed comparison is a full natural transformation on the original K-right arrows. -/
def originalComparison (s : NativeStabilizationFamily.{u, v} I L) :
    (rightArrowProperty s).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (Q) ⋙
      OriginalISuspension.suspension (B := B) ⋙ (H) ⟶
      (rightArrowProperty s).ι ⋙ CofiberNullity.cofiberQ (B := B) ⋙ (H) where
  app F := (nativeFibrationComparison (B := B) a ha).app (rightArrowAsFibrantFibration s F)
  naturality F G q := (nativeFibrationComparison (B := B) a ha).naturality
    (show rightArrowAsFibrantFibration s F ⟶ rightArrowAsFibrantFibration s G from ⟨q.hom⟩)

/-- Every original Arrow square is retained on the actual suspension and Q-cofiber functions. -/
theorem originalComparison_naturality (s : NativeStabilizationFamily.{u, v} I L)
    {F G : (rightArrowProperty s).FullSubcategory} (q : F ⟶ G) :
    (H).map ((OriginalISuspension.suspension (B := B)).map
      ((Q).map (Diagrams.FiberGeometry.chosenFiberMap q.hom (a F.obj) (a G.obj) (ha G.obj)))) ≫
          (originalComparison (B := B) a ha s).app G =
      (originalComparison (B := B) a ha s).app F ≫
        (H).map ((CofiberNullity.cofiberQ (B := B)).map q.hom) :=
  (originalComparison (B := B) a ha s).naturality q

/-- The actual chosen-fiber Iso transports the full Omega tests of the unchanged collapse. -/
theorem chosenFiberCollapse_omegaTests_iff
    (s : NativeStabilizationFamily.{u, v} I L) {X Y : D (I := I)} (p : X ⟶ Y)
    (b : PullbackCone p (Diagrams.zeroTo Y)) (hb : IsLimit b) :
    omegaTests s b.snd ↔ omegaTests s (Diagrams.FiberGeometry.fiberToZero p) := by
  let e : Arrow.mk b.snd ≅ Arrow.mk (Diagrams.FiberGeometry.fiberToZero p) :=
    Arrow.isoMk (Diagrams.FiberGeometry.chosenFiberIso p b hb) (Iso.refl Diagrams.zeroDiagram)
      ((Diagrams.FiberGeometry.chosenFiberIso_hom_snd p b hb).trans (Category.comp_id _).symm)
  exact (omegaTests s).arrow_mk_iso_iff e

private theorem originalSphereQuillen :
    (ScalarLeibniz.adjunction (A := I) PointedCGWH.sphereOne).IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen PointedCGWH.sphereOne

attribute [local instance] originalSphereQuillen

/-- The actual scalar adjunct of the suspended Q-fiber comparison is its source-loop map. -/
def sourceLoopComparisonQApp (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).obj ((Q).obj (a F.obj).pt) ⟶
      (H).obj ((EnrichedFunctorCat.cotensor PointedCGWH.sphereOne).obj
        ((CofiberNullity.cofiberQ (B := B)).obj F.obj)) :=
  QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction PointedCGWH.sphereOne)
    ((Q).obj (a F.obj).pt) ((CofiberNullity.cofiberQ (B := B)).obj F.obj)
    ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).inv.app (a F.obj).pt ≫
      (originalComparison (B := B) a ha s).app F)

/-- Every entire source Arrow and cofiber target map is retained by the actual scalar adjunct. -/
theorem sourceLoopComparisonQApp_naturality (s : NativeStabilizationFamily.{u, v} I L)
    {F G : (rightArrowProperty s).FullSubcategory} (q : F ⟶ G) :
    (H).map ((Q).map (Diagrams.FiberGeometry.chosenFiberMap q.hom
      (a F.obj) (a G.obj) (ha G.obj))) ≫ sourceLoopComparisonQApp (B := B) a ha s G =
    sourceLoopComparisonQApp (B := B) a ha s F ≫
      (H).map ((EnrichedFunctorCat.cotensor PointedCGWH.sphereOne).map
        ((CofiberNullity.cofiberQ (B := B)).map q.hom)) := by
  let α := Diagrams.FiberGeometry.chosenFiberMap q.hom (a F.obj) (a G.obj) (ha G.obj)
  let β := (CofiberNullity.cofiberQ (B := B)).map q.hom
  let eS := ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := I)
  let ψ := originalComparison (B := B) a ha s
  have hTensor :
      (H).map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map ((Q).map α)) ≫
        (eS.inv.app (a G.obj).pt ≫ ψ.app G) =
      (eS.inv.app (a F.obj).pt ≫ ψ.app F) ≫ (H).map β := by
    rw [← Category.assoc,
      ScalarSphereSuspension.originalISuspensionQIsoSphereQ_inv_naturality,
      Category.assoc, originalComparison_naturality, Category.assoc]
  have hAdj := congrArg (QuillenOrdinaryHoHom.homEquiv
    (ScalarLeibniz.adjunction PointedCGWH.sphereOne) ((Q).obj (a F.obj).pt)
      ((CofiberNullity.cofiberQ (B := B)).obj G.obj)) hTensor
  rw [QuillenOrdinaryHoHom.homEquiv_naturality_left,
    QuillenOrdinaryHoHom.homEquiv_naturality_right] at hAdj
  exact hAdj

/-- The full source-loop comparison acts on every actual Q-fiber and original cofiber Arrow map. -/
def sourceLoopComparisonQ (s : NativeStabilizationFamily.{u, v} I L) :
    (rightArrowProperty s).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (Q) ⋙ (H) ⟶
      (rightArrowProperty s).ι ⋙ CofiberNullity.cofiberQ (B := B) ⋙
        EnrichedFunctorCat.cotensor PointedCGWH.sphereOne ⋙ (H) where
  app F := sourceLoopComparisonQApp (B := B) a ha s F
  naturality _ _ q := sourceLoopComparisonQApp_naturality (B := B) a ha s q

/-- Both full original fiber functions give the natural ordinary-Ho Iso of its same Q counit. -/
def originalQFiberCounitHoIso (s : NativeStabilizationFamily.{u, v} I L) :
    (rightArrowProperty s).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (Q) ⋙ (H) ≅
      (rightArrowProperty s).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (H) := by
  let τ := Functor.whiskerLeft (rightArrowProperty s).ι (Functor.whiskerRight
    (Functor.whiskerLeft (Diagrams.FiberGeometry.chosenFiberFunctor a ha) (ε)) (H))
  let _ : ∀ F, IsIso (τ.app F) := fun F => Localization.inverts (H)
    (weakEquivalences (D (I := I))) _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) (a F.obj).pt)
  let _ : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The original chosen fiber maps to the actual scalar loop of its original Q cofiber. -/
def sourceLoopComparison (s : NativeStabilizationFamily.{u, v} I L) :
    (rightArrowProperty s).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha ⋙ (H) ⟶
      (rightArrowProperty s).ι ⋙ CofiberNullity.cofiberQ (B := B) ⋙
        EnrichedFunctorCat.cotensor PointedCGWH.sphereOne ⋙ (H) :=
  (originalQFiberCounitHoIso (B := B) a ha s).inv ≫ sourceLoopComparisonQ (B := B) a ha s

/-- The original Q-fiber counit recovers the whole scalar adjunct on its unchanged carrier. -/
theorem sourceLoopComparison_counit (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (originalQFiberCounitHoIso (B := B) a ha s).hom.app F ≫
      (sourceLoopComparison (B := B) a ha s).app F =
        sourceLoopComparisonQApp (B := B) a ha s F := by
  let e := originalQFiberCounitHoIso (B := B) a ha s
  change e.hom.app F ≫ (e.inv.app F ≫ sourceLoopComparisonQApp (B := B) a ha s F) = _
  rw [← Category.assoc, show e.hom.app F ≫ e.inv.app F = 𝟙 _ from congr_app e.hom_inv_id F,
    Category.id_comp]

/-- Every full original source Arrow commutes with the entire native source-loop comparison. -/
theorem sourceLoopComparison_naturality (s : NativeStabilizationFamily.{u, v} I L)
    {F G : (rightArrowProperty s).FullSubcategory} (q : F ⟶ G) :
    (H).map (Diagrams.FiberGeometry.chosenFiberMap q.hom
      (a F.obj) (a G.obj) (ha G.obj)) ≫ (sourceLoopComparison (B := B) a ha s).app G =
    (sourceLoopComparison (B := B) a ha s).app F ≫
      (H).map ((EnrichedFunctorCat.cotensor PointedCGWH.sphereOne).map
        ((CofiberNullity.cofiberQ (B := B)).map q.hom)) :=
  (sourceLoopComparison (B := B) a ha s).naturality q

/-- The inverse scalar adjunct recovers the full original suspended-fiber comparison function. -/
theorem sourceLoopComparisonQApp_inverseAdjunct (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction PointedCGWH.sphereOne)
      ((Q).obj (a F.obj).pt) ((CofiberNullity.cofiberQ (B := B)).obj F.obj)).symm
        (sourceLoopComparisonQApp (B := B) a ha s F) =
    (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).inv.app (a F.obj).pt ≫
      (originalComparison (B := B) a ha s).app F :=
  (QuillenOrdinaryHoHom.homEquiv (ScalarLeibniz.adjunction PointedCGWH.sphereOne)
    ((Q).obj (a F.obj).pt) ((CofiberNullity.cofiberQ (B := B)).obj F.obj)).symm_apply_apply _

variable (b : ∀ F : Arrow (D (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- The entire native suspended-fiber comparison retains both arbitrary original fiber choices. -/
theorem originalComparison_choice (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).map ((OriginalISuspension.suspension (B := B)).map ((Q).map
      (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
        Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom)) ≫
        (originalComparison (B := B) b hb s).app F =
      (originalComparison (B := B) a ha s).app F := by
  change _ ≫ (nativeFibrationComparison (B := B) b hb).app (rightArrowAsFibrantFibration s F) =
    (nativeFibrationComparison (B := B) a ha).app (rightArrowAsFibrantFibration s F)
  rw [nativeFibrationComparison_app, nativeFibrationComparison_app]
  exact OrdinaryHoChosenFiberHomSequence.OriginalJoin.originalSuspendedFiberToQCofiber_choice
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha (Q) (ε)
    (Replacement.isCofibrant_cofibrantReplacement (B := B))
    (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (B := B))
    (cone) (ι) (c) (hc) (fun X _ => OriginalICone.inclusion_cofibration X)
    (fun X _ => coneCollapse_weak X) b hb (rightArrowAsFibrantFibration s F)

/-- The scalar adjunct transports the full original limit-choice Iso between the actual Q fibers. -/
theorem sourceLoopComparisonQApp_choice (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).map ((Q).map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom) ≫
        sourceLoopComparisonQApp (B := B) b hb s F =
      sourceLoopComparisonQApp (B := B) a ha s F := by
  let γ := (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
    Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom
  let eS := ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := I)
  have hTensor :
      (H).map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map ((Q).map γ)) ≫
        (eS.inv.app (b F.obj).pt ≫ (originalComparison (B := B) b hb s).app F) =
      eS.inv.app (a F.obj).pt ≫ (originalComparison (B := B) a ha s).app F := by
    rw [← Category.assoc,
      ScalarSphereSuspension.originalISuspensionQIsoSphereQ_inv_naturality,
      Category.assoc, originalComparison_choice]
  have hAdj := congrArg (QuillenOrdinaryHoHom.homEquiv
    (ScalarLeibniz.adjunction PointedCGWH.sphereOne) ((Q).obj (a F.obj).pt)
      ((CofiberNullity.cofiberQ (B := B)).obj F.obj)) hTensor
  rw [QuillenOrdinaryHoHom.homEquiv_naturality_left] at hAdj
  exact hAdj

/-- Both original fiber projections identify the complete source-loop map for every limit choice. -/
theorem sourceLoopComparison_choice (s : NativeStabilizationFamily.{u, v} I L)
    (F : (rightArrowProperty s).FullSubcategory) :
    (H).map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫
        (sourceLoopComparison (B := B) b hb s).app F =
      (sourceLoopComparison (B := B) a ha s).app F := by
  let γ := (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
    Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom
  let ηa := (originalQFiberCounitHoIso (B := B) a ha s).hom.app F
  let ηb := (originalQFiberCounitHoIso (B := B) b hb s).hom.app F
  have hη : (H).map ((Q).map γ) ≫ ηb = ηa ≫ (H).map γ := by
    have h := (H).congr_map ((ε).naturality γ)
    simp only [Functor.id_map, Functor.map_comp] at h
    exact h
  change (H).map γ ≫ _ = _
  apply (cancel_epi ηa).mp
  calc
    ηa ≫ ((H).map γ ≫ (sourceLoopComparison (B := B) b hb s).app F) =
        (H).map ((Q).map γ) ≫ (ηb ≫ (sourceLoopComparison (B := B) b hb s).app F) := by
      rw [← Category.assoc, ← hη, Category.assoc]
    _ = (H).map ((Q).map γ) ≫ sourceLoopComparisonQApp (B := B) b hb s F := by
      rw [sourceLoopComparison_counit]
    _ = sourceLoopComparisonQApp (B := B) a ha s F :=
      sourceLoopComparisonQApp_choice (B := B) a ha b hb s F
    _ = ηa ≫ (sourceLoopComparison (B := B) a ha s).app F :=
      (sourceLoopComparison_counit (B := B) a ha s F).symm

/-- A coefficient null in the original Q cofiber has the actual original suspended source lift. -/
theorem originalQCoefficientLift_of_null (F : Arrow (D (I := I))) (K : D (I := I))
    [IsCofibrant K] (g : K ⟶ (Q).obj F.right)
    (hg : (H).map (g ≫ (c ((Q).mapArrow.obj F)).inr) =
      (H).map (OrdinaryHoChosenPuppe.nullMap Diagrams.zeroDiagram
        Diagrams.zeroDiagram_isZero K (c ((Q).mapArrow.obj F)).pt)) :
    ∃ k : (H).obj ((OriginalISuspension.suspension (B := B)).obj K) ⟶
        (H).obj ((OriginalISuspension.suspension (B := B)).obj ((Q).obj F.left)),
      k ≫ (H).map ((OriginalISuspension.suspension (B := B)).map ((Q).map F.hom)) =
        (H).map ((OriginalISuspension.suspension (B := B)).map g) := by
  let _ : IsCofibrant ((Q).mapArrow.obj F).right :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) F.right
  let _ : Cofibration ((ι).app K) :=
    (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration K)
  let _ : Cofibration ((ι).app ((Q).mapArrow.obj F).right) :=
    (cofibration_iff _).mpr (OriginalICone.inclusion_cofibration _)
  exact OrdinaryHoChosenFiberCofiberComparison.suspendedCoefficientLift_of_null
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (cone) (ι) (c) (hc)
    ((Q).mapArrow.obj F) K g (coneCollapse_weak K) (coneCollapse_weak _) hg

end OriginalFiberComparison
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
