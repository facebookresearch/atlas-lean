/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ConditionalFiberHom
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.OriginalClasses

/-!
# Conditional recognition from the actual orthogonal fiber comparison

The exact original comparison Hom premise is used at the genuine
negative one target D(E). Original cofiber nullity then gives nullity of
every caller fiber Hom term. The caller collapse therefore passes all
actual Omega tests, and the existing native one-sphere group detection
theorem gives the full level trivial-fibration class on arbitrary endpoints.

Recognition identifies the two full intersections from the unchanged
original I/K records and Thom cell acyclicity. Every statement using the
pending original comparison retains that premise explicitly. No final
native stable model or proof of the comparison is supplied here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalRecognition

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
open PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}
private abbrev FiberChoices :=
  ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})
private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

/-- The actual negative one target and comparison inverse give nullity
of every original caller fiber Hom test, without Omega endpoint assumptions. -/
theorem chosenFiberHom_eq_null (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (F : rightArrows.{u, v})
    (hW : stableWeakEquivalences F.obj.hom) (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj (a F.obj).pt ⟶ H.obj E) :
    g = OrdinaryHoCofiberKernel.nullHom (a F.obj).pt E := by
  let e := cofiberToFiberHomEquiv hComparison a ha (-1) F E hE
  obtain ⟨k, hk⟩ := e.surjective g
  have hNull : k = OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj)
      ((integerTarget (-1)).obj E) :=
    NativeK.CofiberNullity.cofiberQHom_eq_null (B := B) orthogonalFamily
      F.obj.hom hW ((integerTarget (-1)).obj E) (integerTarget_isOmega (-1) E hE) k
  rw [← hk, hNull]
  exact cofiberToFiberHomEquiv_null hComparison a ha (-1) F E hE

/-- Every original caller collapse passes every actual native Omega
Hom test under the precise original comparison premise. -/
theorem chosenFiberCollapse_omegaTests (hComparison : ComparisonHomBijections.{u, v} (B := B))
    (a : FiberChoices.{u, v}) (ha : ∀ F, IsLimit (a F)) (F : rightArrows.{u, v})
    (hW : stableWeakEquivalences F.obj.hom) :
    stableWeakEquivalences (a F.obj).snd := by
  intro E hE
  have hUnique : Subsingleton (H.obj (a F.obj).pt ⟶ H.obj E) :=
    ⟨fun g h => (chosenFiberHom_eq_null hComparison a ha F hW E hE g).trans
      (chosenFiberHom_eq_null hComparison a ha F hW E hE h).symm⟩
  have hCollapse : (a F.obj).snd = OrdinaryHoChosenPuppe.toZero
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (a F.obj).pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse]
  exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero (a F.obj).pt E).mpr hUnique

/-- Every individual caller limit cone retains both its projections
and actual collapse, with no requirement to use the canonical cone. -/
theorem anyChosenFiberCollapse_omegaTests
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) (hp : stableFibrations p)
    (hW : stableWeakEquivalences p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    stableWeakEquivalences c.snd := by
  let a : FiberChoices.{u, v} := fun F => Diagrams.FiberGeometry.fiberCone F.hom
  let ha : ∀ F, IsLimit (a F) := fun F => Diagrams.FiberGeometry.fiberConeIsLimit F.hom
  let F : rightArrows.{u, v} := ⟨Arrow.mk p, hp⟩
  have hCanonical : stableWeakEquivalences (Diagrams.FiberGeometry.fiberToZero p) :=
    chosenFiberCollapse_omegaTests hComparison a ha F hW
  exact (NativeK.OriginalFiberComparison.chosenFiberCollapse_omegaTests_iff
    orthogonalFamily p c hc).mpr hCanonical

/-- The full native one-sphere group detection proves the actual level
trivial fibration and every original dimensional component. -/
theorem right_weak_levelTrivialFibration
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) (hp : stableFibrations p)
    (hW : stableWeakEquivalences p) :
    trivialFibrations C.{u, v} p ∧ ∀ n : O.{u, v},
      trivialFibrations PointedCGWH.{u, v} (component p n) := by
  let c := Diagrams.FiberGeometry.fiberCone p
  let hc := Diagrams.FiberGeometry.fiberConeIsLimit p
  exact PointedCGWH.Spectra.NativeStable.orthogonal_chosenFiber_levelTrivialFibration
    p hp c hc (anyChosenFiberCollapse_omegaTests hComparison p hp hW c hc)

/-- The original I-right class is precisely the entire K-right and
actual all-target weak intersection on arbitrary native endpoints. -/
theorem right_class_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    originalI.{u, v}.rlp = stableTrivialFibrations := by
  apply le_antisymm originalIRight_le_stableTrivialFibrations
  intro X Y p hp
  exact (HomotopicalAlgebra.EnrichedProjective.Native.Data.generatorsI_rlp).ge p
    (right_weak_levelTrivialFibration hComparison p hp.1 hp.2).1

/-- The unchanged original paired K factors and Thom acyclicity give
the entire trivial-left intersection from the proved right-class equality. -/
theorem left_class_eq (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    originalK.{u, v}.rlp.llp = stableTrivialCofibrations :=
  OriginalGeneratedModel.left_class_eq originalI originalK stableWeakEquivalences
    inferInstance (right_class_eq hComparison)
    originalKLeft_le_stableWeakEquivalences originalKFactorizationData

/-- The stable fibrations are the full right orthogonal of the same
original trivial-cofibration intersection. -/
theorem stableFibrations_eq_trivialCofibrations_rlp
    (hComparison : ComparisonHomBijections.{u, v} (B := B)) :
    stableFibrations.{u, v} = stableTrivialCofibrations.rlp := by
  rw [← left_class_eq hComparison]
  exact originalK.rlp_llp_rlp.symm

/-- All caller fiber Hom terms are null in every actual integer target degree. -/
theorem anyChosenFiberHom_eq_null (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) (hp : stableFibrations p)
    (hW : stableWeakEquivalences p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (q : ℤ) (E : C.{u, v}) (hE : omegaProperty E)
    (g : H.obj c.pt ⟶ H.obj ((integerTarget q).obj E)) :
    g = OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget q).obj E) := by
  have hTests := anyChosenFiberCollapse_omegaTests hComparison p hp hW c hc
    ((integerTarget q).obj E) (integerTarget_isOmega q E hE)
  have hCollapse : c.snd = OrdinaryHoChosenPuppe.toZero
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero c.pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse] at hTests
  have hUnique := (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero c.pt ((integerTarget q).obj E)).mp hTests
  exact hUnique.elim _ _

/-- Weakness of every full K-right arrow is equivalent to the actual
collapse of each caller's entire chosen fiber cone. -/
theorem anyChosenFiberCollapse_omegaTests_iff
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) (hp : stableFibrations p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    stableWeakEquivalences p ↔ stableWeakEquivalences c.snd := by
  constructor
  · exact fun hW => anyChosenFiberCollapse_omegaTests hComparison p hp hW c hc
  · intro hTests
    have hLevel := PointedCGWH.Spectra.NativeStable.orthogonal_chosenFiber_levelTrivialFibration
      p hp c hc hTests
    have hI := (HomotopicalAlgebra.EnrichedProjective.Native.Data.generatorsI_rlp).ge p hLevel.1
    exact (originalIRight_le_stableTrivialFibrations p hI).2

/-- Every actual integer caller fiber Hom term detects the same full
weak class, retaining all Omega targets and the caller limit witness. -/
theorem anyChosenFiber_integerHomNull_iff
    (hComparison : ComparisonHomBijections.{u, v} (B := B))
    {X Y : C.{u, v}} (p : X ⟶ Y) (hp : stableFibrations p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    stableWeakEquivalences p ↔ ∀ (q : ℤ) (E : C.{u, v}), omegaProperty E →
      ∀ g : H.obj c.pt ⟶ H.obj ((integerTarget q).obj E),
        g = OrdinaryHoCofiberKernel.nullHom c.pt ((integerTarget q).obj E) := by
  constructor
  · intro hW q E hE g
    exact anyChosenFiberHom_eq_null hComparison p hp hW c hc q E hE g
  · intro hNull
    apply (anyChosenFiberCollapse_omegaTests_iff hComparison p hp c hc).mpr
    intro E hE
    have hUnique : Subsingleton (H.obj c.pt ⟶ H.obj E) :=
      ⟨fun g h => (hNull 0 E hE g).trans (hNull 0 E hE h).symm⟩
    have hCollapse : c.snd = OrdinaryHoChosenPuppe.toZero
        Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero c.pt :=
      Diagrams.zeroDiagramIsTerminal.hom_ext _ _
    rw [hCollapse]
    exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero c.pt E).mpr hUnique

end PointedCGWH.Spectra.Orthogonal.NativeStableModels.ConditionalRecognition
