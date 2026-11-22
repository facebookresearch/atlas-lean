/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.RTReflection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberExactness
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.DiagonalFiberSequence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization

/-!
# Original native sequential chosen-fiber nullity

The original sequential K-right and Omega-target test hypotheses prove
nullity of every caller-chosen fiber in the unchanged integer homotopy
functors and the original Omega tests. The complete existing comparison
foundation is imported from `StabilizationKOriginalFiberComparison`.
Symmetric and orthogonal chosen-fiber nullity remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberNullity

/-!
Deprecated compatibility names for the original comparison API.
The canonical declarations remain in `OriginalFiberComparison`; each old
name refers directly to its canonical target and retains the original type.
-/

@[deprecated OriginalFiberComparison.resolution (since := "2026-10-30")]
alias resolution := OriginalFiberComparison.resolution

@[deprecated OriginalFiberComparison.resolutionToOriginal (since := "2026-10-30")]
alias resolutionToOriginal := OriginalFiberComparison.resolutionToOriginal

@[deprecated OriginalFiberComparison.QCofiberToResolutionHoIso (since := "2026-10-30")]
alias QCofiberToResolutionHoIso := OriginalFiberComparison.QCofiberToResolutionHoIso

@[deprecated OriginalFiberComparison.chosenFiberMap_eq_generic (since := "2026-10-30")]
alias chosenFiberMap_eq_generic := OriginalFiberComparison.chosenFiberMap_eq_generic

@[deprecated OriginalFiberComparison.chosenFiberFunctorNatIso (since := "2026-10-30")]
alias chosenFiberFunctorNatIso := OriginalFiberComparison.chosenFiberFunctorNatIso

@[deprecated OriginalFiberComparison.originalFibrationComparison (since := "2026-10-30")]
alias originalFibrationComparison := OriginalFiberComparison.originalFibrationComparison

@[deprecated OriginalFiberComparison.nativeFibrationComparison (since := "2026-10-30")]
alias nativeFibrationComparison := OriginalFiberComparison.nativeFibrationComparison

@[deprecated OriginalFiberComparison.nativeFibrationComparison_app (since := "2026-10-30")]
alias nativeFibrationComparison_app := OriginalFiberComparison.nativeFibrationComparison_app

@[deprecated OriginalFiberComparison.rightArrowProperty (since := "2026-10-30")]
alias rightArrowProperty := OriginalFiberComparison.rightArrowProperty

@[deprecated OriginalFiberComparison.rightArrowAsFibrantFibration (since := "2026-10-30")]
alias rightArrowAsFibrantFibration := OriginalFiberComparison.rightArrowAsFibrantFibration

@[deprecated OriginalFiberComparison.originalComparison (since := "2026-10-30")]
alias originalComparison := OriginalFiberComparison.originalComparison

@[deprecated OriginalFiberComparison.originalComparison_naturality (since := "2026-10-30")]
alias originalComparison_naturality := OriginalFiberComparison.originalComparison_naturality

@[deprecated OriginalFiberComparison.chosenFiberCollapse_omegaTests_iff (since := "2026-10-30")]
alias chosenFiberCollapse_omegaTests_iff :=
    OriginalFiberComparison.chosenFiberCollapse_omegaTests_iff

@[deprecated OriginalFiberComparison.sourceLoopComparisonQApp (since := "2026-10-30")]
alias sourceLoopComparisonQApp := OriginalFiberComparison.sourceLoopComparisonQApp

@[deprecated OriginalFiberComparison.sourceLoopComparisonQApp_naturality (since := "2026-10-30")]
alias sourceLoopComparisonQApp_naturality :=
    OriginalFiberComparison.sourceLoopComparisonQApp_naturality

@[deprecated OriginalFiberComparison.sourceLoopComparisonQ (since := "2026-10-30")]
alias sourceLoopComparisonQ := OriginalFiberComparison.sourceLoopComparisonQ

@[deprecated OriginalFiberComparison.originalQFiberCounitHoIso (since := "2026-10-30")]
alias originalQFiberCounitHoIso := OriginalFiberComparison.originalQFiberCounitHoIso

@[deprecated OriginalFiberComparison.sourceLoopComparison (since := "2026-10-30")]
alias sourceLoopComparison := OriginalFiberComparison.sourceLoopComparison

@[deprecated OriginalFiberComparison.sourceLoopComparison_counit (since := "2026-10-30")]
alias sourceLoopComparison_counit := OriginalFiberComparison.sourceLoopComparison_counit

@[deprecated OriginalFiberComparison.sourceLoopComparison_naturality (since := "2026-10-30")]
alias sourceLoopComparison_naturality := OriginalFiberComparison.sourceLoopComparison_naturality

@[deprecated OriginalFiberComparison.sourceLoopComparisonQApp_inverseAdjunct
    (since := "2026-10-30")]
alias sourceLoopComparisonQApp_inverseAdjunct :=
    OriginalFiberComparison.sourceLoopComparisonQApp_inverseAdjunct

@[deprecated OriginalFiberComparison.originalComparison_choice (since := "2026-10-30")]
alias originalComparison_choice := OriginalFiberComparison.originalComparison_choice

@[deprecated OriginalFiberComparison.sourceLoopComparisonQApp_choice (since := "2026-10-30")]
alias sourceLoopComparisonQApp_choice := OriginalFiberComparison.sourceLoopComparisonQApp_choice

@[deprecated OriginalFiberComparison.sourceLoopComparison_choice (since := "2026-10-30")]
alias sourceLoopComparison_choice := OriginalFiberComparison.sourceLoopComparison_choice

@[deprecated OriginalFiberComparison.originalQCoefficientLift_of_null (since := "2026-10-30")]
alias originalQCoefficientLift_of_null := OriginalFiberComparison.originalQCoefficientLift_of_null

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] Native.modelCategory
attribute [local instance] Native.allObjectsFibrant Replacement.isCofibrant_cofibrantReplacement

omit B in
private theorem exact_middle_eq_one
    {G₀ G₁ G₂ G₃ G₄ : Type*}
    [Monoid G₀] [Monoid G₁] [Monoid G₂] [Monoid G₃] [Monoid G₄]
    (a : G₀ →* G₁) (d : G₁ →* G₂) (i : G₂ →* G₃) (p : G₃ →* G₄)
    (hBase : Function.MulExact a d) (hFiber : Function.MulExact d i)
    (hTotal : Function.MulExact i p) (ha : Function.Surjective a)
    (hp : Function.Injective p) (x : G₂) : x = 1 := by
  have hi : i x = 1 := hp ((hTotal.apply_apply_eq_one x).trans p.map_one.symm)
  obtain ⟨y, hy⟩ := (hFiber x).mp hi
  obtain ⟨z, hz⟩ := ha y
  exact hy.symm.trans ((congrArg d hz).symm.trans (hBase.apply_apply_eq_one z))

omit B in
private theorem groupExact_middle_subsingleton
    {G₀ G₁ G₂ G₃ G₄ : GrpCat.{v}}
    (a : G₀ ⟶ G₁) (d : G₁ ⟶ G₂) (i : G₂ ⟶ G₃) (p : G₃ ⟶ G₄)
    (hBase : Function.MulExact a.hom d.hom) (hFiber : Function.MulExact d.hom i.hom)
    (hTotal : Function.MulExact i.hom p.hom) [IsIso a] [IsIso p] : Subsingleton G₂ := by
  have hOne (x : G₂) : x = 1 :=
    exact_middle_eq_one a.hom d.hom i.hom p.hom hBase hFiber hTotal
      (ConcreteCategory.bijective_of_isIso a).2 (ConcreteCategory.bijective_of_isIso p).1 x
  exact ⟨fun x y => (hOne x).trans (hOne y).symm⟩

omit B in
private theorem literalPoint_pi_subsingleton (n : ℕ) :
    Subsingleton (PointedCGWH.piN n PointedCGWH.StrictFiberGeometry.pointObject.{u, v}) := by
  let _ : Subsingleton (CGWH.cgwhToTop.obj
      PointedCGWH.StrictFiberGeometry.pointObject.{u, v}.right) := by
    change Subsingleton PUnit.{v + 1}
    infer_instance
  let _ : Subsingleton (GenLoop (Fin n)
      (CGWH.cgwhToTop.obj PointedCGWH.StrictFiberGeometry.pointObject.{u, v}.right)
      (PointedCGWH.underlyingBasepoint PointedCGWH.StrictFiberGeometry.pointObject)) :=
    ⟨fun a b => by ext t; exact Subsingleton.elim _ _⟩
  change Subsingleton (Quotient (GenLoop.Homotopic.setoid (Fin n) _))
  refine ⟨fun a b => Quotient.inductionOn₂ a b ?_⟩
  intro a b
  exact congrArg (Quotient.mk _) (Subsingleton.elim a b)

omit B in
private theorem pointedZero_pi_subsingleton (n : ℕ) :
    Subsingleton (PointedCGWH.piN n (0 : PointedCGWH.{u, v})) := by
  let _ : Subsingleton ((PointedCGWH.piNFunctor n).obj
      PointedCGWH.StrictFiberGeometry.pointObject.{u, v}) := literalPoint_pi_subsingleton n
  let e := (PointedCGWH.piNFunctor n).mapIso
    ((isZero_zero PointedCGWH.{u, v}).isTerminal.uniqueUpToIso
      PointedCGWH.StrictFiberGeometry.pointObjectIsTerminal)
  exact (ConcreteCategory.bijective_of_isIso e.hom).1.subsingleton


omit B in
private theorem nativeZero_positivePi_subsingleton
    {A : Type} [EnrichedCategory PointedCGWH.{u, v} A] (a : A) (k : ℕ) :
    Subsingleton ((PointedCGWH.piNPositiveFunctor k).obj
      ((EnrichedFunctorCat.evaluation a).obj
        (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram (A := A)))) := by
  let _ : Subsingleton ((PointedCGWH.piNPositiveFunctor k).obj (0 : PointedCGWH.{u, v})) :=
    pointedZero_pi_subsingleton (k + 1)
  let e := (PointedCGWH.piNPositiveFunctor k).mapIso
    (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.initialDiagramComponentZeroIso a)
  exact (ConcreteCategory.bijective_of_isIso e.hom).1.subsingleton

omit B in
private theorem originalGroupColimit_subsingleton (D : ℕ ⥤ GrpCat.{v})
    (hD : ∀ n, Subsingleton (D.obj n)) :
    Subsingleton (GrpCat.FilteredColimits.colimitCocone D).pt := by
  let _ : PreservesFilteredColimitsOfSize.{0, 0} (forget GrpCat.{v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{v, v, 0, 0} (forget GrpCat.{v})
  have hSet := isColimitOfPreserves (forget GrpCat.{v})
    (GrpCat.FilteredColimits.colimitCoconeIsColimit D)
  have hOne (x : (GrpCat.FilteredColimits.colimitCocone D).pt) : x = 1 := by
    obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit hSet x
    change (GrpCat.FilteredColimits.colimitCocone D).ι.app n y = x at hy
    let _ : Subsingleton ((D ⋙ forget GrpCat).obj n) := hD n
    exact hy.symm.trans ((congrArg ((GrpCat.FilteredColimits.colimitCocone D).ι.app n)
      (Subsingleton.elim y 1)).trans (map_one _))
  exact ⟨fun x y => (hOne x).trans (hOne y).symm⟩

section Sequential

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence

local notation "sSeq" => PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family

omit B in
/-- The unchanged original sequential zero has trivial groups in every integer degree. -/
theorem sequentialZero_integerPi_subsingleton (q : ℤ) :
    Subsingleton ((integerStablePiFunctor.{u, v} q).obj
      HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.zeroDiagram) := by
  apply originalGroupColimit_subsingleton
  intro n
  exact nativeZero_positivePi_subsingleton
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne
      (integerTailLevel q + n)) (integerTailPositiveIndex q + n)

private theorem originalSequentialLevelFibrations
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : (generators sSeq).rlp p) :
    ∀ n : ℕ, fibrations PointedCGWH.{u, v} (PointedCGWH.SequentialSpectrum.levelMap p n) := by
  have hLevel := ((lifting_iff sSeq p).mp hp).1
  rw [Native.fibrations_eq] at hLevel
  have hEval := (EvaluationTransfer.evaluationProperty_iff _ _ p).mp hLevel
  exact fun n => hEval (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree
    PointedCGWH.sphereOne n)

/-- The actual original total projection is null in every integer group for a K-right
sequential Omega-test equivalence, on the caller's unchanged chosen fiber. -/
theorem sequentialChosenFiber_totalPiMap_eq_one
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : (generators sSeq).rlp p)
    (hw : omegaTests sSeq p)
    (b : PullbackCone p (Diagrams.zeroTo Y)) (hb : IsLimit b) (q : ℤ)
    (x : (integerStablePiFunctor q).obj b.pt) :
    ((integerStablePiFunctor q).map b.fst).hom x = 1 := by
  have hLocal : localTestEquivalences sSeq p :=
    (originalLocalTestEquivalence_iff_omegaTests sSeq p).mpr hw
  have hPi : integerPiStarEquivalences p :=
    (nativeLocalTests_iff_originalIntegerPiStar p).mp hLocal
  let _ : IsIso ((integerStablePiFunctor q).map p) :=
    (integerPiStarEquivalences_iff p).mp hPi q
  have hExact :=
    PointedCGWH.SequentialSpectrum.StableHomotopy.integerStablePi_chosenFiber_exact_at_total
      p b hb (originalSequentialLevelFibrations p hp) q
  apply (ConcreteCategory.bijective_of_isIso ((integerStablePiFunctor q).map p)).1
  exact (hExact.apply_apply_eq_one x).trans
    (map_one (((integerStablePiFunctor q).map p).hom)).symm

private theorem originalSequentialDiagonalMap_isIso
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hw : omegaTests sSeq p) (m k : ℕ) :
    IsIso (GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map p)) := by
  have hLocal : localTestEquivalences sSeq p :=
    (originalLocalTestEquivalence_iff_omegaTests sSeq p).mpr hw
  have hPi : integerPiStarEquivalences p :=
    (nativeLocalTests_iff_originalIntegerPiStar p).mp hLocal
  have hIso := (integerPiStarEquivalences_iff p).mp hPi
    (integerDegree m k)
  exact ((MorphismProperty.isomorphisms GrpCat.{v}).arrow_mk_iso_iff
    (integerMapArrowIso m k p)).mpr hIso

/-- Every original integer class of the unchanged chosen sequential fiber is the identity. -/
theorem sequentialChosenFiber_integerPi_eq_one
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : (generators sSeq).rlp p) (hw : omegaTests sSeq p)
    (b : PullbackCone p (Diagrams.zeroTo Y)) (hb : IsLimit b) (q : ℤ)
    (x : (integerStablePiFunctor q).obj b.pt) : x = 1 := by
  let m := integerTailLevel q
  let k := integerTailPositiveIndex q
  let hLevel := originalSequentialLevelFibrations p hp
  let a := GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m (k + 1)).map p)
  let d := diagonalConnectingMap p b hb hLevel m k
  let i := GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map b.fst)
  let f := GrpCat.FilteredColimits.colimitMap ((diagonalDiagramFunctor m k).map p)
  let _ : IsIso a := originalSequentialDiagonalMap_isIso p hw m (k + 1)
  let _ : IsIso f := originalSequentialDiagonalMap_isIso p hw m k
  have hBase := diagonal_exact_at_base p b hb hLevel m k
  have hFiber := diagonal_exact_at_fiber p b hb hLevel m k
  have hTotal := diagonal_exact_at_total p b hb hLevel m k
  let _ : Subsingleton ((integerStablePiFunctor q).obj b.pt) :=
    groupExact_middle_subsingleton a d i f hBase hFiber hTotal
  exact Subsingleton.elim x 1

/-- The same original chosen sequential collapse is an Iso in every original integer test. -/
theorem sequentialChosenFiberCollapse_integerPiStar
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : (generators sSeq).rlp p) (hw : omegaTests sSeq p)
    (b : PullbackCone p (Diagrams.zeroTo Y)) (hb : IsLimit b) :
    integerPiStarEquivalences b.snd := by
  apply (integerPiStarEquivalences_iff b.snd).mpr
  intro q
  let _ : Subsingleton ((integerStablePiFunctor q).obj b.pt) := ⟨fun x y =>
    (sequentialChosenFiber_integerPi_eq_one p hp hw b hb q x).trans
      (sequentialChosenFiber_integerPi_eq_one p hp hw b hb q y).symm⟩
  let _ := sequentialZero_integerPi_subsingleton.{u, v} q
  exact (ConcreteCategory.isIso_iff_bijective ((integerStablePiFunctor q).map b.snd)).mpr
    (Function.bijective_of_subsingleton' _)

/-- Original K-rightness and Omega tests prove the actual chosen sequential fiber collapse tests. -/
theorem sequentialChosenFiberCollapse_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (p : X ⟶ Y)
    (hp : (generators sSeq).rlp p) (hw : omegaTests sSeq p)
    (b : PullbackCone p (Diagrams.zeroTo Y)) (hb : IsLimit b) :
    omegaTests sSeq b.snd :=
  (originalLocalTestEquivalence_iff_omegaTests sSeq b.snd).mp
    ((nativeLocalTests_iff_originalIntegerPiStar b.snd).mpr
      (sequentialChosenFiberCollapse_integerPiStar p hp hw b hb))

end Sequential

end OriginalFiberNullity
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
