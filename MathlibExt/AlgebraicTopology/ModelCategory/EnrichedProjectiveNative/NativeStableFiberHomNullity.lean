/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeFiberCofiberIntegerComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalIntegerFunctorBridge
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalCofiberNullity
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SuspensionTestDetection
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.NegativeHom
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.FiberHomComparison
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberHom
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ConditionalFiberHom

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionIntegerPiDetection

/-!
# Original native fiber Hom nullity

The original native zero, Q counit and I suspension are retained. The
actual suspension-to-zero tests reflect through the genuine first Omega
delooping. For an Omega-test weak arrow, every element of the original
integer cofiber-to-fiber comparison image is null. The orthogonal comparison is surjective by the actual native integer
detector; its full chosen-fiber collapse follows by genuine Omega delooping.
The symmetric comparison remains a separate source obligation.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberNullity

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory Native.allObjectsFibrant
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

omit B in
private instance nativeZero : HasZeroObject (D (I := I)) := Diagrams.nativeHasZeroObject

private abbrev H := toHomotopyCategory (D (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)

/-- Each original K-right comparison has isomorphic actual integer PiHo maps in every degree. -/
theorem originalComparison_all_integer_isIso
    (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)
    (s : NativeStabilizationFamily.{u, v} I L)
    (a : ∀ F : Arrow (D (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty s).FullSubcategory) :
    IsIso ((NativeStableCofiberIntegerMaps.integerPiHoFunctor j q).map
      ((OriginalFiberComparison.originalComparison (B := B) a ha s).app F)) := by
  simpa only [OriginalFiberComparison.originalComparison,
    OriginalFiberCofiberGeometry.suspendedComparison, Functor.comp_obj,
    ObjectProperty.ι_obj, Diagrams.FiberGeometry.chosenFiberFunctor,
    OriginalFiberComparison.rightArrowAsFibrantFibration] using
    NativeFiberCofiberIntegerComparison.suspendedComparison_all_integer_isIso
      j a ha q (OriginalFiberComparison.rightArrowAsFibrantFibration s F)

/-- The same original comparison has a genuine Q representative with all raw integer maps Iso. -/
theorem originalComparisonRepresentative_all_integer_isIso
    (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)
    (s : NativeStabilizationFamily.{u, v} I L)
    (a : ∀ F : Arrow (D (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty s).FullSubcategory) (q : ℤ) :
    IsIso ((NativeStableCofiberIntegerMaps.integerPiFunctor j q).map
      (NativeFiberCofiberIntegerComparison.homRepresentative
        ((OriginalFiberComparison.originalComparison (B := B) a ha s).app F))) :=
  NativeFiberCofiberIntegerComparison.homRepresentative_all_integer_isIso j
    ((OriginalFiberComparison.originalComparison (B := B) a ha s).app F)
    (fun r => originalComparison_all_integer_isIso j s a ha r F) q

/-- Every full native level-Ho source arrow preserves the original null class. -/
theorem nativeHom_null_precomp {X Y E : D (I := I)}
    (f : (H (I := I)).obj X ⟶ (H (I := I)).obj Y) :
    f ≫ OrdinaryHoCofiberKernel.nullHom Y E = OrdinaryHoCofiberKernel.nullHom X E := by
  let e := (Replacement.cofibrantReplacementProjectionIso (B := B) (A := I)).app X
  let r := NativeFiberCofiberIntegerComparison.homRepresentative f
  have hr : (H (I := I)).map r = e.hom ≫ f :=
    NativeFiberCofiberIntegerComparison.homRepresentative_ho f
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← hr, OrdinaryHoCofiberKernel.precomp_nullHom]
  exact (OrdinaryHoCofiberKernel.precomp_nullHom
    ((Replacement.cofibrantReplacementCounit (B := B) (A := I)).app X)).symm

/-- Tests of the unchanged native collapse are precisely uniqueness of all Omega-target Homs. -/
theorem toZero_omegaTests_iff (s : NativeStabilizationFamily.{u, v} I L) (X : D (I := I)) :
    omegaTests s (Diagrams.toZero X) ↔
      ∀ E : D (I := I), IsOmega s E →
        Subsingleton ((H (I := I)).obj X ⟶ (H (I := I)).obj E) := by
  have hc : Diagrams.toZero X = OrdinaryHoChosenPuppe.toZero
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  constructor
  · intro h E hE
    have hTest := h E hE
    rw [hc] at hTest
    exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X E).mp hTest
  · intro h E hE
    rw [hc]
    exact (OrdinaryHoPuppeCofiberNull.toZero_precomposition_bijective_iff
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X E).mpr (h E hE)

/-- Original I suspension after Q preserves nullity of the actual native collapse. -/
theorem suspensionQCollapse_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    (X : D (I := I)) (hX : omegaTests s (Diagrams.toZero X)) :
    omegaTests s (Diagrams.toZero ((S (I := I)).obj ((Q (I := I)).obj X))) := by
  apply (toZero_omegaTests_iff s _).mpr
  intro E hE
  let R := cotensor (I := I) PointedCGWH.sphereOne.{u, v}
  let adj := ScalarLeibniz.adjunction (A := I) PointedCGWH.sphereOne.{u, v}
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : adj.IsQuillenAdjunction := ScalarCompatibility.scalar_isQuillen (B := B) _
  let _ : IsCofibrant ((Q (I := I)).obj X) :=
    Replacement.isCofibrant_cofibrantReplacement (B := B) X
  let e : ((H (I := I)).obj ((S (I := I)).obj ((Q (I := I)).obj X)) ⟶
      (H (I := I)).obj E) ≃
      ((H (I := I)).obj X ⟶ (H (I := I)).obj (R.obj E)) :=
    (Iso.homCongr
      ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := I)).app X)
      (Iso.refl _)).trans
      ((QuillenOrdinaryHoHom.homEquiv adj ((Q (I := I)).obj X) E).trans
        (Iso.homCongr
          ((Replacement.cofibrantReplacementProjectionIso (B := B) (A := I)).app X)
          (Iso.refl _)))
  have hUnique := (toZero_omegaTests_iff s X).mp hX (R.obj E)
    (cotensor_isOmega (B := B) s PointedCGWH.sphereOne E hE)
  exact ⟨fun g h => e.injective (hUnique.elim (e g) (e h))⟩

section Symmetric

private abbrev SymC := Actual.SymmetricCarrier.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev QS := Replacement.cofibrantReplacement (B := B) (A := J.{u, v})
private abbrev SS := OriginalISuspension.suspension (B := B) (I := J.{u, v})

omit B in
/-- The complete restricted integer functor is the actual original symmetric integer functor. -/
theorem symmetricIntegerPiFunctor_eq_actual (q : ℤ) :
    NativeStableCofiberIntegerMaps.integerPiFunctor
        CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor q =
      Actual.SymmetricIntegerHomotopy.integerPiFunctor q := rfl

/-- Every integer map of the unchanged symmetric comparison representative is actually Iso. -/
theorem symmetricOriginalComparisonRepresentative_all_integer_isIso
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (q : ℤ) :
    IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map
      (NativeFiberCofiberIntegerComparison.homRepresentative
        ((OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F))) := by
  rw [← symmetricIntegerPiFunctor_eq_actual]
  exact originalComparisonRepresentative_all_integer_isIso
    CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorIndexFunctor
    Actual.symmetricFamily a ha F q

/-- Actual first-free-zero-sphere delooping reflects tests of the same suspended-Q collapse. -/
theorem symmetricSuspensionQCollapse_omegaTests_iff (X : SymC.{u, v}) :
    omegaTests Actual.symmetricFamily (Diagrams.toZero (SS.obj (QS.obj X))) ↔
      omegaTests Actual.symmetricFamily (Diagrams.toZero X) := by
  constructor
  · intro h
    apply (toZero_omegaTests_iff Actual.symmetricFamily X).mpr
    intro E hE
    let e := NativeOmegaRecovery.NativeSymmetricDelooping.negativeHomEquiv (B := B) X E hE
    have hUnique := (toZero_omegaTests_iff Actual.symmetricFamily _).mp h
      (NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping.obj E)
      (NativeOmegaRecovery.NativeSymmetricDelooping.firstDelooping_isOmega E hE)
    exact ⟨fun g k => e.symm.injective (hUnique.elim (e.symm g) (e.symm k))⟩
  · exact suspensionQCollapse_omegaTests Actual.symmetricFamily X

/-- Every original integer cofiber comparison image is the unchanged caller-fiber null class. -/
theorem symmetricOriginalComparison_image_eq_null
    (a : ∀ F : Arrow SymC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (hW : omegaTests Actual.symmetricFamily F.obj.hom)
    (E : SymC.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom.test (B := B) q
      ((CofiberNullity.cofiberQ (B := B) (I := J.{u, v})).obj F.obj) E) :
    PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison.cofiberToFiberHom
        (B := B) a ha q F E hE g =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt
        ((PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target (q + 1)).obj E) := by
  have hn := CofiberNullity.cofiberQHom_eq_null (B := B) Actual.symmetricFamily
    F.obj.hom hW ((PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target q).obj E)
    (PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target_isOmega (B := B) q E hE) g
  rw [hn]
  exact PointedCGWH.Spectra.Symmetric.Stable.FiberHomComparison.cofiberToFiberHom_null
    (B := B) a ha q F E hE

/-- The actual caller-fiber collapse test detects weakness of the whole K-right arrow. -/
theorem symmetricChosenFiberCollapse_omegaTests_implies
    {X Y : SymC.{u, v}} (p : X ⟶ Y) (hp : (generators Actual.symmetricFamily).rlp p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (hTests : omegaTests Actual.symmetricFamily c.snd) : omegaTests Actual.symmetricFamily p := by
  have hLevel := PointedCGWH.Spectra.NativeStable.symmetric_chosenFiber_levelTrivialFibration
    (B := B) p hp c hc hTests
  have hI := Native.Data.generatorsI_rlp.ge p hLevel.1
  exact (levelI_right_le_KRight_omegaTests Actual.symmetricFamily p hI).2

end Symmetric

section Orthogonal

private abbrev OrthC := Actual.OrthogonalCarrier.{u, v}
private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev QO := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev SO := OriginalISuspension.suspension (B := B) (I := O.{u, v})

/-- Every integer map of the same original orthogonal comparison representative is Iso. -/
theorem orthogonalOriginalComparisonRepresentative_all_integer_isIso
    (a : ∀ F : Arrow OrthC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.orthogonalFamily).FullSubcategory)
    (q : ℤ) :
    IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map
      (NativeFiberCofiberIntegerComparison.homRepresentative
        ((OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.orthogonalFamily).app F))) := by
  rw [← orthogonalIntegerPiFunctor_eq_actual]
  exact originalComparisonRepresentative_all_integer_isIso
    CategoryTheory.Spectra.SpectrumIndexMaps.sequentialOrthogonalOperatorIndexFunctor
    Actual.orthogonalFamily a ha F q

/-- Actual native right-shift delooping reflects tests of the original suspended-Q collapse. -/
theorem orthogonalSuspensionQCollapse_omegaTests_iff (X : OrthC.{u, v}) :
    omegaTests Actual.orthogonalFamily (Diagrams.toZero (SO.obj (QO.obj X))) ↔
      omegaTests Actual.orthogonalFamily (Diagrams.toZero X) := by
  constructor
  · intro h
    apply (toZero_omegaTests_iff Actual.orthogonalFamily X).mpr
    intro E hE
    let e := PointedCGWH.Spectra.Orthogonal.NegativeHomTests.negativeHomEquiv
      (B := B) 0 X E hE
    have hUnique := (toZero_omegaTests_iff Actual.orthogonalFamily _).mp h
      ((PointedCGWH.Spectra.Orthogonal.NegativeHomTests.deloopTarget 1).obj E)
      (PointedCGWH.Spectra.Orthogonal.NegativeHomTests.deloopTarget_isOmega 1 E hE)
    exact ⟨fun g k => e.symm.injective (hUnique.elim (e.symm g) (e.symm k))⟩
  · exact suspensionQCollapse_omegaTests Actual.orthogonalFamily X

/-- Every integer original orthogonal comparison image is the same caller-fiber null class. -/
theorem orthogonalOriginalComparison_image_eq_null
    (a : ∀ F : Arrow OrthC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.rightArrows.{u, v})
    (hW : omegaTests Actual.orthogonalFamily F.obj.hom)
    (E : OrthC.{u, v}) (hE : IsOmega Actual.orthogonalFamily E)
    (g : PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.cofiberHom (B := B) q F E) :
    PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.comparisonTest
        (B := B) a ha q F E hE g =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt
        ((PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget (q + 1)).obj E) := by
  have hn := CofiberNullity.cofiberQHom_eq_null (B := B) Actual.orthogonalFamily
    F.obj.hom hW ((PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget q).obj E)
    (PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget_isOmega q E hE) g
  rw [hn]
  exact PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests.comparisonTest_null
    (B := B) a ha q F E hE

/-- Original paired K-rightness and its caller collapse test imply the full original weak class. -/
theorem orthogonalChosenFiberCollapse_omegaTests_implies
    {X Y : OrthC.{u, v}} (p : X ⟶ Y) (hp : (generators Actual.orthogonalFamily).rlp p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (hTests : omegaTests Actual.orthogonalFamily c.snd) : omegaTests Actual.orthogonalFamily p := by
  have hLevel := PointedCGWH.Spectra.NativeStable.orthogonal_chosenFiber_levelTrivialFibration
    (B := B) p hp c hc hTests
  have hI := Native.Data.generatorsI_rlp.ge p hLevel.1
  exact (levelI_right_le_KRight_omegaTests Actual.orthogonalFamily p hI).2

private abbrev HO := toHomotopyCategory OrthC.{u, v}
private abbrev CQO := CofiberNullity.cofiberQ (B := B) (I := O.{u, v})

/-- The same original K-right comparison passes every actual orthogonal Omega Hom test. -/
theorem orthogonalOriginalComparison_omegaTests
    (a : ∀ F : Arrow OrthC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.orthogonalFamily).FullSubcategory)
    (E : OrthC.{u, v}) (hE : IsOmega Actual.orthogonalFamily E) :
    Function.Bijective
      (fun g : HO.obj (CQO.obj F.obj) ⟶ HO.obj E =>
        (OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.orthogonalFamily).app F ≫ g) := by
  let ψ := (OriginalFiberComparison.originalComparison (B := B)
    a ha Actual.orthogonalFamily).app F
  have hRaw : omegaTests Actual.orthogonalFamily
      (NativeFiberCofiberIntegerComparison.homRepresentative ψ) :=
    PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration.integerIsos_imply_omegaTests
      (NativeFiberCofiberIntegerComparison.homRepresentative ψ)
      (fun q => orthogonalOriginalComparisonRepresentative_all_integer_isIso a ha F q)
  exact (NativeFiberCofiberIntegerComparison.homRepresentative_omegaTests_iff
    Actual.orthogonalFamily ψ).mp hRaw E hE

/-- The original comparison supplies the complete interface used by the older clients. -/
theorem orthogonalComparisonHomBijections :
    PointedCGWH.Spectra.Orthogonal.ConditionalFiberHom.ComparisonHomBijections (B := B) :=
  fun a ha F E hE => orthogonalOriginalComparison_omegaTests a ha F E hE

/-- Original comparison surjectivity and the same Q-cofiber nullity give the actual collapse. -/
theorem orthogonalChosenFiberCollapse_omegaTests_of_choices
    (a : ∀ F : Arrow OrthC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.orthogonalFamily).FullSubcategory)
    (hW : omegaTests Actual.orthogonalFamily F.obj.hom) :
    omegaTests Actual.orthogonalFamily (a F.obj).snd := by
  have hS : omegaTests Actual.orthogonalFamily
      (Diagrams.toZero (SO.obj (QO.obj (a F.obj).pt))) := by
    apply (toZero_omegaTests_iff Actual.orthogonalFamily _).mpr
    intro E hE
    have hTest := orthogonalOriginalComparison_omegaTests a ha F E hE
    let ψ : HO.obj (SO.obj (QO.obj (a F.obj).pt)) ⟶ HO.obj (CQO.obj F.obj) :=
      (OriginalFiberComparison.originalComparison (B := B)
        a ha Actual.orthogonalFamily).app F
    have hNull : ∀ g : HO.obj (SO.obj (QO.obj (a F.obj).pt)) ⟶ HO.obj E,
        g = OrdinaryHoCofiberKernel.nullHom (SO.obj (QO.obj (a F.obj).pt)) E := by
      intro g
      obtain ⟨k, hk⟩ := hTest.2 g
      have hkNull := CofiberNullity.cofiberQHom_eq_null (B := B)
        Actual.orthogonalFamily F.obj.hom hW E hE k
      rw [← hk, hkNull]
      exact nativeHom_null_precomp ψ
    exact ⟨fun g k => (hNull g).trans (hNull k).symm⟩
  have hF := (orthogonalSuspensionQCollapse_omegaTests_iff (a F.obj).pt).mp hS
  have hCollapse : (a F.obj).snd = Diagrams.toZero (a F.obj).pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse]
  exact hF

/-- Every caller-chosen limiting orthogonal fiber retains its original collapse and all tests. -/
theorem orthogonalChosenFiberCollapse_omegaTests
    {X Y : OrthC.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.orthogonalFamily).rlp p)
    (hW : omegaTests Actual.orthogonalFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    omegaTests Actual.orthogonalFamily c.snd := by
  let a : ∀ F : Arrow OrthC.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right) :=
    fun F => Diagrams.FiberGeometry.fiberCone F.hom
  let ha : ∀ F, IsLimit (a F) :=
    fun F => Diagrams.FiberGeometry.fiberConeIsLimit F.hom
  let F : (OriginalFiberComparison.rightArrowProperty Actual.orthogonalFamily).FullSubcategory :=
    ⟨Arrow.mk p, hp⟩
  have hCanonical : omegaTests Actual.orthogonalFamily (Diagrams.FiberGeometry.fiberToZero p) :=
    orthogonalChosenFiberCollapse_omegaTests_of_choices a ha F hW
  exact (OriginalFiberComparison.chosenFiberCollapse_omegaTests_iff
    Actual.orthogonalFamily p c hc).mpr hCanonical

/-- The actual chosen collapse and original K-right arrow have precisely the same weak tests. -/
theorem orthogonalChosenFiberCollapse_omegaTests_iff
    {X Y : OrthC.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.orthogonalFamily).rlp p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    omegaTests Actual.orthogonalFamily p ↔ omegaTests Actual.orthogonalFamily c.snd :=
  ⟨fun hW => orthogonalChosenFiberCollapse_omegaTests p hp hW c hc,
    orthogonalChosenFiberCollapse_omegaTests_implies p hp c hc⟩

/-- All ordinary level-Ho maps from the caller fiber to an actual Omega target are null. -/
theorem orthogonalChosenFiberHom_eq_null
    {X Y : OrthC.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.orthogonalFamily).rlp p)
    (hW : omegaTests Actual.orthogonalFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (E : OrthC.{u, v}) (hE : IsOmega Actual.orthogonalFamily E)
    (g : HO.obj c.pt ⟶ HO.obj E) :
    g = OrdinaryHoCofiberKernel.nullHom c.pt E := by
  have hTests := orthogonalChosenFiberCollapse_omegaTests p hp hW c hc
  have hCollapse : c.snd = Diagrams.toZero c.pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse] at hTests
  have hUnique := (toZero_omegaTests_iff Actual.orthogonalFamily c.pt).mp hTests E hE
  exact hUnique.elim _ _

/-- Every genuine integer target keeps the same caller fiber and original null class. -/
theorem orthogonalChosenFiberIntegerHom_eq_null
    {X Y : OrthC.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.orthogonalFamily).rlp p)
    (hW : omegaTests Actual.orthogonalFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (q : ℤ) (E : OrthC.{u, v}) (hE : IsOmega Actual.orthogonalFamily E)
    (g : HO.obj c.pt ⟶
      HO.obj ((PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget q).obj E)) :
    g = OrdinaryHoCofiberKernel.nullHom c.pt
      ((PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget q).obj E) :=
  orthogonalChosenFiberHom_eq_null p hp hW c hc _
    (PointedCGWH.Spectra.Orthogonal.IntegerTargetTests.integerTarget_isOmega q E hE) g

end Orthogonal

end OriginalFiberNullity
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
