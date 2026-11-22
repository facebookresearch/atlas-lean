/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableFiberHomNullity
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricFiberBoundaryComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaDetectionClosed
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableGeneratorClasses

/-!
# The original symmetric comparison, fiber nullity and stable classes

The genuine original integer-isomorphism detector proves every original
comparison Hom bijection. Its inverse retains all integer targets,
source and target maps, both caller limit choices and all three exact
fiber-Hom positions. The original Q-cofiber nullity then gives the same
caller-fiber collapse tests and the literal original I/K class equalities.
The original carrier, cardinal, bottom and whole K factor records remain.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory ZeroObject

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
namespace OriginalFiberNullity

open PointedCGWH.Spectra.Symmetric.Stable

attribute [local instance] Native.modelCategory Native.allObjectsFibrant

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev RecognitionCarrier := Actual.SymmetricCarrier.{u, v}
private abbrev RecognitionIndex := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev RecognitionHo := toHomotopyCategory RecognitionCarrier.{u, v}
private abbrev RecognitionQ := Replacement.cofibrantReplacement (B := B) (A := RecognitionIndex.{u, v})
private abbrev RecognitionSuspension := OriginalISuspension.suspension (B := B) (I := RecognitionIndex.{u, v})
private abbrev RecognitionCofiber := CofiberNullity.cofiberQ (B := B) (I := RecognitionIndex.{u, v})

/-- The actual original Q representative retains every precomposition test of the same comparison. -/
theorem symmetricOriginalComparisonRepresentative_precomp_bijective_iff
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) :
    Function.Bijective
        (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj E =>
          (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F ≫ g) ↔
      Function.Bijective
        (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj E =>
          RecognitionHo.map (NativeFiberCofiberIntegerComparison.homRepresentative
            ((OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F)) ≫ g) :=
  NativeFiberCofiberIntegerComparison.homRepresentative_precomp_bijective_iff
    ((OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F) E

/-- All Omega tests of the original representative are exactly all original comparison Hom tests. -/
theorem symmetricOriginalComparisonRepresentative_omegaTests_iff
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    omegaTests Actual.symmetricFamily
        (NativeFiberCofiberIntegerComparison.homRepresentative
          ((OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F)) ↔
      ∀ (E : RecognitionCarrier.{u, v}), IsOmega Actual.symmetricFamily E →
        Function.Bijective
          (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj E =>
            (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F ≫ g) :=
  NativeFiberCofiberIntegerComparison.homRepresentative_omegaTests_iff Actual.symmetricFamily
    ((OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F)

/-- The same original representative is tested by every genuine integer fiber Hom function. -/
theorem symmetricOriginalComparisonRepresentative_omegaTests_iff_integerHomBijections
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory) :
    omegaTests Actual.symmetricFamily
        (NativeFiberCofiberIntegerComparison.homRepresentative
          ((OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F)) ↔
      ∀ (q : ℤ) (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E),
        Function.Bijective (FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE) := by
  refine (symmetricOriginalComparisonRepresentative_omegaTests_iff a ha F).trans ?_
  let ψ : RecognitionHo.obj (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt)) ⟶
      RecognitionHo.obj (RecognitionCofiber.obj F.obj) :=
    (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F
  constructor
  · intro h q E hE
    let M := ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE
    have hψ : Function.Bijective
        (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶
          RecognitionHo.obj ((ShiftedTargets.target q).obj E) => ψ ≫ g) :=
      h ((ShiftedTargets.target q).obj E) (ShiftedTargets.target_isOmega (B := B) q E hE)
    exact M.bijective.comp hψ
  · intro h E hE
    let M := ShiftedHom.suspensionHomEquiv (B := B) 0 (a F.obj).pt E hE
    let r := FiberHomComparison.cofiberToFiberHom (B := B) a ha 0 F E hE
    have hInverse : (fun g => M.symm (r g)) =
        (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj E => ψ ≫ g) :=
      funext (fun g => FiberHomComparison.cofiberToFiberHom_inverseShift
        (B := B) a ha 0 F E hE g)
    exact hInverse ▸ M.symm.bijective.comp (h 0 E hE)

/-- Original I-rightness is exactly test-nullity of the same limiting fiber of a K-right map. -/
theorem symmetricChosenFiberCollapse_omegaTests_iff_levelIRight
    {X Y : RecognitionCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.symmetricFamily).rlp p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    (levelI (I := RecognitionIndex)).rlp p ↔ omegaTests Actual.symmetricFamily c.snd := by
  constructor
  · intro hI
    have hFiberI : (levelI (I := RecognitionIndex)).rlp c.snd :=
      CategoryTheory.MorphismProperty.of_isPullback (IsPullback.of_isLimit hc) hI
    exact (levelI_right_le_KRight_omegaTests Actual.symmetricFamily c.snd hFiberI).2
  · intro hTests
    have hLevel := PointedCGWH.Spectra.NativeStable.symmetric_chosenFiber_levelTrivialFibration
      (B := B) p hp c hc hTests
    exact Native.Data.generatorsI_rlp.ge p hLevel.1

/-- This boundary is the genuine closed detector on the unchanged original native carrier.
It is instantiated by the actual supplier, rather than supplied by the caller of a final result. -/
private def actualClosedDetectorχ {X Y : RecognitionCarrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    omegaTests Actual.symmetricFamily f :=
  PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests.integerIsos_imply_omegaTests.{u, v}
    f hPi

/-- The same original K-right comparison passes every actual symmetric Omega Hom test. -/
theorem symmetricOriginalComparison_omegaTests
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : IsOmega Actual.symmetricFamily E) :
    Function.Bijective
      (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj E =>
        (OriginalFiberComparison.originalComparison (B := B)
          a ha Actual.symmetricFamily).app F ≫ g) := by
  let ψ := (OriginalFiberComparison.originalComparison (B := B)
    a ha Actual.symmetricFamily).app F
  have hRaw : omegaTests Actual.symmetricFamily
      (NativeFiberCofiberIntegerComparison.homRepresentative ψ) :=
    actualClosedDetectorχ (NativeFiberCofiberIntegerComparison.homRepresentative ψ)
      (fun q => symmetricOriginalComparisonRepresentative_all_integer_isIso a ha F q)
  exact (symmetricOriginalComparisonRepresentative_omegaTests_iff a ha F).mp hRaw E hE

/-- Original comparison surjectivity and the same Q-cofiber nullity give the actual collapse. -/
theorem symmetricChosenFiberCollapse_omegaTests_of_choices
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (hW : omegaTests Actual.symmetricFamily F.obj.hom) :
    omegaTests Actual.symmetricFamily (a F.obj).snd := by
  have hS : omegaTests Actual.symmetricFamily
      (Diagrams.toZero (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt))) := by
    apply (toZero_omegaTests_iff Actual.symmetricFamily _).mpr
    intro E hE
    have hTest := symmetricOriginalComparison_omegaTests a ha F E hE
    let ψ : RecognitionHo.obj (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt)) ⟶ RecognitionHo.obj
      (RecognitionCofiber.obj F.obj) :=
      (OriginalFiberComparison.originalComparison (B := B)
        a ha Actual.symmetricFamily).app F
    have hNull : ∀ g : RecognitionHo.obj (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt)) ⟶ RecognitionHo.obj
      E,
        g = OrdinaryHoCofiberKernel.nullHom (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt)) E := by
      intro g
      obtain ⟨k, hk⟩ := hTest.2 g
      have hkNull := CofiberNullity.cofiberQHom_eq_null (B := B)
        Actual.symmetricFamily F.obj.hom hW E hE k
      rw [← hk, hkNull]
      exact nativeHom_null_precomp ψ
    exact ⟨fun g k => (hNull g).trans (hNull k).symm⟩
  have hF := (symmetricSuspensionQCollapse_omegaTests_iff (a F.obj).pt).mp hS
  have hCollapse : (a F.obj).snd = Diagrams.toZero (a F.obj).pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse]
  exact hF

/-- Every caller-chosen limiting symmetric fiber retains its original collapse and all tests. -/
theorem symmetricChosenFiberCollapse_omegaTests
    {X Y : RecognitionCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.symmetricFamily).rlp p)
    (hW : omegaTests Actual.symmetricFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    omegaTests Actual.symmetricFamily c.snd := by
  let a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right) :=
    fun F => Diagrams.FiberGeometry.fiberCone F.hom
  let ha : ∀ F, IsLimit (a F) :=
    fun F => Diagrams.FiberGeometry.fiberConeIsLimit F.hom
  let F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory :=
    ⟨Arrow.mk p, hp⟩
  have hCanonical : omegaTests Actual.symmetricFamily (Diagrams.FiberGeometry.fiberToZero p) :=
    symmetricChosenFiberCollapse_omegaTests_of_choices a ha F hW
  exact (OriginalFiberComparison.chosenFiberCollapse_omegaTests_iff
    Actual.symmetricFamily p c hc).mpr hCanonical

/-- The actual chosen collapse and original K-right arrow have precisely the same weak tests. -/
theorem symmetricChosenFiberCollapse_omegaTests_iff
    {X Y : RecognitionCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.symmetricFamily).rlp p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    omegaTests Actual.symmetricFamily p ↔ omegaTests Actual.symmetricFamily c.snd :=
  ⟨fun hW => symmetricChosenFiberCollapse_omegaTests p hp hW c hc,
    symmetricChosenFiberCollapse_omegaTests_implies p hp c hc⟩

/-- All ordinary level-Ho maps from the caller fiber to an actual Omega target are null. -/
theorem symmetricChosenFiberHom_eq_null
    {X Y : RecognitionCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.symmetricFamily).rlp p)
    (hW : omegaTests Actual.symmetricFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (E : RecognitionCarrier.{u, v}) (hE : IsOmega Actual.symmetricFamily E)
    (g : RecognitionHo.obj c.pt ⟶ RecognitionHo.obj E) :
    g = OrdinaryHoCofiberKernel.nullHom c.pt E := by
  have hTests := symmetricChosenFiberCollapse_omegaTests p hp hW c hc
  have hCollapse : c.snd = Diagrams.toZero c.pt :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  rw [hCollapse] at hTests
  have hUnique := (toZero_omegaTests_iff Actual.symmetricFamily c.pt).mp hTests E hE
  exact hUnique.elim _ _

/-- Every genuine integer target keeps the same caller fiber and original null class. -/
theorem symmetricChosenFiberIntegerHom_eq_null
    {X Y : RecognitionCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (generators Actual.symmetricFamily).rlp p)
    (hW : omegaTests Actual.symmetricFamily p)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
    (q : ℤ) (E : RecognitionCarrier.{u, v}) (hE : IsOmega Actual.symmetricFamily E)
    (g : RecognitionHo.obj c.pt ⟶
      RecognitionHo.obj ((PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target q).obj E)) :
    g = OrdinaryHoCofiberKernel.nullHom c.pt
      ((PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target q).obj E) :=
  symmetricChosenFiberHom_eq_null p hp hW c hc _
    (PointedCGWH.Spectra.Symmetric.Stable.ShiftedTargets.target_isOmega q E hE) g


/-- Every original integer cofiber-to-fiber Hom function is bijective at full Omega targets. -/
theorem symmetricCofiberToFiberHom_bijective
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Function.Bijective (FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE) := by
  let ψ : RecognitionHo.obj (RecognitionSuspension.obj (RecognitionQ.obj (a F.obj).pt)) ⟶ RecognitionHo.obj
    (RecognitionCofiber.obj F.obj) :=
    (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F
  let M := ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE
  have hψ : Function.Bijective
      (fun g : RecognitionHo.obj (RecognitionCofiber.obj F.obj) ⟶ RecognitionHo.obj ((ShiftedTargets.target q).obj E) =>
        ψ ≫ g) :=
    symmetricOriginalComparison_omegaTests a ha F ((ShiftedTargets.target q).obj E)
      (ShiftedTargets.target_isOmega (B := B) q E hE)
  exact M.bijective.comp hψ

/-- The complete original comparison is an equivalence in every integer Hom degree. -/
def symmetricCofiberToFiberHomEquiv
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E ≃
      ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E :=
  Equiv.ofBijective (FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE)
    (symmetricCofiberToFiberHom_bijective a ha q F E hE)

variable (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- The entire forward function is the same original suspended-fiber comparison test. -/
theorem symmetricCofiberToFiberHomEquiv_apply (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E) :
    symmetricCofiberToFiberHomEquiv a ha q F E hE g =
      FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE g := rfl

/-- The inverse retains the original comparison and the actual inverse suspension shift. -/
theorem symmetricCofiberToFiberHomEquiv_symm_spec (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    (OriginalFiberComparison.originalComparison (B := B) a ha Actual.symmetricFamily).app F ≫
        (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm g =
      (ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE).symm g := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  exact (FiberHomComparison.cofiberToFiberHom_inverseShift
    (B := B) a ha q F E hE (e.symm g)).symm.trans
      (congrArg (ShiftedHom.suspensionHomEquiv (B := B) q (a F.obj).pt E hE).symm
        (e.apply_symm_apply g))

/-- The same inverse recovers every actual original cofiber Hom class. -/
theorem symmetricCofiberToFiberHomEquiv_symm_comparison (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm
        (FiberHomComparison.cofiberToFiberHom (B := B) a ha q F E hE g) = g :=
  (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm_apply_apply g

/-- Both original null classes are retained by the whole forward equivalence. -/
theorem symmetricCofiberToFiberHomEquiv_null (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    symmetricCofiberToFiberHomEquiv a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (RecognitionCofiber.obj F.obj) ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E) :=
  FiberHomComparison.cofiberToFiberHom_null (B := B) a ha q F E hE

/-- The entire inverse retains the same actual caller-fiber and cofiber null classes. -/
theorem symmetricCofiberToFiberHomEquiv_symm_null (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (RecognitionCofiber.obj F.obj) ((ShiftedTargets.target q).obj E) := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  exact (congrArg e.symm (symmetricCofiberToFiberHomEquiv_null a ha q F E hE)).symm.trans
    (e.symm_apply_apply _)

/-- Every original K-right Arrow square acts on the entire forward comparison. -/
theorem symmetricCofiberToFiberHomEquiv_source (q : ℤ)
    {F G : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory}
    (φ : F ⟶ G) (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj G.obj) E) :
    symmetricCofiberToFiberHomEquiv a ha q F E hE (RecognitionHo.map (RecognitionCofiber.map φ.hom) ≫ g) =
      RecognitionHo.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
        (a F.obj) (a G.obj) (ha G.obj)) ≫ symmetricCofiberToFiberHomEquiv a ha q G E hE g :=
  FiberHomComparison.cofiberToFiberHom_source (B := B) a ha q φ E hE g

/-- Every whole original chosen-fiber map acts on the complete inverse comparison. -/
theorem symmetricCofiberToFiberHomEquiv_symm_source (q : ℤ)
    {F G : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory}
    (φ : F ⟶ G) (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a G.obj).pt E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm
        (RecognitionHo.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
          (a F.obj) (a G.obj) (ha G.obj)) ≫ g) =
      RecognitionHo.map (RecognitionCofiber.map φ.hom) ≫ (symmetricCofiberToFiberHomEquiv a ha q G E hE).symm g := by
  let eF := symmetricCofiberToFiberHomEquiv a ha q F E hE
  let eG := symmetricCofiberToFiberHomEquiv a ha q G E hE
  apply eF.injective
  have h := symmetricCofiberToFiberHomEquiv_source a ha q φ E hE (eG.symm g)
  simpa only [eF, eG, Equiv.apply_symm_apply] using h.symm

/-- Every original map between full Omega targets retains both integer target functors. -/
theorem symmetricCofiberToFiberHomEquiv_target (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    {E E' : RecognitionCarrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E) :
    symmetricCofiberToFiberHomEquiv a ha q F E' hE'
        (g ≫ RecognitionHo.map ((ShiftedTargets.target q).map t)) =
      symmetricCofiberToFiberHomEquiv a ha q F E hE g ≫
        RecognitionHo.map ((ShiftedTargets.target (q + 1)).map t) :=
  FiberHomComparison.cofiberToFiberHom_target (B := B) a ha q F hE hE' t g

/-- The complete inverse retains the same two actual integer target-map actions. -/
theorem symmetricCofiberToFiberHomEquiv_symm_target (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    {E E' : RecognitionCarrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E' hE').symm
        (g ≫ RecognitionHo.map ((ShiftedTargets.target (q + 1)).map t)) =
      (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm g ≫
        RecognitionHo.map ((ShiftedTargets.target q).map t) := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  let e' := symmetricCofiberToFiberHomEquiv a ha q F E' hE'
  apply e'.injective
  have h := symmetricCofiberToFiberHomEquiv_target a ha q F hE hE' t (e.symm g)
  simpa only [e, e', Equiv.apply_symm_apply] using h.symm

/-- The whole actual equivalence sends the original boundary to the unchanged caller fst. -/
theorem symmetricCofiberToFiberHomEquiv_connecting (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) F.obj.left E) :
    symmetricCofiberToFiberHomEquiv a ha q F E hE
        (ShiftedPuppeTests.connecting (B := B) q F.obj E hE g) = RecognitionHo.map (a F.obj).fst ≫ g :=
  OriginalFiberBoundary.symmetricCofiberToFiberHom_connecting a ha q F E hE g

/-- The entire inverse recovers the same original cofiber boundary from the caller fst. -/
theorem symmetricCofiberToFiberHomEquiv_symm_fiberRestriction (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) F.obj.left E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm (RecognitionHo.map (a F.obj).fst ≫ g) =
      ShiftedPuppeTests.connecting (B := B) q F.obj E hE g := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  exact (congrArg e.symm
    (symmetricCofiberToFiberHomEquiv_connecting a ha q F E hE g)).symm.trans
      (e.symm_apply_apply _)

variable (b : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Both arbitrary full caller-fiber families retain the entire forward equivalence. -/
theorem symmetricCofiberToFiberHomEquiv_choice (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E) :
    RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫
        symmetricCofiberToFiberHomEquiv b hb q F E hE g =
      symmetricCofiberToFiberHomEquiv a ha q F E hE g :=
  FiberHomComparison.cofiberToFiberHom_choice (B := B) a ha b hb q F E hE g

/-- The inverse also retains the whole forward map of the original caller limit comparison. -/
theorem symmetricCofiberToFiberHomEquiv_symm_choice (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (b F.obj).pt E) :
    (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm
        (RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
          Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫ g) =
      (symmetricCofiberToFiberHomEquiv b hb q F E hE).symm g := by
  let ea := symmetricCofiberToFiberHomEquiv a ha q F E hE
  let eb := symmetricCofiberToFiberHomEquiv b hb q F E hE
  apply ea.injective
  have h := symmetricCofiberToFiberHomEquiv_choice a ha b hb q F E hE (eb.symm g)
  simpa only [ea, eb, Equiv.apply_symm_apply] using h

/-- The original inverse caller limit map retains the same forward comparison. -/
theorem symmetricCofiberToFiberHomEquiv_choice_inv (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q (RecognitionCofiber.obj F.obj) E) :
    RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
      Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv ≫
        symmetricCofiberToFiberHomEquiv a ha q F E hE g =
      symmetricCofiberToFiberHomEquiv b hb q F E hE g :=
  FiberHomComparison.cofiberToFiberHom_choice_inv (B := B) a ha b hb q F E hE g

/-- Both complete inverse functions retain the inverse original caller limit map. -/
theorem symmetricCofiberToFiberHomEquiv_symm_choice_inv (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    (symmetricCofiberToFiberHomEquiv b hb q F E hE).symm
        (RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
          Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv ≫ g) =
      (symmetricCofiberToFiberHomEquiv a ha q F E hE).symm g := by
  let ea := symmetricCofiberToFiberHomEquiv a ha q F E hE
  let eb := symmetricCofiberToFiberHomEquiv b hb q F E hE
  apply eb.injective
  have h := symmetricCofiberToFiberHomEquiv_choice_inv a ha b hb q F E hE (ea.symm g)
  simpa only [ea, eb, Equiv.apply_symm_apply] using h

/-- Every caller RecognitionQ-cofiber and its entire original comparison give the same full Hom equivalence. -/
def symmetricChosenCofiberToFiberHomEquiv
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (d : ∀ F : Arrow RecognitionCarrier.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := RecognitionIndex)).app F.left) F.hom)
    (hd : ∀ F, IsColimit (d F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) q ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E ≃
      ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E :=
  (ChosenCofiberTests.testHomEquiv (B := B) d hd q F.obj E).trans
    (symmetricCofiberToFiberHomEquiv a ha q F E hE)

/-- Its entire forward function is the original caller-cofiber to caller-fiber Hom function. -/
theorem symmetricChosenCofiberToFiberHomEquiv_apply
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (d : ∀ F : Arrow RecognitionCarrier.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := RecognitionIndex)).app F.left) F.hom)
    (hd : ∀ F, IsColimit (d F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q
      ((ChosenCofiberTests.chosenCofiber (B := B) d hd).obj F.obj) E) :
    symmetricChosenCofiberToFiberHomEquiv a ha d hd q F E hE g =
      FiberHomComparison.chosenCofiberToFiberHom (B := B) a ha d hd q F E hE g := rfl

/-- Every original caller cofiber-to-fiber Hom function is bijective, with all choices retained. -/
theorem symmetricChosenCofiberToFiberHom_bijective
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F))
    (d : ∀ F : Arrow RecognitionCarrier.{u, v}, PushoutCocone
      ((OriginalICone.inclusion (B := B) (I := RecognitionIndex)).app F.left) F.hom)
    (hd : ∀ F, IsColimit (d F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    Function.Bijective (FiberHomComparison.chosenCofiberToFiberHom
      (B := B) a ha d hd q F E hE) :=
  (symmetricChosenCofiberToFiberHomEquiv a ha d hd q F E hE).bijective

/-- The complete fiber connecting function uses the original inverse comparison and target leg. -/
def symmetricFiberHomConnecting
    (a : ∀ F : Arrow RecognitionCarrier.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
    (ha : ∀ F, IsLimit (a F)) (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E →
      ShiftedHom.test (B := B) q F.obj.right E :=
  fun g => ShiftedPuppeTests.targetRestriction (B := B) q F.obj E
    ((symmetricCofiberToFiberHomEquiv a ha q F E hE).symm g)

/-- The original base term is exact with the unchanged original arrow in every integer degree. -/
theorem symmetricFiberHom_exact_at_base (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) q F.obj.right E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E,
      symmetricFiberHomConnecting a ha q F E hE h = g) ↔
      ShiftedPuppeTests.sourceRestriction (B := B) q F.obj E g =
        OrdinaryHoCofiberKernel.nullHom F.obj.left ((ShiftedTargets.target q).obj E) := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  constructor
  · rintro ⟨h, hh⟩
    exact (ShiftedPuppeTests.exact_at_target (B := B) q F.obj E g).mp ⟨e.symm h, hh⟩
  · intro h
    obtain ⟨k, hk⟩ := (ShiftedPuppeTests.exact_at_target (B := B) q F.obj E g).mpr h
    refine ⟨e k, ?_⟩
    exact (congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E)
      (e.symm_apply_apply k)).trans hk

/-- The caller fiber term is exact for its same first projection and original connecting map. -/
theorem symmetricFiberHom_exact_at_fiber (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.obj.left E,
      RecognitionHo.map (a F.obj).fst ≫ h = g) ↔
      symmetricFiberHomConnecting a ha q F E hE g =
        OrdinaryHoCofiberKernel.nullHom F.obj.right ((ShiftedTargets.target q).obj E) := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  refine (OriginalFiberBoundary.symmetricFiberRestriction_image_iff a ha q F E hE g).trans ?_
  constructor
  · rintro ⟨k, hk, hNull⟩
    have hpre : e.symm g = k :=
      (congrArg e.symm hk).symm.trans (e.symm_apply_apply k)
    exact (congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E) hpre).trans hNull
  · intro h
    exact ⟨e.symm g, e.apply_symm_apply g, h⟩

include ha in
/-- The shifted total term is exact for the unchanged original input arrow and caller fst. -/
theorem symmetricFiberHom_exact_at_shifted_total (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) F.obj.left E) :
    (∃ h : ShiftedHom.test (B := B) (q + 1) F.obj.right E,
      ShiftedPuppeTests.sourceRestriction (B := B) (q + 1) F.obj E h = g) ↔
      RecognitionHo.map (a F.obj).fst ≫ g =
        OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E) := by
  let e := symmetricCofiberToFiberHomEquiv a ha q F E hE
  refine (ShiftedPuppeTests.exact_at_shifted_source (B := B) q F.obj E hE g).trans ?_
  constructor
  · intro h
    exact (symmetricCofiberToFiberHomEquiv_connecting a ha q F E hE g).symm.trans
      ((congrArg e h).trans (symmetricCofiberToFiberHomEquiv_null a ha q F E hE))
  · intro h
    apply e.injective
    exact (symmetricCofiberToFiberHomEquiv_connecting a ha q F E hE g).trans
      (h.trans (symmetricCofiberToFiberHomEquiv_null a ha q F E hE).symm)

/-- Every original K-right Arrow square preserves the full fiber connecting function. -/
theorem symmetricFiberHomConnecting_source (q : ℤ)
    {F G : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory}
    (φ : F ⟶ G) (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a G.obj).pt E) :
    symmetricFiberHomConnecting a ha q F E hE
        (RecognitionHo.map (Diagrams.FiberGeometry.chosenFiberMap φ.hom
          (a F.obj) (a G.obj) (ha G.obj)) ≫ g) =
      RecognitionHo.map φ.hom.right ≫ symmetricFiberHomConnecting a ha q G E hE g := by
  exact (congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E)
    (symmetricCofiberToFiberHomEquiv_symm_source a ha q φ E hE g)).trans
      (ShiftedPuppeTests.targetRestriction_source (B := B) q φ.hom E
        ((symmetricCofiberToFiberHomEquiv a ha q G E hE).symm g))

/-- Every original Omega target map preserves both integer target actions of the connection. -/
theorem symmetricFiberHomConnecting_target (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    {E E' : RecognitionCarrier.{u, v}} (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E')
    (t : E ⟶ E') (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    symmetricFiberHomConnecting a ha q F E' hE'
        (g ≫ RecognitionHo.map ((ShiftedTargets.target (q + 1)).map t)) =
      symmetricFiberHomConnecting a ha q F E hE g ≫ RecognitionHo.map ((ShiftedTargets.target q).map t) := by
  exact (congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E')
    (symmetricCofiberToFiberHomEquiv_symm_target a ha q F hE hE' t g)).trans
      (ShiftedPuppeTests.targetRestriction_target (B := B) q F.obj t
        ((symmetricCofiberToFiberHomEquiv a ha q F E hE).symm g))

/-- The complete connecting function retains the actual original fiber and base null classes. -/
theorem symmetricFiberHomConnecting_null (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    symmetricFiberHomConnecting a ha q F E hE
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((ShiftedTargets.target (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom F.obj.right ((ShiftedTargets.target q).obj E) := by
  exact (congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E)
    (symmetricCofiberToFiberHomEquiv_symm_null a ha q F E hE)).trans
      (nativeHom_null_precomp (ShiftedPuppeTests.targetLegHo (B := B) F.obj))

/-- Both complete arbitrary caller-fiber choices retain the same original connection. -/
theorem symmetricFiberHomConnecting_choice (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (b F.obj).pt E) :
    symmetricFiberHomConnecting a ha q F E hE
        (RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
          Diagrams.zeroDiagram_isZero a ha b hb F.obj).hom ≫ g) =
      symmetricFiberHomConnecting b hb q F E hE g :=
  congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E)
    (symmetricCofiberToFiberHomEquiv_symm_choice a ha b hb q F E hE g)

/-- The whole inverse caller choice retains the original fiber connecting function as well. -/
theorem symmetricFiberHomConnecting_choice_inv (q : ℤ)
    (F : (OriginalFiberComparison.rightArrowProperty Actual.symmetricFamily).FullSubcategory)
    (E : RecognitionCarrier.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : ShiftedHom.test (B := B) (q + 1) (a F.obj).pt E) :
    symmetricFiberHomConnecting b hb q F E hE
        (RecognitionHo.map (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram
          Diagrams.zeroDiagram_isZero a ha b hb F.obj).inv ≫ g) =
      symmetricFiberHomConnecting a ha q F E hE g :=
  congrArg (ShiftedPuppeTests.targetRestriction (B := B) q F.obj E)
    (symmetricCofiberToFiberHomEquiv_symm_choice_inv a ha b hb q F E hE g)

end OriginalFiberNullity
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

namespace HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction

open OperatorStabilizationK
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev symmetricIndex := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev symmetricFamily := Actual.symmetricFamily.{u, v}
private instance symmetricFiniteLimits : HasFiniteLimits Actual.SymmetricCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := symmetricIndex)).cm1a
private instance symmetricFiniteColimits : HasFiniteColimits Actual.SymmetricCarrier.{u, v} :=
  (Native.modelCategory (B := B) (A := symmetricIndex)).cm1b

theorem symmetric_right_class_eq :
    (NativeK.levelI (I := symmetricIndex)).rlp =
      (NativeK.generators symmetricFamily).rlp ⊓ NativeK.omegaTests symmetricFamily := by
  apply le_antisymm (NativeK.levelI_right_le_KRight_omegaTests symmetricFamily)
  intro X Y p hp
  let c := Diagrams.FiberGeometry.fiberCone p
  let hc := Diagrams.FiberGeometry.fiberConeIsLimit p
  exact (NativeK.OriginalFiberNullity.symmetricChosenFiberCollapse_omegaTests_iff_levelIRight
    (B := B) p hp.1 c hc).mpr
      (NativeK.OriginalFiberNullity.symmetricChosenFiberCollapse_omegaTests
        (B := B) p hp.1 hp.2 c hc)

theorem symmetric_left_class_eq :
    (NativeK.generators symmetricFamily).rlp.llp =
      (NativeK.levelI (I := symmetricIndex)).rlp.llp ⊓ NativeK.omegaTests symmetricFamily :=
  OriginalGeneratedModel.left_class_eq
    (NativeK.levelI (I := symmetricIndex)) (NativeK.generators symmetricFamily)
    (NativeK.omegaTests symmetricFamily) inferInstance symmetric_right_class_eq
    PointedCGWH.Spectra.NativeStable.symmetricKLeft_le_omegaTests
    (NativeK.factorizationData symmetricFamily)

end HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction
