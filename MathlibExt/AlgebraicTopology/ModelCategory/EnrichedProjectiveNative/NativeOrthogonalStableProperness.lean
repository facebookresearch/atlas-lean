/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
See NOTICE in the repository root for the original attribution.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOrthogonalStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexCofibrantProperness
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOmegaHomFiveLemma
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ConditionalChosenFiberSequence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOrthogonalRawPiHEPPushoutGluing
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Full properness and original source tests of the native orthogonal stable model

The same original I factorization proves left properness on arbitrary
endpoints. Original Q-source mapping groups, the actual Omega delta and
the original caller fiber exactness prove right properness. Both caller
fibers and all integer degrees remain present. The complete original
I-source span retains every HEP, Omega and scalar test, all caller
pushouts, both source maps and their full naturality.

The actual model, independent coefficient universes, realized cardinal,
every B and the original I/K classes and factor values are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.Spectra.Orthogonal.NativeStableProperness

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := Actual.OrthogonalCarrier.{u, v}
private abbrev s := Actual.orthogonalFamily.{u, v}

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev H := toHomotopyCategory C.{u, v}

private abbrev W : CategoryTheory.MorphismProperty C.{u, v} := NativeK.omegaTests s
private abbrev Cof : CategoryTheory.MorphismProperty C.{u, v} :=
  (StableModelConstruction.orthogonalModelCategory (B := B)).categoryWithCofibrations.cofibrations

/-- The complete left pushout law uses the actual original stable classes and caller maps. -/
def LeftPushoutStatement : Prop :=
  ∀ {A X Z P : C.{u, v}} {i : A ⟶ X} {f : A ⟶ Z} {f' : X ⟶ P} {j : Z ⟶ P},
    IsPushout i f f' j → Cof i → W f → W f'

/-- Cobase change of every original stable weak arrow along an actual stable cofibration is weak. -/
theorem omegaTests_of_original_pushout
    {A X Z P : C.{u, v}} {i : A ⟶ X} {f : A ⟶ Z} {f' : X ⟶ P} {j : Z ⟶ P}
    (sq : IsPushout i f f' j) (hi : Cof i) (hf : W f) : W f' := by
  have hiLevel : cofibrations C.{u, v} i := by
    have eqCof := congrArg (fun P : CategoryTheory.MorphismProperty C.{u, v} => P i)
      (StableModelConstruction.orthogonal_cofibrations_eq_level (B := B))
    exact eqCof.mp hi
  let F : Arrow C.{u, v} := Arrow.mk f
  let data := Native.cofibrantFactorizationData (B := B) (A := O.{u, v})
  let M : C.{u, v} := data.Z.obj F
  let a : A ⟶ M := data.i.app F
  let q : M ⟶ Z := data.p.app F
  have hfac : a ≫ q = f := data.fac_app
  have ha : cofibrations C.{u, v} a := data.hi F
  have hq : trivialFibrations C.{u, v} q := data.hp F
  have hqW : W q := NativeK.levelWeak_le_omegaTests s q hq.2
  have haW : W a := by
    apply (W (B := B)).of_postcomp a q hqW
    rw [hfac]
    exact hf
  have haStable :
      (StableModelConstruction.orthogonalModelCategory (B := B)).categoryWithCofibrations.cofibrations a := by
    have eqCof := congrArg (fun P : CategoryTheory.MorphismProperty C.{u, v} => P a)
      (StableModelConstruction.orthogonal_cofibrations_eq_level (B := B))
    exact eqCof.mpr ha
  have haK : (NativeK.generators s).rlp.llp a := by
    rw [StableModelConstruction.orthogonal_left_class_eq (B := B)]
    exact ⟨haStable, haW⟩
  have hleft : (NativeK.generators s).rlp.llp (pushout.inl i a) :=
    (NativeK.generators s).rlp.llp.pushout_inl i a haK
  have hleftW : W (pushout.inl i a) :=
    PointedCGWH.Spectra.NativeStable.orthogonalKLeft_le_omegaTests _ hleft
  have hright : cofibrations C.{u, v} (pushout.inr i a) :=
    (cofibrations C.{u, v}).pushout_inr i a hiLevel
  let r : pushout i a ⟶ P :=
    pushout.desc f' (q ≫ j) (by rw [← Category.assoc, hfac]; exact sq.w)
  have hlr : pushout.inl i a ≫ r = f' := by
    dsimp only [r]
    rw [pushout.inl_desc]
  have hrr : pushout.inr i a ≫ r = q ≫ j := by
    dsimp only [r]
    rw [pushout.inr_desc]
  have outer : IsPushout i (a ≫ q) (pushout.inl i a ≫ r) j := by
    rw [hfac, hlr]
    exact sq
  have second : IsPushout (pushout.inr i a) q r j :=
    IsPushout.of_top outer hrr (IsPushout.of_hasPushout i a)
  have hrLevel : weakEquivalences C.{u, v} r :=
    IndexCofibrantProperness.originalNativePushout_levelWeak
      PointedCGWH.Spectra.NativeStable.orthogonalHom_isCofibrant
      (pushout.inr i a) q r j second hright hq.2
  have hrW : W r := NativeK.levelWeak_le_omegaTests s r hrLevel
  have hcomp : W (pushout.inl i a ≫ r) := (W (B := B)).comp_mem _ _ hleftW hrW
  rw [hlr] at hcomp
  exact hcomp

/-- This preparation proves the full left-pushout statement for the same original stable model. -/
theorem leftPushoutStatement : LeftPushoutStatement.{u, v} (B := B) := by
  intro A X Z P i f f' j sq hi hf
  exact omegaTests_of_original_pushout sq hi hf

/-- The original ordinary orthogonal stable model is left proper on all original endpoints. -/
theorem orthogonalModel_isLeftProper :
    let : ModelCategory C.{u, v} := StableModelConstruction.orthogonalModelCategory (B := B)
    IsLeftProper C.{u, v} := by
  let : ModelCategory C.{u, v} := StableModelConstruction.orthogonalModelCategory (B := B)
  refine ⟨?_⟩
  constructor
  intro A X i hi
  constructor
  intro Z P j f' f sq hf
  exact omegaTests_of_original_pushout sq hi hf


open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

/-- The full original HEP source span and its same I counit comparison have every Omega target test. -/
theorem originalSpanCallerComparison_omegaTests_of_HEP
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst)) :
    W (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) := by
  exact MMSSStabilization.OriginalFunctionRawIteration.integerPiStar_implies_omegaTests _
    (originalOrthogonalSpanCallerComparison_integerPi D lQ rQ sqQ lP rP sqP hHEP)

/-- The complete original I source-span comparison has every original
Omega-target test when the actual caller attaching arrow is a stable cofibration. -/
theorem originalSpanCallerComparison_omegaTests
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : Cof (D.map WalkingSpan.Hom.fst)) :
    W (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) := by
  have hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst) :=
    PointedCGWH.Spectra.OriginalContinuousSourceApproximation.originalNativeILeft_le_HEP _ hi
  exact originalSpanCallerComparison_omegaTests_of_HEP D lQ rQ sqQ lP rP sqP hHEP

/-- Every full original scalar cotensor of every Omega target retains
the same complete source-span/Q-counit/caller-pushout precomposition function. -/
theorem originalSpanCallerComparison_allOmegaScalarTests_of_HEP
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst))
    (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Function.Bijective
      (fun g : H.obj P ⟶ H.obj ((cotensor M).obj E) =>
        H.map (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) ≫ g) :=
  originalSpanCallerComparison_omegaTests_of_HEP D lQ rQ sqQ lP rP sqP hHEP
    ((cotensor M).obj E) (NativeK.cotensor_isOmega s M E hE)

/-- Every full original scalar cotensor of every Omega target retains
the same complete source-span/Q-counit/caller-pushout precomposition function. -/
theorem originalSpanCallerComparison_allOmegaScalarTests
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : Cof (D.map WalkingSpan.Hom.fst))
    (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Function.Bijective
      (fun g : H.obj P ⟶ H.obj ((cotensor M).obj E) =>
        H.map (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) ≫ g) :=
  originalSpanCallerComparison_omegaTests D lQ rQ sqQ lP rP sqP hi
    ((cotensor M).obj E) (NativeK.cotensor_isOmega s M E hE)

/-- Both full original span input maps and all four caller pushouts
retain the actual I-source/counit naturality in every target Hom function. -/
theorem originalSpanCallerComparison_test_naturality
    {D E : WalkingSpan ⥤ C.{u, v}} (a : D ⟶ E)
    {QD PD QE PE : C.{u, v}}
    (lQD : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ QD)
    (rQD : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ QD)
    (sQD : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQD rQD)
    (lPD : D.obj WalkingSpan.left ⟶ PD) (rPD : D.obj WalkingSpan.right ⟶ PD)
    (sPD : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lPD rPD)
    (lQE : (originalSpanDiagram (B := B) E).obj WalkingSpan.left ⟶ QE)
    (rQE : (originalSpanDiagram (B := B) E).obj WalkingSpan.right ⟶ QE)
    (sQE : IsPushout ((originalSpanDiagram (B := B) E).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) E).map WalkingSpan.Hom.snd) lQE rQE)
    (lPE : E.obj WalkingSpan.left ⟶ PE) (rPE : E.obj WalkingSpan.right ⟶ PE)
    (sPE : IsPushout (E.map WalkingSpan.Hom.fst) (E.map WalkingSpan.Hom.snd) lPE rPE)
    (q : QD ⟶ QE) (p : PD ⟶ PE)
    (hQL : lQD ≫ q = (originalSpanMap (B := B) a).app WalkingSpan.left ≫ lQE)
    (hQR : rQD ≫ q = (originalSpanMap (B := B) a).app WalkingSpan.right ≫ rQE)
    (hPL : lPD ≫ p = a.app WalkingSpan.left ≫ lPE)
    (hPR : rPD ≫ p = a.app WalkingSpan.right ≫ rPE)
    (T : C.{u, v}) (g : H.obj PE ⟶ H.obj T) :
    H.map q ≫ (H.map (originalSpanCallerComparison E lQE rQE sQE lPE rPE sPE) ≫ g) =
      H.map (originalSpanCallerComparison D lQD rQD sQD lPD rPD sPD) ≫ (H.map p ≫ g) := by
  have h := H.congr_map
    (originalSpanCallerComparison_naturality a lQD rQD sQD lPD rPD sPD
      lQE rQE sQE lPE rPE sPE q p hQL hQR hPL hPR)
  simp only [Functor.map_comp] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ g) h).trans (Category.assoc _ _ _))



end PointedCGWH.Spectra.Orthogonal.NativeStableProperness


namespace PointedCGWH.Spectra.Orthogonal.NativeStableProperness

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests

private abbrev Fib : CategoryTheory.MorphismProperty C.{u, v} :=
  (StableModelConstruction.orthogonalModelCategory (B := B)).categoryWithFibrations.fibrations
private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

private theorem conditionalOmegaFiberFiveLemma_successor
    (hComparison : ConditionalFiberHom.ComparisonHomBijections.{u, v} (B := B))
    (F F' : rightArrows.{u, v}) (a : F' ⟶ F)
    (c : PullbackCone F'.obj.hom (Diagrams.zeroTo F'.obj.right)) (hc : IsLimit c)
    (d : PullbackCone F.obj.hom (Diagrams.zeroTo F.obj.right)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (hbase : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj F.obj.right ⟶ H.obj ((integerTarget q).obj E) => H.map a.hom.right ≫ g))
    (hfiber : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj d.pt ⟶ H.obj ((integerTarget q).obj E) =>
        H.map (chosenFiberMap a.hom c d hd) ≫ g)) (q : ℤ) :
    Function.Bijective
      (fun g : H.obj F.obj.left ⟶ H.obj ((integerTarget (q + 1)).obj E) => H.map a.hom.left ≫ g) := by
  let E1 : C.{u, v} := (integerTarget (q + 1)).obj E
  have hE1 : NativeK.IsOmega s E1 := integerTarget_isOmega (q + 1) E hE
  have haw : a.hom.left ≫ F.obj.hom = F'.obj.hom ≫ a.hom.right := a.hom.w
  have hbc (g : H.obj F.obj.right ⟶ H.obj E1) :
      H.map a.hom.left ≫ (H.map F.obj.hom ≫ g) = H.map F'.obj.hom ≫ (H.map a.hom.right ≫ g) := by
    rw [← Category.assoc, ← H.map_comp, haw, H.map_comp, Category.assoc]
  have hcf : chosenFiberMap a.hom c d hd ≫ d.fst = c.fst ≫ a.hom.left :=
    chosenFiberMap_fst a.hom c d hd
  have hcd (g : H.obj F.obj.left ⟶ H.obj E1) :
      H.map (chosenFiberMap a.hom c d hd) ≫ (H.map d.fst ≫ g) =
        H.map c.fst ≫ (H.map a.hom.left ≫ g) := by
    rw [← Category.assoc, ← H.map_comp, hcf, H.map_comp, Category.assoc]
  exact OriginalOmegaHoHomGroup.omegaHomFiveLemma E1 hE1
    (ConditionalChosenFiberSequence.connecting hComparison (q + 1) F d hd E hE)
    F.obj.hom d.fst (ConditionalChosenFiberSequence.connecting hComparison q F d hd E hE)
    (ConditionalChosenFiberSequence.connecting hComparison (q + 1) F' c hc E hE)
    F'.obj.hom c.fst (ConditionalChosenFiberSequence.connecting hComparison q F' c hc E hE)
    (fun g => H.map (chosenFiberMap a.hom c d hd) ≫ g)
    a.hom.right a.hom.left (chosenFiberMap a.hom c d hd) (fun g => H.map a.hom.right ≫ g)
    (OrdinaryHoCofiberKernel.nullHom F.obj.right ((integerTarget q).obj E))
    (OrdinaryHoCofiberKernel.nullHom F'.obj.right ((integerTarget q).obj E))
    (ConditionalChosenFiberSequence.exact_at_base hComparison (q + 1) F d hd E hE)
    (ConditionalChosenFiberSequence.exact_at_shifted_total hComparison q F d hd E hE)
    (ConditionalChosenFiberSequence.exact_at_fiber hComparison q F d hd E hE)
    (ConditionalChosenFiberSequence.exact_at_base hComparison (q + 1) F' c hc E hE)
    (ConditionalChosenFiberSequence.exact_at_shifted_total hComparison q F' c hc E hE)
    (ConditionalChosenFiberSequence.exact_at_fiber hComparison q F' c hc E hE)
    (fun g => (ConditionalChosenFiberSequence.connecting_source hComparison (q + 1)
      a c hc d hd E hE g).symm)
    hbc hcd
    (fun g => (ConditionalChosenFiberSequence.connecting_source hComparison q
      a c hc d hd E hE g).symm)
    (OrdinaryHoCofiberKernel.precomp_nullHom a.hom.right)
    (hfiber ((q + 1) + 1)).2 (hbase (q + 1)) (hfiber (q + 1)) (hbase q).1

private theorem conditionalOmegaFiberFiveLemma
    (hComparison : ConditionalFiberHom.ComparisonHomBijections.{u, v} (B := B))
    {X Y X' Y' : C.{u, v}} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (hp : (NativeK.generators s).rlp p) (hp' : (NativeK.generators s).rlp p')
    (a : Arrow.mk p' ⟶ Arrow.mk p)
    (c : PullbackCone p' (Diagrams.zeroTo Y')) (hc : IsLimit c)
    (d : PullbackCone p (Diagrams.zeroTo Y)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (hbase : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj Y ⟶ H.obj ((integerTarget q).obj E) => H.map a.right ≫ g))
    (hfiber : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj d.pt ⟶ H.obj ((integerTarget q).obj E) =>
        H.map (chosenFiberMap a c d hd) ≫ g)) :
    ∀ q : ℤ, Function.Bijective
      (fun g : H.obj X ⟶ H.obj ((integerTarget q).obj E) => H.map a.left ≫ g) := by
  intro q
  let F : rightArrows.{u, v} := ⟨Arrow.mk p, hp⟩
  let F' : rightArrows.{u, v} := ⟨Arrow.mk p', hp'⟩
  let aa : F' ⟶ F := ⟨a⟩
  have hs := conditionalOmegaFiberFiveLemma_successor hComparison F F' aa c hc d hd E hE hbase hfiber (q - 1)
  have hq : q - 1 + 1 = q := sub_add_cancel q 1
  rw [hq] at hs
  exact hs


/-- The full original Omega-target fiber Five Lemma retains both arbitrary
K-right arrows, both caller limit cones and every original integer degree. -/
theorem originalOmegaFiberFiveLemma
    {X Y X' Y' : C.{u, v}} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (hp : (NativeK.generators s).rlp p) (hp' : (NativeK.generators s).rlp p')
    (a : Arrow.mk p' ⟶ Arrow.mk p)
    (c : PullbackCone p' (Diagrams.zeroTo Y')) (hc : IsLimit c)
    (d : PullbackCone p (Diagrams.zeroTo Y)) (hd : IsLimit d)
    (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (hbase : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj Y ⟶ H.obj ((integerTarget q).obj E) => H.map a.right ≫ g))
    (hfiber : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj d.pt ⟶ H.obj ((integerTarget q).obj E) =>
        H.map (chosenFiberMap a c d hd) ≫ g)) :
    ∀ q : ℤ, Function.Bijective
      (fun g : H.obj X ⟶ H.obj ((integerTarget q).obj E) => H.map a.left ≫ g) := by
  exact conditionalOmegaFiberFiveLemma
    (NativeK.OriginalFiberNullity.orthogonalComparisonHomBijections (B := B))
    p p' hp hp' a c hc d hd E hE hbase hfiber

omit B in
private def mappedFiberConeIsLimit
    {A Z X Y : C.{u, v}} {p' : A ⟶ Z} {f' : A ⟶ X} {f : Z ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) (c : PullbackCone p' (Diagrams.zeroTo Z)) (hc : IsLimit c) :
    IsLimit (chosenMapCone (Arrow.homMk f' f sq.w.symm : Arrow.mk p' ⟶ Arrow.mk p) c) := by
  have hs : IsPullback c.fst c.snd p' (Diagrams.zeroTo Z) := IsPullback.of_isLimit hc
  have ht : IsPullback (c.fst ≫ f') c.snd p (Diagrams.zeroTo Y) := by
    simpa only [Diagrams.zeroTo_naturality] using hs.paste_horiz sq.flip
  exact ht.isLimit

/-- Pulling back the original stable weak arrow along an actual stable
fibration preserves every original Omega-target test on the same caller leg. -/
theorem omegaTests_of_original_pullback
    {A Z X Y : C.{u, v}} {p' : A ⟶ Z} {f' : A ⟶ X} {f : Z ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) (hp : Fib p) (hf : W f) : W f' := by
  have hpK : (NativeK.generators s).rlp p := hp
  have hp' : (NativeK.generators s).rlp p' :=
    (NativeK.generators s).rlp.of_isPullback sq.flip hpK
  let a : Arrow.mk p' ⟶ Arrow.mk p := Arrow.homMk f' f sq.w.symm
  let c : PullbackCone p' (Diagrams.zeroTo Z) := fiberCone p'
  let hc : IsLimit c := fiberConeIsLimit p'
  let d : PullbackCone p (Diagrams.zeroTo Y) := chosenMapCone a c
  let hd : IsLimit d := mappedFiberConeIsLimit sq c hc
  intro E hE
  have hbase : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj Y ⟶ H.obj ((integerTarget q).obj E) => H.map a.right ≫ g) :=
    fun q => precomposition_bijective q f hf E hE
  have hfiber : ∀ q : ℤ, Function.Bijective
      (fun g : H.obj d.pt ⟶ H.obj ((integerTarget q).obj E) =>
        H.map (chosenFiberMap a c d hd) ≫ g) := by
    intro q
    change Function.Bijective
      (fun g : H.obj d.pt ⟶ H.obj ((integerTarget q).obj E) => H.map (hd.lift d) ≫ g)
    rw [hd.lift_self, H.map_id]
    simp only [Category.id_comp]
    exact Function.bijective_id
  exact originalOmegaFiberFiveLemma p p' hpK hp' a c hc d hd E hE hbase hfiber 0

/-- The original ordinary orthogonal stable model is right proper on arbitrary endpoints. -/
theorem orthogonalModel_isRightProper :
    let : ModelCategory C.{u, v} := StableModelConstruction.orthogonalModelCategory (B := B)
    IsRightProper C.{u, v} := by
  let : ModelCategory C.{u, v} := StableModelConstruction.orthogonalModelCategory (B := B)
  refine ⟨?_⟩
  constructor
  intro X Y p hp
  constructor
  intro Z A p' f' f sq hf
  exact omegaTests_of_original_pullback sq hp hf

/-- Both full properness laws concern the one actual original ordinary stable model. -/
theorem orthogonalModel_isProper :
    let : ModelCategory C.{u, v} := StableModelConstruction.orthogonalModelCategory (B := B)
    IsLeftProper C.{u, v} ∧ IsRightProper C.{u, v} :=
  ⟨orthogonalModel_isLeftProper, orthogonalModel_isRightProper⟩

open PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

/-- The full original source comparison retains every actual integer Pi group test. -/
theorem originalSpanCallerComparison_integerPi_of_HEP
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst)) :
    Actual.OrthogonalIntegerHomotopy.integerPiStarEquivalences
      (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) :=
  originalOrthogonalSpanCallerComparison_integerPi D lQ rQ sqQ lP rP sqP hHEP

/-- All signed integer targets and all original cofibrant scalars preserve
both complete caller pushouts and the same source comparison function. -/
theorem originalSpanCallerComparison_allIntegerOmegaScalarTests_of_HEP
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hHEP : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst))
    (q : ℤ) (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Function.Bijective
      (fun g : H.obj P ⟶ H.obj ((cotensor M).obj ((integerTarget q).obj E)) =>
        H.map (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) ≫ g) :=
  originalSpanCallerComparison_allOmegaScalarTests_of_HEP D lQ rQ sqQ lP rP sqP hHEP
    ((integerTarget q).obj E) (integerTarget_isOmega q E hE) M

/-- All signed integer targets and all original cofibrant scalars preserve
both complete caller pushouts and the same source comparison function. -/
theorem originalSpanCallerComparison_allIntegerOmegaScalarTests
    (D : WalkingSpan ⥤ C.{u, v}) {Q P : C.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : Cof (D.map WalkingSpan.Hom.fst))
    (q : ℤ) (E : C.{u, v}) (hE : NativeK.IsOmega s E)
    (M : PointedCGWH.{u, v}) [IsCofibrant M] :
    Function.Bijective
      (fun g : H.obj P ⟶ H.obj ((cotensor M).obj ((integerTarget q).obj E)) =>
        H.map (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) ≫ g) :=
  originalSpanCallerComparison_allOmegaScalarTests D lQ rQ sqQ lP rP sqP hi
    ((integerTarget q).obj E) (integerTarget_isOmega q E hE) M

end PointedCGWH.Spectra.Orthogonal.NativeStableProperness
