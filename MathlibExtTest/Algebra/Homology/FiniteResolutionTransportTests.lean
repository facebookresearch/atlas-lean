/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExtTest.Algebra.Homology.FiniteResolutionTests
public import MathlibExt.Algebra.Homology.FiniteResolutionSourceCoherence
public import MathlibExt.Algebra.Homology.FiniteResolutionCochainShift
public import MathlibExt.Algebra.Homology.Embedding.TruncGETransitionComposition
public import MathlibExt.Algebra.Homology.Embedding.RestrictionExtendAdjunction
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncMap
public import MathlibExt.Algebra.Homology.Embedding.UpNatToInt
public import MathlibExt.Algebra.Homology.ExactColimits
public import MathlibExt.Algebra.Homology.HomComplex.CocycleBoundary
public import MathlibExt.Algebra.Homology.HomComplexCoproducts
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public meta import Mathlib.Tactic.NormNum

/-!
# Finite-resolution transport and signed cochain comparisons over the integers

The split sequence ℤ → ℤ → 0 gives a finite resolution whose differential is the identity.
An odd cochain shift changes that differential to its negative. A separate resolution of ℤ
tests the nonzero augmentation and the source-change comparison. The same module supplies
good-truncation, restriction-extension and exact-colimit examples.

Two coproduct summands detect a nonzero homology class and a cochain with coefficient two.
A triangle with degree-one morphism −2 tests the cocycle boundary expression and its
homotopy-category specialization; no distinguished-triangle claim is needed for that formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Preadditive Opposite
open CategoryTheory.Abelian
open CategoryTheory.Pretriangulated
open CochainComplex.HomComplex
open scoped ZeroObject

namespace CategoryTheory.Abelian.FiniteResolution.TransportTests

private abbrev M := ModuleCat.{0} ℤ
private abbrev E : M := ModuleCat.of ℤ ℤ
private abbrev C := CochainComplex M ℤ

private abbrev identityResolution : FiniteResolution (𝟭 M) E :=
  Tests.identityResolution E 0

private abbrev splitSequence : ShortComplex M :=
  ShortComplex.mk (𝟙 E) (0 : E ⟶ (0 : M)) (by simp)

private def splitSequenceSplitting : splitSequence.Splitting where
  r := 𝟙 E
  s := 0
  f_r := by simp [splitSequence]
  s_g := (isZero_zero M).eq_of_tgt _ _
  id := by simp [splitSequence]

private def splitResolution : FiniteResolution (𝟭 M) (0 : M) :=
  ofShortExact E (𝟙 E) (0 : E ⟶ (0 : M)) (by simp)
    splitSequenceSplitting.shortExact identityResolution

private lemma splitResolution_d : splitResolution.complex.d 1 0 = 𝟙 E := by
  change (ofShortExact E (𝟙 E) (0 : E ⟶ (0 : M)) (by simp)
    splitSequenceSplitting.shortExact identityResolution).mappedComplex.d 1 0 = 𝟙 E
  rw [ofShortExact_mappedComplex_d_one_zero]
  change (𝟙 E) ≫ (𝟙 E) = 𝟙 E
  exact Category.id_comp _

private lemma splitResolution_bound : splitResolution.bound = 1 := by
  change (ofShortExact E (𝟙 E) (0 : E ⟶ (0 : M)) (by simp)
    splitSequenceSplitting.shortExact identityResolution).bound = 1
  rw [ofShortExact_bound]
  rfl

private lemma splitResolution_projective (n : ℕ) :
    Projective (splitResolution.complex.X n) := by
  cases n with
  | zero =>
      change Projective E
      infer_instance
  | succ n =>
      change Projective (identityResolution.complex.X n)
      cases n with
      | zero =>
          change Projective E
          infer_instance
      | succ n =>
          exact (identityResolution.isZero_above (n + 1) (Nat.zero_lt_succ n)).projective

private abbrev sourceMoved :=
  identityResolution.mapSource (𝟭 M) (Functor.leftUnitor (𝟭 M))

private abbrev targetMoved :=
  identityResolution.mapTarget (𝟭 M) (Functor.rightUnitor (𝟭 M))

-- Source transport retains the augmentation on a nonzero integer.
example : ModuleCat.Hom.hom sourceMoved.augmentation₀ (7 : ℤ) = 7 := by
  change ModuleCat.Hom.hom ((𝟙 E) ≫ (𝟙 E)) (7 : ℤ) = 7
  rfl

-- Target transport uses the inverse source comparison and forward single-complex comparison.
example : ModuleCat.Hom.hom targetMoved.augmentation₀ (7 : ℤ) = (7 : ℤ) := by
  change ModuleCat.Hom.hom ((𝟙 E) ≫ (𝟙 E) ≫ (𝟙 E)) (7 : ℤ) = 7
  rfl

example : ModuleCat.Hom.hom ((mapSourceIdentityMap identityResolution).f 0) (13 : ℤ) =
    (13 : ℤ) ∧
    ((𝟭 M).mapHomologicalComplex (.down ℕ)).map
        (mapSourceIdentityMap identityResolution) ≫ identityResolution.augmentation =
      sourceMoved.augmentation := by
  constructor
  · rw [mapSourceIdentityMap_f]
    rfl
  · exact mapSourceIdentityMap_augmentation identityResolution

private abbrev signedComplex := splitResolution.cochainShift 1

private def signedDifferential : E ⟶ E :=
  (splitResolution.cochainShiftTermIso 1 1).inv ≫ signedComplex.d 0 1 ≫
    (splitResolution.cochainShiftTermIso 1 0).hom

private lemma signedDifferential_eq : signedDifferential = -(𝟙 E) := by
  have h := cochainShiftTermIso_d splitResolution (1 : ℤ) 0
  rw [splitResolution_d] at h
  have hsign : (-(1 : ℤ)).negOnePow • (𝟙 E) = -(𝟙 E) := by
    ext x
    norm_num [Units.smul_def]
  exact (show signedDifferential = (-(1 : ℤ)).negOnePow • (𝟙 E) from h).trans hsign

-- The odd shift has a genuinely nonzero negative differential.
example : ModuleCat.Hom.hom signedDifferential (1 : ℤ) = -1 ∧ signedDifferential ≠ 0 := by
  rw [signedDifferential_eq]
  constructor
  · rfl
  · intro h
    have h' := congrArg (fun f : E ⟶ E => ModuleCat.Hom.hom f (1 : ℤ)) h
    norm_num at h'

private def shiftedAugmentation : E ⟶ E :=
  (identityResolution.cochainShiftTermIso 1 0).inv ≫
    (identityResolution.cochainShiftAugmentation 1).f 1 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 1 E).hom

private lemma shiftedAugmentation_eq : shiftedAugmentation = 𝟙 E := by
  have hx : (identityResolution.cochainShift 1).XIsoOfEq
      (show (1 : ℤ) = 1 - (0 : ℤ) by simp) = Iso.refl _ := by
    rfl
  dsimp only [shiftedAugmentation]
  erw [cochainShiftAugmentation_f]
  simp only [Functor.id_map, hx, Iso.refl_hom, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp [identityResolution, Tests.identityResolution, augmentation₀]

example : ModuleCat.Hom.hom shiftedAugmentation (1 : ℤ) = 1 := by
  rw [shiftedAugmentation_eq]
  rfl

-- Support and augmentation quasi-isomorphism facts are available by inference.
example : signedComplex.IsStrictlyLE 1 ∧ signedComplex.IsStrictlyGE 0 ∧
    QuasiIso (splitResolution.cochainShiftAugmentation 1) ∧
      Projective (signedComplex.X 0) := by
  refine ⟨inferInstance, ?_, inferInstance, ?_⟩
  · simpa [signedComplex, splitResolution_bound] using
      cochainShift_isStrictlyGE splitResolution (1 : ℤ)
  · exact cochainShift_projective_term splitResolution 1 0 splitResolution_projective

-- At a strict cutoff, the transition is the actual opcycles quotient.
example :
    (signedComplex.truncGETransition 0 1 (by norm_num)).f 1 ≫
        (signedComplex.truncGEXIsoOpcycles 1).hom =
      (signedComplex.truncGEXIso 0 1 (by norm_num)).hom ≫ signedComplex.pOpcycles 1 :=
  signedComplex.truncGETransition_f_comp_truncGEXIsoOpcycles_hom 0 1 (by norm_num)

example : Epi (signedComplex.truncGETransition 0 1 (by norm_num)) ∧
    QuasiIsoAt (signedComplex.truncGETransition 0 1 (by norm_num)) 1 :=
  ⟨inferInstance, signedComplex.quasiIsoAt_truncGETransition 0 1 1
    (by norm_num) (by norm_num)⟩

example : (identityResolution.cochainShift 1).truncGETransition 1 1 le_rfl =
    𝟙 ((identityResolution.cochainShift 1).truncGE 1) :=
  (identityResolution.cochainShift 1).truncGETransition_self 1

private abbrev singleZero : C := (CochainComplex.singleFunctor M 0).obj E
private abbrev singleOne : C := (CochainComplex.singleFunctor M 1).obj E
private abbrev singleZeroX : singleZero.X 0 ≅ E :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 E

-- The adjunction unit is the projection, with identity coordinates on the retained term.
example : ModuleCat.Hom.hom
    (singleZeroX.inv ≫
      ((ComplexShape.embeddingDownNat.restrictionExtendAdjunction (C := M)).unit.app
        singleZero).f 0 ≫
      (singleZero.stupidTruncXIso ComplexShape.embeddingDownNat
        (show ComplexShape.embeddingDownNat.f 0 = 0 by simp)).hom ≫ singleZeroX.hom)
    (7 : ℤ) = 7 := by
  let s := singleZero.stupidTruncXIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f (0 : ℕ) = (0 : ℤ) by simp)
  rw [← HomologicalComplex.πStupidTrunc_eq_unit,
    HomologicalComplex.πStupidTrunc_f_eq (K := singleZero)
      (e := ComplexShape.embeddingDownNat) (p := 0) (q := 0) (by simp)]
  have hs : s.inv ≫ s.hom = 𝟙 _ := s.inv_hom_id
  have he : singleZeroX.inv ≫ s.inv ≫ s.hom ≫ singleZeroX.hom = 𝟙 E := by
    calc
      _ = singleZeroX.inv ≫ (s.inv ≫ s.hom) ≫ singleZeroX.hom := by
        simp only [Category.assoc]
      _ = singleZeroX.inv ≫ 𝟙 _ ≫ singleZeroX.hom :=
        congrArg (fun f => singleZeroX.inv ≫ f ≫ singleZeroX.hom) hs
      _ = 𝟙 E := by rw [Category.id_comp, singleZeroX.inv_hom_id]
  change ModuleCat.Hom.hom (singleZeroX.inv ≫ s.inv ≫ s.hom ≫ singleZeroX.hom) (7 : ℤ) = 7
  exact (ConcreteCategory.congr_hom he (7 : ℤ)).trans (by rfl)

private abbrev family : Fin 2 → C := fun _ => singleZero
private abbrev diagram : Discrete (Fin 2) ⥤ C := Discrete.functor family
private abbrev H := HomologicalComplex.homologyFunctor M (.up ℤ) 0
private abbrev singleZeroHomology : singleZero.homology 0 ≅ E :=
  HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 E

example : PreservesColimitsOfShape (Discrete (Fin 2)) H := inferInstance

private def homologyDetector : colimit (diagram ⋙ H) ⟶ E :=
  colimit.desc (diagram ⋙ H)
    { pt := E
      ι := Discrete.natTrans (fun _ => singleZeroHomology.hom) }

private def homologyInjection : E ⟶ (colimit diagram).homology 0 :=
  singleZeroHomology.inv ≫ H.map (colimit.ι diagram (.mk 0))

private lemma homologyDetection :
    homologyInjection ≫ (HomologicalComplex.homologyColimitIso diagram 0).hom ≫
      homologyDetector = 𝟙 E := by
  dsimp only [homologyInjection]
  calc
    _ = singleZeroHomology.inv ≫
        (H.map (colimit.ι diagram (.mk 0)) ≫
          (HomologicalComplex.homologyColimitIso diagram 0).hom) ≫ homologyDetector := by
      simp only [Category.assoc]
    _ = singleZeroHomology.inv ≫ colimit.ι (diagram ⋙ H) (.mk 0) ≫ homologyDetector := by
      rw [HomologicalComplex.map_ι_comp_homologyColimitIso_hom]
    _ = 𝟙 E := by simp [homologyDetector]

example : ModuleCat.Hom.hom
    (homologyInjection ≫ (HomologicalComplex.homologyColimitIso diagram 0).hom ≫
      homologyDetector) (1 : ℤ) = 1 ∧ homologyInjection ≠ 0 := by
  constructor
  · rw [homologyDetection]
    rfl
  · intro h
    have h' := congrArg (fun f : E ⟶ E => ModuleCat.Hom.hom f (1 : ℤ)) homologyDetection
    rw [h, zero_comp] at h'
    norm_num at h'

private def doubleFold : (∐ family) ⟶ singleZero :=
  Limits.Sigma.desc (fun _ => (2 : ℤ) • 𝟙 singleZero)

private def twiceFold : (∐ family) ⟶ singleZero :=
  (2 : ℤ) • Limits.Sigma.desc (fun _ => 𝟙 singleZero)

-- Equal values on both summands identify two different expressions for a nonzero cochain.
example : Cochain.ofHom doubleFold = Cochain.ofHom twiceFold := by
  apply Cochain.ext_of_precomp_sigma_ι
  intro j
  rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  congr 1
  simp [doubleFold, twiceFold, comp_zsmul]

example : ModuleCat.Hom.hom
    (singleZeroX.inv ≫ ((Limits.Sigma.ι family 0) ≫ doubleFold).f 0 ≫ singleZeroX.hom)
    (1 : ℤ) = 2 := by
  simp [doubleFold, HomologicalComplex.zsmul_f_apply, comp_zsmul, zsmul_comp,
    Category.assoc]

private def shiftCoordinate : singleOne⟦(1 : ℤ)⟧ ≅ singleZero :=
  ((CochainComplex.singleFunctors M).shiftIso 1 0 1 (by norm_num)).app E

private def negativeBoundary : singleZero ⟶ singleOne⟦(1 : ℤ)⟧ :=
  ((-2 : ℤ) • 𝟙 singleZero) ≫ shiftCoordinate.inv

private def boundaryTriangle : Triangle C where
  obj₁ := singleOne
  obj₂ := 0
  obj₃ := singleZero
  mor₁ := 0
  mor₂ := 0
  mor₃ := negativeBoundary

private def identityCocycle : Cocycle singleZero singleZero 0 :=
  Cocycle.equivHomShift (ShiftedHom.mk₀ 0 rfl (𝟙 singleZero))

private def boundaryMap : singleZero ⟶ singleOne⟦(1 : ℤ)⟧ :=
  (preadditiveCoyoneda.obj (op singleZero)).homologySequenceδ
    ((𝟭 C).mapTriangle.obj boundaryTriangle) 0 1 rfl
    (Cocycle.mappedShiftedHom (𝟭 C) identityCocycle)

private lemma boundaryMap_eq : boundaryMap = negativeBoundary := by
  have h := Cocycle.mappedShiftedHom_boundary (𝟭 C) boundaryTriangle
    (K := singleZero) (0 : ℤ) identityCocycle
  calc
    boundaryMap = Cocycle.mappedShiftedHom (𝟭 C)
        ((identityCocycle.postcomp negativeBoundary).rightUnshift 1 rfl) := by
      exact h
    _ = negativeBoundary := by
      dsimp only [Cocycle.mappedShiftedHom, ShiftedHom.map]
      rw [Cocycle.equivHomShift_symm_postcomp_rightUnshift]
      simp [identityCocycle]

private lemma boundaryNormalized :
    boundaryMap ≫ shiftCoordinate.hom = (-2 : ℤ) • 𝟙 singleZero := by
  rw [boundaryMap_eq]
  simp [negativeBoundary, Category.assoc]

example : ModuleCat.Hom.hom
    (singleZeroX.inv ≫ (boundaryMap ≫ shiftCoordinate.hom).f 0 ≫ singleZeroX.hom)
    (1 : ℤ) = -2 := by
  rw [boundaryNormalized]
  simp [HomologicalComplex.zsmul_f_apply, comp_zsmul, zsmul_comp, Category.assoc]

example :
    (preadditiveCoyoneda.obj
      (op ((HomotopyCategory.quotient M (.up ℤ)).obj singleZero))).homologySequenceδ
      ((HomotopyCategory.quotient M (.up ℤ)).mapTriangle.obj boundaryTriangle)
      0 1 rfl identityCocycle.shiftedHom =
        ((identityCocycle.postcomp negativeBoundary).rightUnshift 1 rfl).shiftedHom :=
  Cocycle.shiftedHom_boundary boundaryTriangle 0 identityCocycle

end CategoryTheory.Abelian.FiniteResolution.TransportTests

end
