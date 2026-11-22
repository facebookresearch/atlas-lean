/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ShiftedPuppeExactness
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.ChosenFiberNaturality
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalBasedPathCoefficientGeometry

/-!
# Actual original orthogonal chosen-fiber Hom maps in every integer degree

The source is the original suspended Q chosen-fiber comparison on every
full native K-right Arrow. Its actual precomposition map and the original
integer suspension Hom functions construct the full fiber-test function.
All source and target maps, original fiber restrictions, null classes and
both maps of every caller's change of fiber are retained.

The source comparison's test bijectivity and boundary normalization are
separate proof obligations. These definitions and naturality laws use
the original comparison map itself and introduce neither result as an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.IntegerTargetTests
open PointedCGWH.Spectra.Orthogonal.NegativeHomTests

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

/-- Every original full paired K-right Arrow is retained as an actual source object. -/
abbrev rightArrows := (NativeK.OriginalFiberComparison.rightArrowProperty
  orthogonalFamily.{u, v}).FullSubcategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := O.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := O.{u, v})
private abbrev CQ := NativeK.CofiberNullity.cofiberQ (B := B) (I := O.{u, v})

/-- The full native level-fibration property includes its actual fibrant-target witness. -/
abbrev fibrantFibrationProperty : ObjectProperty (Arrow C.{u, v}) :=
  OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := C.{u, v})

/-- Every original K-right Arrow is included with the same Arrow and actual native witnesses. -/
theorem rightArrows_le_fibrantFibrations :
    NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v} ≤
      fibrantFibrationProperty.{u, v} (B := B) :=
  fun F hF => (NativeK.OriginalFiberComparison.rightArrowAsFibrantFibration
    orthogonalFamily.{u, v} ⟨F, hF⟩).property

namespace General

variable {P : ObjectProperty (Arrow C.{u, v})}
  (hP : P ≤ ChosenFiberHomTests.fibrantFibrationProperty.{u, v} (B := B))


/-- The inclusion retains the full original Arrow, both components and its native witnesses. -/
def asFibrantFibration (F : P.FullSubcategory) :
    (fibrantFibrationProperty.{u, v} (B := B)).FullSubcategory :=
  ⟨F.obj, hP F.obj F.property⟩

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- Every actual caller fiber has the same original integer target test. -/
abbrev fiberHom (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :=
  H.obj (a F.obj).pt ⟶ H.obj ((integerTarget q).obj E)

/-- The original Q cofiber has its same actual integer target test. -/
abbrev cofiberHom (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :=
  H.obj (CQ.obj F.obj) ⟶ H.obj ((integerTarget q).obj E)

/-- The original suspended Q caller fiber retains its whole native Hom term. -/
abbrev suspendedFiberHom (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :=
  H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶ H.obj ((integerTarget q).obj E)

/-- The actual original comparison map is retained at the unchanged caller chosen fiber. -/
abbrev comparison (F : P.FullSubcategory) :
    H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶ H.obj (CQ.obj F.obj) :=
  (NativeK.OriginalFiberComparison.nativeFibrationComparison (B := B) a ha).app
    (asFibrantFibration hP F)

/-- Each original comparison test is its actual full precomposition function. -/
def comparisonPrecomposition (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    cofiberHom q F E → suspendedFiberHom a q F E := fun g => comparison (hP := hP) a ha F ≫ g

/-- The original integer suspension function acts on that same actual comparison test. -/
def comparisonTest (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberHom q F E → fiberHom a (q + 1) F E :=
  fun g => shiftHomEquiv q (a F.obj).pt E hE (comparisonPrecomposition (hP := hP) a ha q F E g)

/-- Every complete original K-right Arrow square acts by its actual chosen-fiber map. -/
def fiberSource (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G) (E : C.{u, v}) :
    fiberHom a q G E → fiberHom a q F E :=
  fun g => H.map (chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj)) ≫ g

/-- Every original whole Arrow square retains the unchanged original Q-cofiber map. -/
def cofiberSource (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G) (E : C.{u, v}) :
    cofiberHom q G E → cofiberHom q F E := fun g => H.map (CQ.map f.hom) ≫ g

/-- Every whole target map retains its actual integer target functor action on the fiber. -/
def fiberTarget (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E') :
    fiberHom a q F E → fiberHom a q F E' := fun g => g ≫ H.map ((integerTarget q).map t)

/-- The original Q-cofiber target action keeps the same entire integer target map. -/
def cofiberTarget (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E') :
    cofiberHom q F E → cofiberHom q F E' := fun g => g ≫ H.map ((integerTarget q).map t)

/-- Both original comparison and suspension Hom functions retain the whole native source square. -/
theorem comparisonTest_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q G E) :
    comparisonTest (hP := hP) a ha q F E hE (cofiberSource q f E g) =
      fiberSource a ha (q + 1) f E (comparisonTest (hP := hP) a ha q G E hE g) := by
  let α := chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj)
  have h : H.map (S.map (Q.map α)) ≫ comparison (hP := hP) a ha G =
      comparison (hP := hP) a ha F ≫ H.map (CQ.map f.hom) :=
    OriginalFiberCofiberGeometry.suspendedComparison_naturality (B := B) (J := O.{u, v})
      a ha (show asFibrantFibration hP F ⟶ asFibrantFibration hP G from ⟨f.hom⟩)
  have h' : comparison (hP := hP) a ha F ≫ (H.map (CQ.map f.hom) ≫ g) =
      H.map (S.map (Q.map α)) ≫ (comparison (hP := hP) a ha G ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ g) h.symm).trans (Category.assoc _ _ _))
  change shiftHomEquiv q (a F.obj).pt E hE
      (comparison (hP := hP) a ha F ≫ (H.map (CQ.map f.hom) ≫ g)) =
    H.map α ≫ shiftHomEquiv q (a G.obj).pt E hE (comparison (hP := hP) a ha G ≫ g)
  rw [h']
  exact shiftHomEquiv_source q α E hE _

/-- Every original target map retains the same complete comparison and integer shift square. -/
theorem comparisonTest_target (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') (g : cofiberHom q F E) :
    comparisonTest (hP := hP) a ha q F E' hE' (cofiberTarget q F t g) =
      fiberTarget a (q + 1) F t (comparisonTest (hP := hP) a ha q F E hE g) := by
  change shiftHomEquiv q (a F.obj).pt E' hE'
      (comparison (hP := hP) a ha F ≫ (g ≫ H.map ((integerTarget q).map t))) =
    shiftHomEquiv q (a F.obj).pt E hE (comparison (hP := hP) a ha F ≫ g) ≫
      H.map ((integerTarget (q + 1)).map t)
  rw [← Category.assoc]
  exact shiftHomEquiv_target q (a F.obj).pt t hE hE' _

/-- The actual original comparison test preserves the same ordinary null class in every degree. -/
theorem comparisonTest_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) :
    comparisonTest (hP := hP) a ha q F E hE (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj)
        ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) := by
  change shiftHomEquiv q (a F.obj).pt E hE
      (comparison (hP := hP) a ha F ≫ OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj)
        ((integerTarget q).obj E)) = _
  rw [NullHomTransport.precomp_nullHom]
  exact shiftHomEquiv_null q (a F.obj).pt E hE

/-- The same original total spectrum retains its complete integer target Hom term. -/
abbrev totalHom (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :=
  H.obj F.obj.left ⟶ H.obj ((integerTarget q).obj E)

/-- The original fiber restriction is precisely the caller's unchanged first projection. -/
def fiberRestriction (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    totalHom q F E → fiberHom a q F E := fun g => H.map (a F.obj).fst ≫ g

/-- The actual original total component acts by its full unchanged source map. -/
def totalSource (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G) (E : C.{u, v}) :
    totalHom q G E → totalHom q F E := fun g => H.map f.hom.left ≫ g

/-- Each original chosen-fiber restriction retains the complete native Arrow square. -/
theorem fiberRestriction_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (g : totalHom q G E) :
    fiberRestriction a q F E (totalSource q f E g) =
      fiberSource a ha q f E (fiberRestriction a q G E g) := by
  have h := H.congr_map (chosenFiberMap_fst f.hom (a F.obj) (a G.obj) (ha G.obj))
  simp only [Functor.map_comp] at h
  change H.map (a F.obj).fst ≫ (H.map f.hom.left ≫ g) =
    H.map (chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj)) ≫
      (H.map (a G.obj).fst ≫ g)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ g) h.symm).trans (Category.assoc _ _ _))

/-- Every actual target map retains the same original fiber projection function. -/
theorem fiberRestriction_target (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : totalHom q F E) :
    fiberRestriction a q F E' (g ≫ H.map ((integerTarget q).map t)) =
      fiberTarget a q F t (fiberRestriction a q F E g) :=
  (Category.assoc _ _ _).symm

/-- Every original caller fiber restriction retains its same null class. -/
theorem fiberRestriction_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    fiberRestriction a q F E
        (OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E) :=
  OrdinaryHoCofiberKernel.precomp_nullHom (a F.obj).fst

variable (b : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Both actual original caller fiber choices retain their full universal-property Iso. -/
def choiceIso (F : P.FullSubcategory) : (a F.obj).pt ≅ (b F.obj).pt :=
  OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
    a ha b hb F.obj

omit B in
/-- This source comparison is exactly the full native chosen-fiber choice comparison. -/
theorem choiceIso_eq_native (F : P.FullSubcategory) :
    choiceIso a ha b hb F =
      ChosenFiberNaturality.choiceIso F.obj.hom (a F.obj) (ha F.obj) (b F.obj) (hb F.obj) := by
  apply Iso.ext
  apply PullbackCone.IsLimit.hom_ext (hb F.obj)
  · change (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
      a ha b hb F.obj).hom ≫ (b F.obj).fst = _
    rw [OrdinaryHoChosenFiberMaps.choiceIso_hom_fst,
      ChosenFiberNaturality.choiceIso_hom_map, chosenFiberMap_fst]
    change (a F.obj).fst = (a F.obj).fst ≫ 𝟙 F.obj.left
    exact (Category.comp_id _).symm
  · change (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
      a ha b hb F.obj).hom ≫ (b F.obj).snd = _
    rw [OrdinaryHoChosenFiberMaps.choiceIso_hom_snd,
      ChosenFiberNaturality.choiceIso_hom_map, chosenFiberMap_snd]

/-- Both full choice functions transport every original integer chosen-fiber Hom test. -/
def choiceHomEquiv (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    fiberHom b q F E ≃ fiberHom a q F E :=
  Iso.homCongr ((H.mapIso (choiceIso a ha b hb F)).symm) (Iso.refl _)

/-- The entire forward choice function is the actual original choice map precomposition. -/
theorem choiceHomEquiv_apply (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (g : fiberHom b q F E) :
    choiceHomEquiv a ha b hb q F E g = H.map (choiceIso a ha b hb F).hom ≫ g := by
  simp only [choiceHomEquiv, Iso.homCongr_apply, Iso.symm_inv, Functor.mapIso_hom,
    Iso.refl_hom, Category.comp_id]

/-- The entire inverse retains the same original inverse caller choice map. -/
theorem choiceHomEquiv_symm_apply (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (g : fiberHom a q F E) :
    (choiceHomEquiv a ha b hb q F E).symm g = H.map (choiceIso a ha b hb F).inv ≫ g := by
  simp only [choiceHomEquiv, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_inv, Iso.refl_inv, Category.comp_id]

/-- The entire chosen Hom comparison retains every full native source
Arrow map in both original caller families. -/
theorem choiceHomEquiv_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (g : fiberHom b q G E) :
    choiceHomEquiv a ha b hb q F E (fiberSource b hb q f E g) =
      fiberSource a ha q f E (choiceHomEquiv a ha b hb q G E g) := by
  have hn : chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj) ≫
      (choiceIso a ha b hb G).hom =
    (choiceIso a ha b hb F).hom ≫ chosenFiberMap f.hom (b F.obj) (b G.obj) (hb G.obj) := by
    change chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj) ≫
        (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
          a ha b hb G.obj).hom =
      (OrdinaryHoChosenFiberMaps.choiceIso Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero
        a ha b hb F.obj).hom ≫ chosenFiberMap f.hom (b F.obj) (b G.obj) (hb G.obj)
    rw [NativeK.OriginalFiberComparison.chosenFiberMap_eq_generic a ha f.hom,
      NativeK.OriginalFiberComparison.chosenFiberMap_eq_generic b hb f.hom]
    exact OrdinaryHoChosenFiberMaps.choiceIso_naturality
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha b hb f.hom
  have h := H.congr_map hn
  simp only [Functor.map_comp] at h
  rw [choiceHomEquiv_apply, choiceHomEquiv_apply]
  change H.map (choiceIso a ha b hb F).hom ≫
      (H.map (chosenFiberMap f.hom (b F.obj) (b G.obj) (hb G.obj)) ≫ g) =
    H.map (chosenFiberMap f.hom (a F.obj) (a G.obj) (ha G.obj)) ≫
      (H.map (choiceIso a ha b hb G).hom ≫ g)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ g) h.symm).trans (Category.assoc _ _ _))

/-- Every full original integer target map retains both complete chosen Hom functions. -/
theorem choiceHomEquiv_target (q : ℤ) (F : P.FullSubcategory) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : fiberHom b q F E) :
    choiceHomEquiv a ha b hb q F E' (fiberTarget b q F t g) =
      fiberTarget a q F t (choiceHomEquiv a ha b hb q F E g) := by
  rw [choiceHomEquiv_apply, choiceHomEquiv_apply]
  exact (Category.assoc _ _ _).symm

/-- The complete inverse chosen function retains the same entire native source square. -/
theorem choiceHomEquiv_symm_source (q : ℤ) {F G : P.FullSubcategory} (f : F ⟶ G)
    (E : C.{u, v}) (g : fiberHom a q G E) :
    (choiceHomEquiv a ha b hb q F E).symm (fiberSource a ha q f E g) =
      fiberSource b hb q f E ((choiceHomEquiv a ha b hb q G E).symm g) := by
  apply (choiceHomEquiv a ha b hb q F E).injective
  rw [Equiv.apply_symm_apply, choiceHomEquiv_source, Equiv.apply_symm_apply]

/-- The inverse also retains every full original integer target action. -/
theorem choiceHomEquiv_symm_target (q : ℤ) (F : P.FullSubcategory)
    {E E' : C.{u, v}} (t : E ⟶ E') (g : fiberHom a q F E) :
    (choiceHomEquiv a ha b hb q F E').symm (fiberTarget a q F t g) =
      fiberTarget b q F t ((choiceHomEquiv a ha b hb q F E).symm g) := by
  apply (choiceHomEquiv a ha b hb q F E').injective
  rw [Equiv.apply_symm_apply, choiceHomEquiv_target, Equiv.apply_symm_apply]

/-- Both full original choice functions retain the actual caller's first projection test. -/
theorem fiberRestriction_choice (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (g : totalHom q F E) :
    choiceHomEquiv a ha b hb q F E (fiberRestriction b q F E g) =
      fiberRestriction a q F E g := by
  have hn : (choiceIso a ha b hb F).hom ≫ (b F.obj).fst = (a F.obj).fst :=
    OrdinaryHoChosenFiberMaps.choiceIso_hom_fst
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a ha b hb F.obj
  have h := H.congr_map hn
  simp only [Functor.map_comp] at h
  rw [choiceHomEquiv_apply]
  change H.map (choiceIso a ha b hb F).hom ≫ (H.map (b F.obj).fst ≫ g) =
    H.map (a F.obj).fst ≫ g
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ g) h)

/-- Its same complete inverse retains the unchanged first projection as well. -/
theorem fiberRestriction_choice_inverse (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (g : totalHom q F E) :
    (choiceHomEquiv a ha b hb q F E).symm (fiberRestriction a q F E g) =
      fiberRestriction b q F E g := by
  apply (choiceHomEquiv a ha b hb q F E).injective
  rw [Equiv.apply_symm_apply, fiberRestriction_choice]

/-- Every original chosen-fiber Hom comparison keeps the same null class. -/
theorem choiceHomEquiv_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    choiceHomEquiv a ha b hb q F E
        (OrdinaryHoCofiberKernel.nullHom (b F.obj).pt ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E) := by
  rw [choiceHomEquiv_apply]
  exact OrdinaryHoCofiberKernel.precomp_nullHom (choiceIso a ha b hb F).hom

/-- Its entire inverse keeps the same original null class as well. -/
theorem choiceHomEquiv_symm_null (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v}) :
    (choiceHomEquiv a ha b hb q F E).symm
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (b F.obj).pt ((integerTarget q).obj E) := by
  rw [choiceHomEquiv_symm_apply]
  exact OrdinaryHoCofiberKernel.precomp_nullHom (choiceIso a ha b hb F).inv

/-- The original suspended-fiber comparison test retains the whole forward change of caller. -/
theorem comparisonTest_choice (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : cofiberHom q F E) :
    choiceHomEquiv a ha b hb (q + 1) F E (comparisonTest (hP := hP) b hb q F E hE g) =
      comparisonTest (hP := hP) a ha q F E hE g := by
  let γ := (choiceIso a ha b hb F).hom
  have h : H.map (S.map (Q.map γ)) ≫ comparison (hP := hP) b hb F = comparison (hP := hP) a ha F :=
    OriginalFiberCofiberGeometry.FiberChoiceGeometry.suspendedComparison_choice
      (B := B) (J := O.{u, v}) a ha b hb (asFibrantFibration hP F)
  rw [choiceHomEquiv_apply]
  change H.map γ ≫ shiftHomEquiv q (b F.obj).pt E hE (comparison (hP := hP) b hb F ≫ g) =
    shiftHomEquiv q (a F.obj).pt E hE (comparison (hP := hP) a ha F ≫ g)
  have h' := shiftHomEquiv_source q γ E hE (comparison (hP := hP) b hb F ≫ g)
  have h'' : H.map (S.map (Q.map γ)) ≫ (comparison (hP := hP) b hb F ≫ g) =
      comparison (hP := hP) a ha F ≫ g := (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ g) h)
  exact h'.symm.trans (congrArg (shiftHomEquiv q (a F.obj).pt E hE) h'')

/-- The same full original comparison retains the complete inverse change of caller fiber. -/
theorem comparisonTest_choice_inverse (q : ℤ) (F : P.FullSubcategory) (E : C.{u, v})
    (hE : omegaProperty E) (g : cofiberHom q F E) :
    (choiceHomEquiv a ha b hb (q + 1) F E).symm (comparisonTest (hP := hP) a ha q F E hE g) =
      comparisonTest (hP := hP) b hb q F E hE g := by
  apply (choiceHomEquiv a ha b hb (q + 1) F E).injective
  rw [Equiv.apply_symm_apply, comparisonTest_choice (hP := hP)]

end General

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- Every actual caller fiber has the same original integer target test. -/
abbrev fiberHom (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :=
  General.fiberHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)

/-- The original Q cofiber has its same actual integer target test. -/
abbrev cofiberHom (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :=
  General.cofiberHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- The original suspended Q caller fiber retains its whole native Hom term. -/
abbrev suspendedFiberHom (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :=
  General.suspendedFiberHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)

/-- The actual original comparison map is retained at the unchanged caller chosen fiber. -/
abbrev comparison (F : rightArrows.{u, v}) :
    H.obj (S.obj (Q.obj (a F.obj).pt)) ⟶ H.obj (CQ.obj F.obj) :=
  General.comparison
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (F := F)

/-- Each original comparison test is its actual full precomposition function. -/
def comparisonPrecomposition (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    cofiberHom q F E → suspendedFiberHom a q F E :=
  General.comparisonPrecomposition
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)

/-- The original integer suspension function acts on that same actual comparison test. -/
def comparisonTest (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) (hE : omegaProperty E) :
    cofiberHom q F E → fiberHom a (q + 1) F E :=
  General.comparisonTest
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- Every complete original K-right Arrow square acts by its actual chosen-fiber map. -/
def fiberSource (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G) (E : C.{u, v}) :
    fiberHom a q G E → fiberHom a q F E :=
  General.fiberSource
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)

/-- Every original whole Arrow square retains the unchanged original Q-cofiber map. -/
def cofiberSource (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G) (E : C.{u, v}) :
    cofiberHom q G E → cofiberHom q F E :=
  General.cofiberSource
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)

/-- Every whole target map retains its actual integer target functor action on the fiber. -/
def fiberTarget (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    fiberHom a q F E → fiberHom a q F E' :=
  General.fiberTarget
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)

/-- The original Q-cofiber target action keeps the same entire integer target map. -/
def cofiberTarget (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E') :
    cofiberHom q F E → cofiberHom q F E' :=
  General.cofiberTarget
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)

/-- Both original comparison and suspension Hom functions retain the whole native source square. -/
theorem comparisonTest_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (hE : omegaProperty E) (g : cofiberHom q G E) :
    comparisonTest a ha q F E hE (cofiberSource q f E g) =
      fiberSource a ha (q + 1) f E (comparisonTest a ha q G E hE g) :=
  General.comparisonTest_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (hE := hE)
    (g := g)

/-- Every original target map retains the same complete comparison and integer shift square. -/
theorem comparisonTest_target (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (hE : omegaProperty E) (hE' : omegaProperty E') (g : cofiberHom q F E) :
    comparisonTest a ha q F E' hE' (cofiberTarget q F t g) =
      fiberTarget a (q + 1) F t (comparisonTest a ha q F E hE g) :=
  General.comparisonTest_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (hE := hE)
    (hE' := hE')
    (g := g)

/-- The actual original comparison test preserves the same ordinary null class in every degree. -/
theorem comparisonTest_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) :
    comparisonTest a ha q F E hE (OrdinaryHoCofiberKernel.nullHom (CQ.obj F.obj)
        ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget (q + 1)).obj E) :=
  General.comparisonTest_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)

/-- The same original total spectrum retains its complete integer target Hom term. -/
abbrev totalHom (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :=
  General.totalHom
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (E := E)

/-- The original fiber restriction is precisely the caller's unchanged first projection. -/
def fiberRestriction (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    totalHom q F E → fiberHom a q F E :=
  General.fiberRestriction
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)

/-- The actual original total component acts by its full unchanged source map. -/
def totalSource (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G) (E : C.{u, v}) :
    totalHom q G E → totalHom q F E :=
  General.totalSource
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)

/-- Each original chosen-fiber restriction retains the complete native Arrow square. -/
theorem fiberRestriction_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (g : totalHom q G E) :
    fiberRestriction a q F E (totalSource q f E g) =
      fiberSource a ha q f E (fiberRestriction a q G E g) :=
  General.fiberRestriction_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (g := g)

/-- Every actual target map retains the same original fiber projection function. -/
theorem fiberRestriction_target (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : totalHom q F E) :
    fiberRestriction a q F E' (g ≫ H.map ((integerTarget q).map t)) =
      fiberTarget a q F t (fiberRestriction a q F E g) :=
  General.fiberRestriction_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- Every original caller fiber restriction retains its same null class. -/
theorem fiberRestriction_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    fiberRestriction a q F E
        (OrdinaryHoCofiberKernel.nullHom F.obj.left ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E) :=
  General.fiberRestriction_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (q := q)
    (F := F)
    (E := E)

variable (b : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Both actual original caller fiber choices retain their full universal-property Iso. -/
def choiceIso (F : rightArrows.{u, v}) : (a F.obj).pt ≅ (b F.obj).pt :=
  General.choiceIso
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (F := F)

omit B in
/-- This source comparison is exactly the full native chosen-fiber choice comparison. -/
theorem choiceIso_eq_native (F : rightArrows.{u, v}) :
    choiceIso a ha b hb F =
      ChosenFiberNaturality.choiceIso F.obj.hom (a F.obj) (ha F.obj) (b F.obj) (hb F.obj) :=
  General.choiceIso_eq_native
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (F := F)

/-- Both full choice functions transport every original integer chosen-fiber Hom test. -/
def choiceHomEquiv (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    fiberHom b q F E ≃ fiberHom a q F E :=
  General.choiceHomEquiv
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)

/-- The entire forward choice function is the actual original choice map precomposition. -/
theorem choiceHomEquiv_apply (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (g : fiberHom b q F E) :
    choiceHomEquiv a ha b hb q F E g = H.map (choiceIso a ha b hb F).hom ≫ g :=
  General.choiceHomEquiv_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- The entire inverse retains the same original inverse caller choice map. -/
theorem choiceHomEquiv_symm_apply (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (g : fiberHom a q F E) :
    (choiceHomEquiv a ha b hb q F E).symm g = H.map (choiceIso a ha b hb F).inv ≫ g :=
  General.choiceHomEquiv_symm_apply
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- The entire chosen Hom comparison retains every full native source
Arrow map in both original caller families. -/
theorem choiceHomEquiv_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (g : fiberHom b q G E) :
    choiceHomEquiv a ha b hb q F E (fiberSource b hb q f E g) =
      fiberSource a ha q f E (choiceHomEquiv a ha b hb q G E g) :=
  General.choiceHomEquiv_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (g := g)

/-- Every full original integer target map retains both complete chosen Hom functions. -/
theorem choiceHomEquiv_target (q : ℤ) (F : rightArrows.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : fiberHom b q F E) :
    choiceHomEquiv a ha b hb q F E' (fiberTarget b q F t g) =
      fiberTarget a q F t (choiceHomEquiv a ha b hb q F E g) :=
  General.choiceHomEquiv_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- The complete inverse chosen function retains the same entire native source square. -/
theorem choiceHomEquiv_symm_source (q : ℤ) {F G : rightArrows.{u, v}} (f : F ⟶ G)
    (E : C.{u, v}) (g : fiberHom a q G E) :
    (choiceHomEquiv a ha b hb q F E).symm (fiberSource a ha q f E g) =
      fiberSource b hb q f E ((choiceHomEquiv a ha b hb q G E).symm g) :=
  General.choiceHomEquiv_symm_source
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (G := G)
    (f := f)
    (E := E)
    (g := g)

/-- The inverse also retains every full original integer target action. -/
theorem choiceHomEquiv_symm_target (q : ℤ) (F : rightArrows.{u, v})
    {E E' : C.{u, v}} (t : E ⟶ E') (g : fiberHom a q F E) :
    (choiceHomEquiv a ha b hb q F E').symm (fiberTarget a q F t g) =
      fiberTarget b q F t ((choiceHomEquiv a ha b hb q F E).symm g) :=
  General.choiceHomEquiv_symm_target
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (E' := E')
    (t := t)
    (g := g)

/-- Both full original choice functions retain the actual caller's first projection test. -/
theorem fiberRestriction_choice (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (g : totalHom q F E) :
    choiceHomEquiv a ha b hb q F E (fiberRestriction b q F E g) =
      fiberRestriction a q F E g :=
  General.fiberRestriction_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- Its same complete inverse retains the unchanged first projection as well. -/
theorem fiberRestriction_choice_inverse (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (g : totalHom q F E) :
    (choiceHomEquiv a ha b hb q F E).symm (fiberRestriction a q F E g) =
      fiberRestriction b q F E g :=
  General.fiberRestriction_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (g := g)

/-- Every original chosen-fiber Hom comparison keeps the same null class. -/
theorem choiceHomEquiv_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    choiceHomEquiv a ha b hb q F E
        (OrdinaryHoCofiberKernel.nullHom (b F.obj).pt ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E) :=
  General.choiceHomEquiv_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)

/-- Its entire inverse keeps the same original null class as well. -/
theorem choiceHomEquiv_symm_null (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v}) :
    (choiceHomEquiv a ha b hb q F E).symm
        (OrdinaryHoCofiberKernel.nullHom (a F.obj).pt ((integerTarget q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (b F.obj).pt ((integerTarget q).obj E) :=
  General.choiceHomEquiv_symm_null
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)

/-- The original suspended-fiber comparison test retains the whole forward change of caller. -/
theorem comparisonTest_choice (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : cofiberHom q F E) :
    choiceHomEquiv a ha b hb (q + 1) F E (comparisonTest b hb q F E hE g) =
      comparisonTest a ha q F E hE g :=
  General.comparisonTest_choice
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

/-- The same full original comparison retains the complete inverse change of caller fiber. -/
theorem comparisonTest_choice_inverse (q : ℤ) (F : rightArrows.{u, v}) (E : C.{u, v})
    (hE : omegaProperty E) (g : cofiberHom q F E) :
    (choiceHomEquiv a ha b hb (q + 1) F E).symm (comparisonTest a ha q F E hE g) =
      comparisonTest b hb q F E hE g :=
  General.comparisonTest_choice_inverse
    (P := NativeK.OriginalFiberComparison.rightArrowProperty orthogonalFamily.{u, v})
    (hP := ChosenFiberHomTests.rightArrows_le_fibrantFibrations (B := B))
    (B := B)
    (a := a)
    (ha := ha)
    (b := b)
    (hb := hb)
    (q := q)
    (F := F)
    (E := E)
    (hE := hE)
    (g := g)

end PointedCGWH.Spectra.Orthogonal.ChosenFiberHomTests
