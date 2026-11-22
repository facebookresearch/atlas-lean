/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyInjectiveComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCartesianModel
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCofibrant
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.IndexedFreeMappingData
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalRezkLocalizerComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalCartesianLocalPowers
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.RowRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalExponentClosure
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingRepresentableProducts
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalCartesianCriterionFinish
import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Simplicial-space powers and Cartesian complete Segal spaces

Original true simplicial-space powers and Cartesian CSS compatibility.

The simplex representable comparison and GLOBAL lifting bridge transport
the proved representable-product criterion to arbitrary true exponents.
The Cartesian laws use the original selected Rezk model and its class getters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory MonoidalClosed HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner SimplicialSpace.Cartesian
  SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.hasEnd
  SimplicialPresheaf.InjectiveKan.modelCategory

namespace TrueSpacePowerPreparation

/-- The original spine family, without adding an E-completeness test. -/
def spineFamily : {n : ℕ // 2 ≤ n} →
    Arrow (SimplicialPresheaf.{u} SimplexCategory) :=
  fun n => Arrow.mk (SSet.Rezk.segalMap n.1)

/-- The original shrunk Hom representable is the actual discrete outer simplex.
The inverse uses the SAME original Hom equivalence; every inner map stays constant. -/
def simplexRepresentableIso (d : SimplexCategory) :
    SimplicialPresheaf.discreteYoneda.{u}.obj d ≅
      (SimplicialSpace.discreteInnerFunctor.obj (SSet.stdSimplex.{u}.obj d)).diagram := by
  change (shrinkYoneda.{u}.obj d ⋙ Functor.const SimplexCategoryᵒᵖ) ≅
    (uliftYoneda.{u}.obj d ⋙ Functor.const SimplexCategoryᵒᵖ)
  exact Functor.isoWhiskerRight
    ((uliftYonedaIsoShrinkYoneda (C := SimplexCategory)).app d).symm
    (Functor.const SimplexCategoryᵒᵖ)

private theorem designation_rlp_iff
    (Q : MorphismProperty SimplicialSpace.{u}) [Q.RespectsIso]
    {A B : SimplicialPresheaf.{u} SimplexCategory} (p : A ⟶ B) :
    (Q.inverseImage SimplicialSpace.ofSimplicialObject).rlp p ↔
      Q.rlp (SimplicialSpace.ofSimplicialObject.map p) := by
  let E := SimplicialSpace.equivalenceSimplicialObject.{u}.symm
  constructor
  · intro hp X Y i hi
    let e : Arrow.mk (E.functor.map (E.inverse.map i)) ≅ Arrow.mk i :=
      Arrow.isoMk (E.counitIso.app X) (E.counitIso.app Y)
        (E.counitIso.hom.naturality i).symm
    have hImage : Q (E.functor.map (E.inverse.map i)) :=
      (Q.arrow_mk_iso_iff e).mpr hi
    have hLift : HasLiftingProperty (E.inverse.map i) p := hp _ hImage
    have hMapped : HasLiftingProperty (E.functor.map (E.inverse.map i))
        (E.functor.map p) :=
      (E.functor.hasLiftingProperty_iff_of_isEquivalence _ _).mpr hLift
    exact (HasLiftingProperty.iff_of_arrow_iso_left e (E.functor.map p)).mp hMapped
  · intro hp X Y i hi
    exact (E.functor.hasLiftingProperty_iff_of_isEquivalence i p).mp
      (hp (E.functor.map i) hi)

private theorem baselineFibration_iff
    {A B : SimplicialPresheaf.{u} SimplexCategory} (p : A ⟶ B) :
    letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    SimplicialPresheaf.InjectiveKan.injectiveFibrations SimplexCategory p ↔
      fibrations SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map p) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let Q := trivialCofibrations SimplicialSpace.{u}
  have hQ : Q.inverseImage SimplicialSpace.ofSimplicialObject =
      SimplicialPresheaf.InjectiveKan.trivialMonomorphisms SimplexCategory := by
    ext A B f
    change (cofibrations SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map f) ∧
      weakEquivalences SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map f)) ↔ _
    rw [SimplicialSpace.ReedyModel.selectedReedy_injective_classes.1,
      SimplicialSpace.ReedyModel.selectedReedy_injective_classes.2.1]
    change (Mono (SimplicialSpace.ofSimplicialObject.map f) ∧
      ∀ n : SimplexCategoryᵒᵖ, SSet.realizationWeakEquivalences (f.app n)) ↔
      (Mono f ∧ ∀ n : SimplexCategoryᵒᵖ, SSet.realizationWeakEquivalences (f.app n))
    exact and_congr
      (SimplicialSpace.mono_forget_map_iff (SimplicialSpace.ofSimplicialObject.map f)).symm
      Iff.rfl
  change (SimplicialPresheaf.InjectiveKan.trivialMonomorphisms SimplexCategory).rlp p ↔ _
  rw [← hQ, ← trivialCofibrations_rlp SimplicialSpace.{u}]
  exact designation_rlp_iff Q p

/-- GLOBAL baseline fibrancy transports through the original designation and
the actual terminal image; it is not a coefficientwise-fibrancy converse. -/
theorem baselineFibrant_iff (Z : SimplicialPresheaf.{u} SimplexCategory) :
    IsFibrant Z ↔
      (letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
       IsFibrant (SimplicialSpace.ofSimplicialObject.obj Z)) := by
  let : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have hBase : IsFibrant Z ↔
      SimplicialPresheaf.InjectiveKan.injectiveFibrations SimplexCategory (terminal.from Z) := by
    rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff]
    change
        (SimplicialPresheaf.InjectiveKan.data.{u}
          SimplexCategory).model.categoryWithFibrations.fibrations
      (terminal.from Z) ↔ _
    rw [(SimplicialPresheaf.InjectiveKan.data.{u} SimplexCategory).fibrations_eq]
  let ht : IsTerminal
      (SimplicialSpace.ofSimplicialObject.obj (⊤_ (SimplicialPresheaf.{u} SimplexCategory))) :=
    (terminalIsTerminal (C := SimplicialPresheaf.{u} SimplexCategory)).isTerminalObj
      SimplicialSpace.ofSimplicialObject.{u} _
  have hDesignated : IsFibrant (SimplicialSpace.ofSimplicialObject.obj Z) ↔
      fibrations SimplicialSpace.{u} (SimplicialSpace.ofSimplicialObject.map
          (terminal.from Z)) := by
    rw [isFibrant_iff_of_isTerminal
      (SimplicialSpace.ofSimplicialObject.map (terminal.from Z)) ht, fibration_iff]
  exact hBase.trans ((baselineFibration_iff (terminal.from Z)).trans hDesignated.symm)

private def coefficientPrecompArrowIso
    {A B : SimplicialPresheaf.{u} SimplexCategory} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} SimplexCategory) :
    Arrow.mk (SimplicialPresheaf.innerHomPre f Z) ≅
      Arrow.mk ((SimplicialSpace.innerHomFunctor.map
        (SimplicialSpace.ofSimplicialObject.map f).op).app
        (SimplicialSpace.ofSimplicialObject.obj Z)) :=
  Arrow.isoMk
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso
      (SimplicialSpace.ofSimplicialObject.obj B) (SimplicialSpace.ofSimplicialObject.obj Z))
    (SimplicialPresheaf.IndexedFreeMapping.rawEndIso
      (SimplicialSpace.ofSimplicialObject.obj A) (SimplicialSpace.ofSimplicialObject.obj Z))
    ((SimplicialPresheaf.IndexedFreeMapping.rawEnd_naturality.1
      (SimplicialSpace.ofSimplicialObject.map f)
      (SimplicialSpace.ofSimplicialObject.obj Z)).1).symm

/-- The original spine-local GLOBAL targets are exactly the named RF Segal spaces. -/
theorem spineLocalFibrant_iff (Z : SimplicialPresheaf.{u} SimplexCategory) :
    SimplicialPresheaf.InjectiveKan.isOriginalLocalFibrant spineFamily Z ↔
      SimplicialSpace.segalSpaces (SimplicialSpace.ofSimplicialObject.obj Z) := by
  change (IsFibrant Z ∧ ∀ n : {n : ℕ // 2 ≤ n},
    SSet.realizationWeakEquivalences
      (SimplicialPresheaf.innerHomPre (SSet.Rezk.segalMap.{u} n.1) Z)) ↔ _
  change _ ↔ ((letI : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    IsFibrant (SimplicialSpace.ofSimplicialObject.obj Z)) ∧ ∀ n : ℕ, 2 ≤ n →
      SSet.realizationWeakEquivalences
        ((SimplicialSpace.innerHomFunctor.map
          (SimplicialSpace.ofSimplicialObject.map (SSet.Rezk.segalMap.{u} n)).op).app
          (SimplicialSpace.ofSimplicialObject.obj Z)))
  apply and_congr (baselineFibrant_iff Z)
  constructor
  · intro h n hn
    exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (coefficientPrecompArrowIso (SSet.Rezk.segalMap.{u} n) Z)).mp (h ⟨n, hn⟩)
  · intro h n
    exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (coefficientPrecompArrowIso (SSet.Rezk.segalMap.{u} n.1) Z)).mpr (h n.1 n.2)


open SimplicialPresheaf SimplicialPresheaf.InjectiveKan
open SimplicialSpace

/-- Both original endpoints of a family map use the actual representable comparison. -/
def representableTensorArrowIso {I : Type} (S : I → Arrow (SimplicialPresheaf.{u} SimplexCategory))
    (a : I) (d : SimplexCategory) :
    Arrow.mk ((S a).hom ▷ discreteYoneda.obj d) ≅
      Arrow.mk ((S a).hom ▷ (discreteInnerFunctor.obj (SSet.stdSimplex.obj d)).diagram) :=
  Arrow.isoMk
    ((tensorLeft (S a).left).mapIso (simplexRepresentableIso d))
    ((tensorLeft (S a).right).mapIso (simplexRepresentableIso d))
    (by ext m k x; rfl)

/-- Original Segal spine products satisfy the criterion on EVERY original global local target. -/
theorem spineRepresentableCriterion :
    ∀ a d, originalLocalEquivalences spineFamily
      ((spineFamily.{u} a).hom ▷ discreteYoneda.obj d) := by
  intro a d Z hZ
  let W := ofSimplicialObject.obj Z
  let K := SSet.stdSimplex.{u}.obj d
  let A := discreteInnerFunctor.obj K
  let b := ofSimplicialObject.map (spineFamily.{u} a).hom
  have hW : segalSpaces W := (spineLocalFibrant_iff Z).mp hZ
  let e : Arrow.mk (innerHomPre ((spineFamily.{u} a).hom ▷ A.diagram) Z) ≅
      Arrow.mk ((boxLeftDivisionFunctor.map
        (SegalExponentSupport.spineProductMap K a.1).op).app W) :=
    (SegalExponentRawAssembly.powerPrecompRawArrowIso A b W).symm ≪≫
      SegalExponentRawAssembly.outerPowerSpineArrowIso K a.1 W
  have hRight : SSet.realizationWeakEquivalences
      (innerHomPre ((spineFamily.{u} a).hom ▷ A.diagram) Z) :=
    (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).mpr
      (SegalExponentSupport.spineProduct_realizationWeak W hW K a.1 a.2)
  let r := representableTensorArrowIso spineFamily a d
  exact (rawPrecomp_weak_iff_of_sourceComparison r.hom
    ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso r.hom.left)
    ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso r.hom.right)
    Z hZ.1).mpr hRight

/-- Both original full-CSS branches satisfy the SAME criterion, including the full E endpoint. -/
theorem completeRepresentableCriterion :
    ∀ a d, originalLocalEquivalences SSet.Rezk.localizingMap.{u}
      ((SSet.Rezk.localizingMap.{u} a).hom ▷ discreteYoneda.obj d) := by
  intro a d
  let r := representableTensorArrowIso SSet.Rezk.localizingMap.{u} a d
  have hRight : originalLocalEquivalences SSet.Rezk.localizingMap.{u}
      ((SSet.Rezk.localizingMap.{u} a).hom ▷
        (discreteInnerFunctor.obj (SSet.stdSimplex.{u}.obj d)).diagram) := by
    apply (OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak _).mpr
    cases d with
    | mk m =>
      change rezkWeakEquivalences
        (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} a).hom ▷
          ofSimplicialObject.obj (SSet.Rezk.representable.{u} m))
      exact scalarLocalizingProduct_rezkWeak a m
  intro Z hZ
  exact (rawPrecomp_weak_iff_of_sourceComparison r.hom
    ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso r.hom.left)
    ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso r.hom.right)
    Z hZ.1).mpr (hRight Z hZ)

private theorem anyPower_reedyFibrant (A W : SimplicialSpace.{u})
    (hW : letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
      IsFibrant W) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant ((ihom A).obj W) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    ReedyModel.cartesian_isClosedSymmetricMonoidalModelCategory
  let : IsCofibrant A := ReedyModel.isCofibrant A
  let : Adjunction.IsQuillenAdjunction (ihom.adjunction A) :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant A
  exact (Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := ihom.adjunction A)) hW

/-- The Segal clause of Rezk Corollary7.3, proved via the original representable-product
criterion. -/
theorem arbitrarySpacePower_segal (A W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    segalSpaces ((ihom A).obj W) := by
  let E := SimplicialPresheaf.exponential A.diagram W.diagram
  have hZ : isOriginalLocalFibrant spineFamily W.diagram :=
    (spineLocalFibrant_iff W.diagram).mpr hW
  have hE : isOriginalLocalFibrant spineFamily E :=
    originalRepresentableCriterion_powerLocalFibrant spineFamily
      spineRepresentableCriterion A.diagram W.diagram hZ
  let e := (SegalExponentRawAssembly.chosenPowerRawIso A).app W
  have hChosen : IsFibrant ((ihom A).obj W).diagram :=
    (baselineFibrant_iff ((ihom A).obj W).diagram).mpr
      (anyPower_reedyFibrant A W hW.1)
  have hLocal : isOriginalLocalFibrant spineFamily ((ihom A).obj W).diagram :=
    (isOriginalLocalFibrant_iff_of_targetWeak spineFamily e.hom
      ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso e.hom)
      hChosen hE.1).mpr hE
  exact (spineLocalFibrant_iff ((ihom A).obj W).diagram).mp hLocal

/-- FULL Corollary7.3 completeness closure retains BOTH original localizing branches. -/
theorem arbitrarySpacePower_completeSegal (A W : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) : completeSegalSpaces ((ihom A).obj W) := by
  let S := SSet.Rezk.localizingMap.{u}
  let E := SimplicialPresheaf.exponential A.diagram W.diagram
  have hZ : isOriginalLocalFibrant S W.diagram :=
    (OriginalRezkLocalizer.coefficientLocalFibrant_iff_completeSegalSpaces W.diagram).mpr hW
  have hE : isOriginalLocalFibrant S E :=
    originalRepresentableCriterion_powerLocalFibrant S
      completeRepresentableCriterion A.diagram W.diagram hZ
  let e := (SegalExponentRawAssembly.chosenPowerRawIso A).app W
  have hChosen : IsFibrant ((ihom A).obj W).diagram :=
    (baselineFibrant_iff ((ihom A).obj W).diagram).mpr
      (anyPower_reedyFibrant A W hW.1)
  have hLocal : isOriginalLocalFibrant S ((ihom A).obj W).diagram :=
    (isOriginalLocalFibrant_iff_of_targetWeak S e.hom
      ((weakEquivalences (SimplicialPresheaf.{u} SimplexCategory)).of_isIso e.hom)
      hChosen hE.1).mpr hE
  exact (OriginalRezkLocalizer.coefficientLocalFibrant_iff_completeSegalSpaces
    ((ihom A).obj W).diagram).mp hLocal

/-- The original spine-S model's full PP iff uses the internally proved criterion. -/
theorem spineModel_pushoutProduct_and_pullbackHom :
    letI : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
        originalLocalSmithModel spineFamily
    CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} SimplexCategory) ∧
      CartesianPullbackHomAxiom (C := SimplicialPresheaf.{u} SimplexCategory) := by
  let : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
      originalLocalSmithModel spineFamily
  have hPP : CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} SimplexCategory) :=
    (originalLocalCartesianPP_iff_representableCriterion spineFamily.{u}).mpr
      spineRepresentableCriterion.{u}
  exact ⟨hPP, cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp hPP⟩

/-- The original full-CSS coefficient model satisfies ALL three PP and PB-Hom clauses. -/
theorem completeCoefficientModel_pushoutProduct_and_pullbackHom :
    letI : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
      originalLocalSmithModel SSet.Rezk.localizingMap.{u}
    CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} SimplexCategory) ∧
      CartesianPullbackHomAxiom (C := SimplicialPresheaf.{u} SimplexCategory) := by
  let : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
    originalLocalSmithModel SSet.Rezk.localizingMap.{u}
  have hPP : CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} SimplexCategory) :=
    (originalLocalCartesianPP_iff_representableCriterion
      SSet.Rezk.localizingMap.{u}).mpr completeRepresentableCriterion.{u}
  exact ⟨hPP, cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp hPP⟩

private def forgetPushoutData {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)).PushoutObjObj i.hom j.hom where
  pt := sq.pt.diagram
  inl := sq.inl.hom
  inr := sq.inr.hom
  isPushout := sq.isPushout.map forget
  ι := sq.ι.hom
  inl_ι := by
    change forget.map sq.inl ≫ forget.map sq.ι =
      forget.map ((curriedTensor SimplicialSpace.{u}).obj B |>.map j)
    exact ((forget.map_comp sq.inl sq.ι).symm.trans
      (congrArg (fun f => forget.map f) sq.inl_ι))
  inr_ι := by
    change forget.map sq.inr ≫ forget.map sq.ι =
      forget.map (((curriedTensor SimplicialSpace.{u}).map i).app L)
    exact ((forget.map_comp sq.inr sq.ι).symm.trans
      (congrArg (fun f => forget.map f) sq.inr_ι))

private noncomputable def designatePushoutData {A B K L : SimplicialPresheaf.{u} SimplexCategory}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)).PushoutObjObj i j) :
    (curriedTensor SimplicialSpace.{u}).PushoutObjObj
      (ofSimplicialObject.{u}.map i) (ofSimplicialObject.{u}.map j) := by
  let F : SimplicialPresheaf.{u} SimplexCategory ⥤ SimplicialSpace.{u} :=
    ofSimplicialObject.{u}
  exact
    { pt := F.obj sq.pt
      inl := F.map sq.inl
      inr := F.map sq.inr
      isPushout := sq.isPushout.map F
      ι := F.map sq.ι
      inl_ι := (F.map_comp sq.inl sq.ι).symm.trans
        (congrArg (fun f => F.map f) sq.inl_ι)
      inr_ι := (F.map_comp sq.inr sq.ι).symm.trans
        (congrArg (fun f => F.map f) sq.inr_ι) }

private def forgetPushoutArrowIso {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    Arrow.mk sq.ι.hom ≅ (Arrow.mk i.hom □ Arrow.mk j.hom) := by
  let sq₀ := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)) i.hom j.hom
  change Arrow.mk (forgetPushoutData i j sq).ι ≅ Arrow.mk sq₀.ι
  exact Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor (SimplicialPresheaf.{u} SimplexCategory))
    (f₁ := Arrow.mk i.hom) (f₁' := Arrow.mk i.hom) (f₂ := Arrow.mk j.hom)
    (forgetPushoutData i j sq) sq₀ (Iso.refl (Arrow.mk i.hom))

private def designatePushoutArrowIso {A B K L : SimplicialPresheaf.{u} SimplexCategory}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)).PushoutObjObj i j) :
    Arrow.mk (ofSimplicialObject.map sq.ι) ≅
      (Arrow.mk (ofSimplicialObject.map i) □ Arrow.mk (ofSimplicialObject.map j)) := by
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u})
    (ofSimplicialObject.map i) (ofSimplicialObject.map j)
  change Arrow.mk (designatePushoutData i j sq).ι ≅ Arrow.mk sq₀.ι
  exact Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SimplicialSpace.{u})
    (f₁ := Arrow.mk (ofSimplicialObject.map i))
    (f₁' := Arrow.mk (ofSimplicialObject.map i))
    (f₂ := Arrow.mk (ofSimplicialObject.map j))
    (designatePushoutData i j sq) sq₀ (Iso.refl (Arrow.mk (ofSimplicialObject.map i)))

private theorem actualRezkCof_iff {A B : SimplicialSpace.{u}} (f : A ⟶ B) :
    RezkModel.modelCategory.categoryWithCofibrations.cofibrations f ↔
      (originalLocalSmithModel
          SSet.Rezk.localizingMap.{u}).categoryWithCofibrations.cofibrations f.hom := by
  have h := OriginalRezkLocalizer.coefficientModel_classes_and_equivalence.{u}.1
  rw [h]
  rfl

private theorem actualRezkWeak_iff {A B : SimplicialSpace.{u}} (f : A ⟶ B) :
    RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔
      (originalLocalSmithModel
          SSet.Rezk.localizingMap.{u}).categoryWithWeakEquivalences.weakEquivalences f.hom := by
  have h := OriginalRezkLocalizer.coefficientModel_classes_and_equivalence.{u}.2.1
  rw [h]
  rfl

private theorem actualRezkTrivialCof_iff {A B : SimplicialSpace.{u}} (f : A ⟶ B) :
    (RezkModel.modelCategory.categoryWithCofibrations.cofibrations ⊓
      RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences) f ↔
    ((originalLocalSmithModel SSet.Rezk.localizingMap.{u}).categoryWithCofibrations.cofibrations ⊓
      (originalLocalSmithModel
          SSet.Rezk.localizingMap.{u}).categoryWithWeakEquivalences.weakEquivalences) f.hom :=
  and_congr (actualRezkCof_iff f) (actualRezkWeak_iff f)

/-- The actual named Rezk model's whole PP axiom is transported through its genuine class
getters. -/
theorem actualRezkPushoutProduct_iff_coefficientPushoutProduct :
    (letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory;
      CartesianPushoutProductAxiom (C := SimplicialSpace.{u})) ↔
    (letI : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
      originalLocalSmithModel SSet.Rezk.localizingMap.{u};
      CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} SimplexCategory)) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
    originalLocalSmithModel SSet.Rezk.localizingMap.{u}
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout
        (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)) i j
      have hx := h.1 (ofSimplicialObject.map i) (ofSimplicialObject.map j)
        ((actualRezkCof_iff _).mpr hi) ((actualRezkCof_iff _).mpr hj)
      have hm := ((cofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
        (designatePushoutArrowIso i j sq)).mpr hx
      exact (actualRezkCof_iff (ofSimplicialObject.map sq.ι)).mp hm
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout
        (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)) i j
      have hx := h.2.1 (ofSimplicialObject.map i) (ofSimplicialObject.map j)
        ((actualRezkTrivialCof_iff _).mpr hi) ((actualRezkCof_iff _).mpr hj)
      have hm := ((trivialCofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
        (designatePushoutArrowIso i j sq)).mpr hx
      exact (actualRezkTrivialCof_iff (ofSimplicialObject.map sq.ι)).mp hm
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout
        (curriedTensor (SimplicialPresheaf.{u} SimplexCategory)) i j
      have hx := h.2.2 (ofSimplicialObject.map i) (ofSimplicialObject.map j)
        ((actualRezkCof_iff _).mpr hi) ((actualRezkTrivialCof_iff _).mpr hj)
      have hm := ((trivialCofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
        (designatePushoutArrowIso i j sq)).mpr hx
      exact (actualRezkTrivialCof_iff (ofSimplicialObject.map sq.ι)).mp hm
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j
      have hx := h.1 i.hom j.hom ((actualRezkCof_iff i).mp hi) ((actualRezkCof_iff j).mp hj)
      have hm := ((cofibrations (SimplicialPresheaf.{u} SimplexCategory)).arrow_mk_iso_iff
        (forgetPushoutArrowIso i j sq)).mpr hx
      exact (actualRezkCof_iff sq.ι).mpr hm
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j
      have hx := h.2.1 i.hom j.hom ((actualRezkTrivialCof_iff i).mp hi)
          ((actualRezkCof_iff j).mp hj)
      have hm := ((trivialCofibrations (SimplicialPresheaf.{u} SimplexCategory)).arrow_mk_iso_iff
        (forgetPushoutArrowIso i j sq)).mpr hx
      exact (actualRezkTrivialCof_iff sq.ι).mpr hm
    · intro A B K L i j hi hj
      let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j
      have hx := h.2.2 i.hom j.hom ((actualRezkCof_iff i).mp hi)
          ((actualRezkTrivialCof_iff j).mp hj)
      have hm := ((trivialCofibrations (SimplicialPresheaf.{u} SimplexCategory)).arrow_mk_iso_iff
        (forgetPushoutArrowIso i j sq)).mpr hx
      exact (actualRezkTrivialCof_iff sq.ι).mpr hm

/-- Full named-CSS Cartesian PP compatibility is the exact original representable criterion. -/
theorem actualRezkPushoutProduct_iff_originalCriterion :
    (letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory;
      CartesianPushoutProductAxiom (C := SimplicialSpace.{u})) ↔
      ∀ a d, originalLocalEquivalences SSet.Rezk.localizingMap.{u}
        ((SSet.Rezk.localizingMap.{u} a).hom ▷ discreteYoneda.obj d) :=
  actualRezkPushoutProduct_iff_coefficientPushoutProduct.trans
    (originalLocalCartesianPP_iff_representableCriterion SSet.Rezk.localizingMap.{u})

/-- ALL three PP and PB-Hom clauses hold in the SAME named Rezk model. -/
theorem actualRezkPushoutProduct_and_pullbackHom :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    CartesianPushoutProductAxiom (C := SimplicialSpace.{u}) ∧
      CartesianPullbackHomAxiom (C := SimplicialSpace.{u}) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  have hPP : CartesianPushoutProductAxiom (C := SimplicialSpace.{u}) :=
    actualRezkPushoutProduct_iff_originalCriterion.{u}.mpr completeRepresentableCriterion.{u}
  exact ⟨hPP, cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp hPP⟩

/-- Compatibility name for cofibrancy in the selected Rezk model. -/
theorem actualRezk_isCofibrant (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    IsCofibrant X := RezkModel.isCofibrant X

/-- The complete Cartesian closed model witness belongs to the actual selected Rezk model. -/
theorem actualRezk_closedSymmetricMonoidalModel :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let : IsCofibrant (𝟙_ SimplicialSpace.{u}) := actualRezk_isCofibrant _
  have h := actualRezkPushoutProduct_and_pullbackHom.1
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    SimplicialSpace.{u}
    (by intro A B K L i j hi hj; exact h.1 i j hi hj)
    (by intro A B K L i j hi hj; exact h.2.1 i j hi hj)
    (by intro A B K L i j hi hj; exact h.2.2 i j hi hj)

private def samePushoutArrowIso {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    Arrow.mk sq.ι ≅ (Arrow.mk i □ Arrow.mk j) := by
  let sq₀ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SimplicialSpace.{u}) i j
  change Arrow.mk sq.ι ≅ Arrow.mk sq₀.ι
  exact Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SimplicialSpace.{u})
    (f₁ := Arrow.mk i) (f₁' := Arrow.mk i) (f₂ := Arrow.mk j)
    sq sq₀ (Iso.refl (Arrow.mk i))

/-- The SAME supplied original pushout corner is Cof in the actual Rezk model. -/
theorem actualRezk_suppliedPushout_cofibration {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    cofibrations SimplicialSpace.{u} i → cofibrations SimplicialSpace.{u} j →
      cofibrations SimplicialSpace.{u} sq.ι := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hj
  exact ((cofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePushoutArrowIso i j sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.1.1 i j hi hj)

/-- Left triviality is retained for the SAME supplied original pushout and both factor maps. -/
theorem actualRezk_suppliedPushout_trivialLeft {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → cofibrations SimplicialSpace.{u} j →
      trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hj
  exact ((trivialCofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePushoutArrowIso i j sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.1.2.1 i j hi hj)

/-- Right triviality is retained for the SAME supplied original pushout and both factor maps. -/
theorem actualRezk_suppliedPushout_trivialRight {A B K L : SimplicialSpace.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj i j) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialCofibrations SimplicialSpace.{u} j →
      trivialCofibrations SimplicialSpace.{u} sq.ι := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hj
  exact ((trivialCofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePushoutArrowIso i j sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.1.2.2 i j hi hj)

private def samePullbackArrowIso {A B X Y : SimplicialSpace.{u}}
    (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    Arrow.mk sq.π ≅ ((op (Arrow.mk i)) ⋔ Arrow.mk p) := by
  let sq₀ := Functor.PullbackObjObj.ofHasPullback
    (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SimplicialSpace.{u}) i p
  change Arrow.mk sq.π ≅ Arrow.mk sq₀.π
  exact Functor.PullbackObjObj.π_iso_of_iso_left
    (G := internalHom) (f₁ := Arrow.mk i) (f₁' := Arrow.mk i) (f₃ := Arrow.mk p)
    sq sq₀ (Iso.refl (Arrow.mk i))

/-- The full supplied true internal-Hom pullback corner is Fib in the SAME Rezk model. -/
theorem actualRezk_suppliedPullback_fibration {A B X Y : SimplicialSpace.{u}}
    (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    cofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      fibrations SimplicialSpace.{u} sq.π := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hp
  exact ((fibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePullbackArrowIso i p sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.2.2.2 i p hi hp)

/-- A trivial original source cofibration makes the SAME supplied pullback corner TF. -/
theorem actualRezk_suppliedPullback_trivialLeft {A B X Y : SimplicialSpace.{u}}
    (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    trivialCofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hp
  exact ((trivialFibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePullbackArrowIso i p sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.2.2.1 i p hi hp)

/-- A trivial original target fibration makes the SAME supplied pullback corner TF. -/
theorem actualRezk_suppliedPullback_trivialRight {A B X Y : SimplicialSpace.{u}}
    (i : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj i p) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    cofibrations SimplicialSpace.{u} i → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  intro hi hp
  exact ((trivialFibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (samePullbackArrowIso i p sq)).mpr
      (actualRezkPushoutProduct_and_pullbackHom.2.1 i p hi hp)

end TrueSpacePowerPreparation
