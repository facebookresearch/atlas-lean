/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkScalarSM7
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkVerticalFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer
import MathlibExt.AlgebraicTopology.SimplicialSpace.JoyalTierneyQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.TotalComparisonQuillenEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalIntrinsicDKRecognition
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSDerivedMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSmithDerivedMappingComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalQuasicategoryCoreComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorCategory
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidStandardLoopWeak
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceTotalDerived
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.Category.ULift

/-!
# Complete Segal models and comparison adjunctions

External clients retain the constructed models, original supplied corners,
completion units and adjuncts. Both Joyal–Tierney criteria allow arbitrary
cofibrant sources. Their canonical derived adjunctions are checked on arbitrary
localization objects. Complete-target, Segal-groupoid and independent universe
hypotheses remain explicit where the corresponding results require them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open Cardinal CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty MonoidalCategory MonoidalClosed
open SimplicialSpace
open scoped Simplicial MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace MathlibExtTest.RezkComparisonAPI

-- The generating families, both WFS and one common cardinal are outputs.
example :
    let C := SimplicialSpace.{u}
    let I := ReedyGeneratingFamilies.I.{u}
    let W := rezkWeakEquivalences.{u}
    let Monos := monomorphisms C
    let T := Monos ⊓ W
    let F := T.rlp
    ∃ (M : ModelCategory C) (G : MorphismProperty C) (ν : Cardinal.{u})
      (regular : Fact ν.IsRegular) (bottom : OrderBot ν.ord.ToType),
      letI : ModelCategory C := M
      letI : Fact ν.IsRegular := regular
      letI : OrderBot ν.ord.ToType := bottom
      ∃ cg : CofibrantGenerationData C ν,
        M.categoryWithCofibrations.cofibrations = Monos ∧
        M.categoryWithWeakEquivalences.weakEquivalences = W ∧
        M.categoryWithFibrations.fibrations = F ∧
        trivialCofibrations C = T ∧ trivialFibrations C = I.rlp ∧
        I.rlp = Monos.rlp ∧ F ⊓ W = I.rlp ∧
        IsWeakFactorizationSystem Monos I.rlp ∧
        IsWeakFactorizationSystem T F ∧
        G.rlp = F ∧ G.rlp.llp = T ∧ G ≤ T ∧
        I.IsSmall.{u} ∧ G.IsSmall.{u} ∧
        I.HasSmallObjectArgument.{u} ∧ G.HasSmallObjectArgument.{u} ∧
        IsCardinalLocallyPresentable C ν ∧
        I.IsCardinalForSmallObjectArgument ν ∧
        G.IsCardinalForSmallObjectArgument ν ∧
        cg.I = I ∧ cg.J = G ∧
        IsCombinatorialModelCategory.{u} C ∧
        (∀ X : C, IsFibrant X ↔ completeSegalSpaces X) := by
  obtain ⟨s, M, h⟩ := RezkModel.exists_modelCategory.{u}
  obtain ⟨ν, regular, h⟩ := h
  obtain ⟨bottom, h⟩ := h
  obtain ⟨cg, hCof, hW, hFib, hTC, hTF, hIRight, hFW, hFirst, hSecond,
    hGRight, hGLeft, hGMem, hISmall, hGSmall, hISOA, hGSOA, hLP,
    hIν, hGν, hcgI, hcgG, hComb, hFibrant⟩ := h
  exact ⟨M, s.J, ν, regular, bottom, cg, hCof, hW, hFib, hTC, hTF,
    hIRight, hFW, hFirst, hSecond, hGRight, hGLeft, hGMem, hISmall,
    hGSmall, hISOA, hGSOA, hLP, hIν, hGν, hcgI, hcgG, hComb, hFibrant⟩

private local instance selectedRezk : ModelCategory SimplicialSpace.{u} :=
  RezkModel.modelCategory

private local instance selectedJoyal : ModelCategory JoyalSSet.{u} :=
  JoyalSSet.modelCategory

private local instance selectedKan : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

private local instance firstComparisonIsQuillenEquivalence :
    comparisonAdjunction.{u}.IsQuillenEquivalence :=
  comparisonAdjunction_isQuillenEquivalence

private local instance totalComparisonIsQuillenEquivalence :
    TotalSpace.adjunction.{u}.IsQuillenEquivalence :=
  TotalSpace.adjunction_isQuillenEquivalence

private local instance sourceLocallySmall :
    LocallySmall.{u} (CategoryTheory.FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) : Cofibration f ↔ Mono f := by
  rw [cofibration_iff]
  change RezkModel.modelCategory.categoryWithCofibrations.cofibrations f ↔ _
  rw [RezkModel.modelCategory_cofibrations]

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ rezkWeakEquivalences f := by
  rw [weakEquivalence_iff]
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔ _
  rw [RezkModel.modelCategory_weakEquivalences]

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    Fibration f ↔ (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences).rlp f := by
  rw [fibration_iff]
  change RezkModel.modelCategory.categoryWithFibrations.fibrations f ↔ _
  rw [RezkModel.modelCategory_fibrations]

example (X : SimplicialSpace.{u}) : IsFibrant X ↔ completeSegalSpaces X :=
  RezkModel.isFibrant_iff_completeSegalSpaces X

example : IsCombinatorialModelCategory.{u} SimplicialSpace.{u} :=
  RezkModel.modelCategory_isCombinatorial

example (X : SimplicialSpace.{u}) : IsCofibrant X := RezkModel.isCofibrant X

example : trivialFibrations SimplicialSpace.{u} = ReedyGeneratingFamilies.I.{u}.rlp :=
  RezkModel.modelCategory_trivialFibrations

example {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) (hf : Fibration f) :
    ReedyModel.modelCategory.categoryWithFibrations.fibrations f :=
  RezkModel.reedyFibration_of_fibration f ((fibration_iff f).mp hf)

-- Arbitrary supplied scalar pushout and pullback corners retain all six laws.
example {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) (pp : innerTensorBifunctor.PushoutObjObj i j) :
    (cofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      cofibrations SimplicialSpace.{u} pp.ι) ∧
    (trivialCofibrations SimplicialSpace.{u} i → cofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} pp.ι) ∧
    (cofibrations SimplicialSpace.{u} i → trivialCofibrations SSet.{u} j →
      trivialCofibrations SimplicialSpace.{u} pp.ι) :=
  ⟨RezkModel.inner_pushoutObjObj_cofibration i j pp,
    RezkModel.inner_pushoutObjObj_trivialCofibration_of_left i j pp,
    RezkModel.inner_pushoutObjObj_trivialCofibration_of_right i j pp⟩

example {A B U V : SimplicialSpace.{u}}
    (i : A ⟶ B) (p : U ⟶ V) (sq : innerHomFunctor.PullbackObjObj i p) :
    (cofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      fibrations SSet.{u} sq.π) ∧
    (trivialCofibrations SimplicialSpace.{u} i → fibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π) ∧
    (cofibrations SimplicialSpace.{u} i → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SSet.{u} sq.π) :=
  ⟨RezkModel.inner_pullbackHom_fibration i p sq,
    RezkModel.inner_pullbackHom_trivialFibration_of_left i p sq,
    RezkModel.inner_pullbackHom_trivialFibration_of_right i p sq⟩

-- The filler is constructed from model classes, rather than supplied as an outcome.
example {A B U V : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : A ⟶ B) (p : U ⟶ V) (sq : innerHomFunctor.PullbackObjObj i p)
    (j : K ⟶ L)
    (top : K ⟶ (innerHomFunctor.obj (op B)).obj U) (bottom : L ⟶ sq.pt)
    (problem : CommSq top j sq.π bottom)
    (hi : cofibrations SimplicialSpace.{u} i) (hp : fibrations SimplicialSpace.{u} p)
    (hj : trivialCofibrations SSet.{u} j) :
    ∃ lift : L ⟶ (innerHomFunctor.obj (op B)).obj U,
      j ≫ lift = top ∧ lift ≫ sq.π = bottom ∧
      lift ≫ (innerHomFunctor.map i.op).app U = bottom ≫ sq.fst ∧
      lift ≫ (innerHomFunctor.obj (op B)).map p = bottom ≫ sq.snd := by
  let _ : Fibration sq.π := (fibration_iff _).mpr
    (RezkModel.inner_pullbackHom_fibration i p sq hi hp)
  let _ : Cofibration j := (cofibration_iff _).mpr hj.1
  let _ : WeakEquivalence j := (weakEquivalence_iff _).mpr hj.2
  let _ : HasLiftingProperty j sq.π := ModelCategory.cm4a j sq.π
  let _ : problem.HasLift := inferInstance
  refine ⟨problem.lift, problem.fac_left, problem.fac_right, ?_, ?_⟩
  · rw [← sq.π_fst, ← Category.assoc, problem.fac_right]
  · rw [← sq.π_snd, ← Category.assoc, problem.fac_right]

example : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
  TrueSpacePowerPreparation.actualRezk_closedSymmetricMonoidalModel

example {A B K L : SimplicialSpace.{u}} (f : A ⟶ B) (g : K ⟶ L)
    (sq : (curriedTensor SimplicialSpace.{u}).PushoutObjObj f g) :
    (trivialCofibrations SimplicialSpace.{u} f → cofibrations SimplicialSpace.{u} g →
      trivialCofibrations SimplicialSpace.{u} sq.ι) ∧
    (cofibrations SimplicialSpace.{u} f → trivialCofibrations SimplicialSpace.{u} g →
      trivialCofibrations SimplicialSpace.{u} sq.ι) :=
  ⟨TrueSpacePowerPreparation.actualRezk_suppliedPushout_trivialLeft f g sq,
    TrueSpacePowerPreparation.actualRezk_suppliedPushout_trivialRight f g sq⟩

example {A B X Y : SimplicialSpace.{u}} (f : A ⟶ B) (p : X ⟶ Y)
    (sq : (internalHom : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤
      SimplicialSpace.{u}).PullbackObjObj f p) :
    (trivialCofibrations SimplicialSpace.{u} f → fibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π) ∧
    (cofibrations SimplicialSpace.{u} f → trivialFibrations SimplicialSpace.{u} p →
      trivialFibrations SimplicialSpace.{u} sq.π) :=
  ⟨TrueSpacePowerPreparation.actualRezk_suppliedPullback_trivialLeft f p sq,
    TrueSpacePowerPreparation.actualRezk_suppliedPullback_trivialRight f p sq⟩

example (A W : SimplicialSpace.{u + 1}) (hW : segalSpaces W) :
    segalSpaces ((ihom A).obj W) ∧
      (completeSegalSpaces W → completeSegalSpaces ((ihom A).obj W)) :=
  ⟨TrueSpacePowerPreparation.arbitrarySpacePower_segal A W hW,
    TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal A W⟩

-- The first criterion has no source-fibrancy assumption.
example {Q : JoyalSSet.{u}} {X : SimplicialSpace.{u}}
    (f : comparisonLeft.obj Q ⟶ X) (hX : completeSegalSpaces X) :
    rezkWeakEquivalences f ↔
      SSet.categoricalEquivalences
        (JoyalSSet.forget.map (comparisonAdjunction.homEquiv Q X f)) := by
  let _ : IsCofibrant Q := JoyalSSet.isCofibrant Q
  let _ : IsFibrant X := (RezkModel.isFibrant_iff_completeSegalSpaces X).mpr hX
  have h := Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
    (adj := comparisonAdjunction) f
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔
    JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (comparisonAdjunction.homEquiv Q X f) at h
  rw [RezkModel.modelCategory_weakEquivalences, JoyalSSet.modelCategory_weakEquivalences] at h
  exact h

example {Q : JoyalSSet.{u}} {X : SimplicialSpace.{u}}
    (g : Q ⟶ comparisonRight.obj X) [IsFibrant X] :
    WeakEquivalence ((comparisonAdjunction.homEquiv Q X).symm g) ↔ WeakEquivalence g := by
  let _ : IsCofibrant Q := JoyalSSet.isCofibrant Q
  simpa only [Equiv.apply_symm_apply] using
    (Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
      (adj := comparisonAdjunction) ((comparisonAdjunction.homEquiv Q X).symm g))

-- The second criterion also applies to every original space source.
example (X : SimplicialSpace.{u}) (Q : JoyalSSet.{u})
    (hQ : SSet.Quasicategory Q.toSSet) (f : TotalSpace.left.obj X ⟶ Q) :
    SSet.categoricalEquivalences (JoyalSSet.forget.map f) ↔
      rezkWeakEquivalences (TotalSpace.adjunction.homEquiv X Q f) := by
  have h := TotalSpace.adjunction_homEquiv_weakEquivalence_iff X Q
    (RezkModel.isCofibrant X) ((JoyalSSet.isFibrant_iff_quasicategory Q).mpr hQ) f
  simp only [weakEquivalence_iff] at h
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔
    RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (TotalSpace.adjunction.homEquiv X Q f) at h
  rw [JoyalSSet.modelCategory_weakEquivalences, RezkModel.modelCategory_weakEquivalences] at h
  exact h

example (X : SimplicialSpace.{u}) (Q : JoyalSSet.{u}) [IsFibrant Q]
    (g : X ⟶ TotalSpace.right.obj Q) :
    WeakEquivalence ((TotalSpace.adjunction.homEquiv X Q).symm g) ↔ WeakEquivalence g := by
  simpa only [Equiv.apply_symm_apply] using
    (TotalSpace.adjunction_homEquiv_weakEquivalence_iff X Q
      (RezkModel.isCofibrant X) inferInstance ((TotalSpace.adjunction.homEquiv X Q).symm g))

example {Q : JoyalSSet.{u}} {X : SimplicialSpace.{u}}
    (f : comparisonLeft.obj Q ⟶ X) :
    comparisonLeft.map (comparisonAdjunction.homEquiv Q X f) ≫
      comparisonAdjunction.counit.app X = f := by
  have h := comparisonAdjunction.homEquiv_counit
    (g := comparisonAdjunction.homEquiv Q X f)
  exact h.symm.trans (Equiv.symm_apply_apply _ _)

example (Q : JoyalSSet.{u}) (m : SimplexCategoryᵒᵖ) :
    (JoyalSSet.forget.map (comparisonAdjunction.unit.app Q)).app m =
      𝟙 (Q.toSSet.obj m) := comparisonAdjunction_unit_app Q m

example (X : SimplicialSpace.{u}) (hX : completeSegalSpaces X)
    {Q : JoyalSSet.{u}} (q : Q ⟶ comparisonRight.obj X)
    (hq : JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences q) :
    rezkWeakEquivalences (comparisonLeft.map q ≫ comparisonAdjunction.counit.app X) :=
  comparisonAdjunction_derivedCounit_rezkWeak X hX q hq

example (Q : JoyalSSet.{u}) [IsFibrant Q] :
    WeakEquivalence (TotalSpace.adjunction.counit.app Q) := by
  let _ : IsCofibrant (TotalSpace.right.obj Q) := RezkModel.isCofibrant _
  exact Adjunction.IsQuillenEquivalence.weakEquivalence_counit
    (adj := TotalSpace.adjunction) Q

example (X : SimplicialSpace.{u}) :
    TotalSpace.left.map (TotalSpace.adjunction.unit.app X) ≫
      TotalSpace.adjunction.counit.app (TotalSpace.left.obj X) = 𝟙 _ :=
  TotalSpace.adjunction_left_triangle X

example (Q : JoyalSSet.{u}) :
    TotalSpace.adjunction.unit.app (TotalSpace.right.obj Q) ≫
      TotalSpace.right.map (TotalSpace.adjunction.counit.app Q) = 𝟙 _ :=
  TotalSpace.adjunction_right_triangle Q

-- Neither comparison's canonical localization equivalence is an input.
example : (weakEquivalences JoyalSSet.{u}).Localization ≌
    (weakEquivalences SimplicialSpace.{u}).Localization :=
  quillenEquivalenceDerivedEquivalence comparisonAdjunction

example (X : (weakEquivalences JoyalSSet.{u}).Localization)
    (Y : (weakEquivalences SimplicialSpace.{u}).Localization) :
    IsIso ((quillenDerivedAdjunctionData comparisonAdjunction).adjunction.unit.app X) ∧
      IsIso ((quillenDerivedAdjunctionData comparisonAdjunction).adjunction.counit.app Y) := by
  let _ : IsIso (quillenDerivedAdjunctionData comparisonAdjunction).adjunction.unit :=
    quillenEquivalenceDerived_unit_isIso comparisonAdjunction
  let _ : IsIso (quillenDerivedAdjunctionData comparisonAdjunction).adjunction.counit :=
    quillenEquivalenceDerived_counit_isIso comparisonAdjunction
  constructor <;> infer_instance

example (X : (weakEquivalences JoyalSSet.{u}).Localization)
    (Y : (weakEquivalences SimplicialSpace.{u}).Localization)
    (f : (quillenDerivedAdjunctionData comparisonAdjunction).leftDerived.obj X ⟶ Y) :
    (quillenEquivalenceDerivedEquivalence comparisonAdjunction).toAdjunction.homEquiv X Y f =
      (quillenDerivedAdjunctionData comparisonAdjunction).adjunction.homEquiv X Y f :=
  quillenEquivalenceDerivedEquivalence_homEquiv comparisonAdjunction X Y f

example :
    (quillenEquivalenceDerivedEquivalence comparisonAdjunction).unitIso.hom =
        (quillenDerivedAdjunctionData comparisonAdjunction).adjunction.unit ∧
      (quillenEquivalenceDerivedEquivalence comparisonAdjunction).counitIso.hom =
        (quillenDerivedAdjunctionData comparisonAdjunction).adjunction.counit :=
  ⟨quillenEquivalenceDerivedEquivalence_unit_hom comparisonAdjunction,
    quillenEquivalenceDerivedEquivalence_counit_hom comparisonAdjunction⟩

example : (weakEquivalences SimplicialSpace.{u}).Localization ≌
    (weakEquivalences JoyalSSet.{u}).Localization :=
  quillenEquivalenceDerivedEquivalence TotalSpace.adjunction

example (X : (weakEquivalences SimplicialSpace.{u}).Localization)
    (Q : (weakEquivalences JoyalSSet.{u}).Localization) :
    IsIso ((quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.unit.app X) ∧
      IsIso ((quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.counit.app Q) := by
  let _ : IsIso (quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.unit :=
    quillenEquivalenceDerived_unit_isIso TotalSpace.adjunction
  let _ : IsIso (quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.counit :=
    quillenEquivalenceDerived_counit_isIso TotalSpace.adjunction
  constructor <;> infer_instance

example :
    (quillenEquivalenceDerivedEquivalence TotalSpace.adjunction).unitIso.hom =
        (quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.unit ∧
      (quillenEquivalenceDerivedEquivalence TotalSpace.adjunction).counitIso.hom =
        (quillenDerivedAdjunctionData TotalSpace.adjunction).adjunction.counit :=
  ⟨quillenEquivalenceDerivedEquivalence_unit_hom TotalSpace.adjunction,
    quillenEquivalenceDerivedEquivalence_counit_hom TotalSpace.adjunction⟩

-- The literal completion's target and unit comparisons are constructed.
example (W : SimplicialSpace.{u + 1}) (hW : segalSpaces W) :
    completeSegalSpaces (RezkCompletionData.completion.obj W) ∧
      rezkWeakEquivalences (RezkCompletionData.unit.app W) ∧
      IntrinsicDK.isEquivalence (RezkCompletionData.unit.app W) hW
        (RezkCompletionAllVertex.sameCompletion_segal W hW) :=
  ⟨RezkCompletionCoreDiagonal.sameCompletion_completeSegal_from_derived_image_fibres W hW,
    RezkCompletionData.unit_rezkWeak W, RezkCompletionData.unit_intrinsicDK W hW⟩

example (W : SimplicialSpace.{u + 1}) :
    RezkCompletionData.unit.app W = RezkCompletionRaw.rawCompletionUnit W ≫
      RezkBaselineReplacement.unit.app (RezkCompletionRaw.rawCompletion W) :=
  RezkCompletionData.unit_app W

example (W : SimplicialSpace.{u + 1}) :
    Function.Surjective (SSet.mapπ₀
      (RezkCompletionAllVertex.sameOriginalUnitTuple W 0)) :=
  RezkCompletionAllVertex.sameOriginalUnitTuple_components_surjective W 0

example (W : SimplicialSpace.{u + 1}) (hW : segalSpaces W)
    (x : Fin 3 → (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (OriginalChosenSpineFixedTupleBaseChange.simplexAllVertexFibreMap
        (RezkCompletionData.unit.app W) 2 x) :=
  RezkCompletionAllVertex.sameOriginalUnit_simplexAllVertexFibreMap_weak W hW 2 (by decide) x

example {W V : SimplicialSpace.{u + 1}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    rezkWeakEquivalences f ↔
      (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
        SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl)) ∧
      (SegalHomotopy.map f hW hV).EssSurj :=
  segalMap_cssWeak_iff_mappingWeak_and_essSurj f hW hV

example {W V : SimplicialSpace.{u + 1}} (f : W ⟶ V) :
    rezkWeakEquivalences (RezkCompletionData.completion.map f) ↔ rezkWeakEquivalences f :=
  RezkCompletionData.completion_map_rezkWeak_iff f

-- Empty sources require no assumed completeness or mapping-space outcome.
example : completeSegalSpaces (OriginalSmithCSS.replacement.obj (⊥_ SimplicialSpace.{u})) :=
  OriginalSmithCSS.replacement_completeSegal _

example : rezkWeakEquivalences (RezkCompletionData.unit.app (⊥_ SimplicialSpace.{u})) :=
  RezkCompletionData.unit_rezkWeak _

example (A B : SimplicialSpace.{u}) :
    SSet.KanComplex ((OriginalSmithCSS.derivedEnd.obj (op A)).obj B) :=
  OriginalSmithCSS.derivedEnd_kan A B

example (A B : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences
        ((RezkCompletionSmithComparison.completionPreSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences
        ((RezkCompletionSmithComparison.completionPostSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences
        ((RezkCompletionSmithComparison.smithPreSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences
        ((RezkCompletionSmithComparison.smithPostSpan.app (op A)).app B) :=
  RezkCompletionSmithComparison.all_four_derived_span_legs_weak A B

example (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    SSet.Quasicategory (OnefoldCoreComparison.row.obj W) ∧
      SSet.KanComplex (OnefoldCoreComparison.nativeCore.obj W) ∧
      SSet.realizationWeakEquivalences (OnefoldCoreComparison.targetCoreLeg.app W) ∧
      SSet.realizationWeakEquivalences (OnefoldCoreComparison.nativeCoreLeg.app W) :=
  ⟨OnefoldCoreComparison.row_isQuasicategory W hW,
    OnefoldCoreComparison.nativeCore_isKan W hW,
    OnefoldCoreComparison.targetCoreLeg_weak W hW,
    OnefoldCoreComparison.nativeCoreLeg_weak W hW⟩

example {W V : OnefoldCoreComparison.CompleteTargets.{u}} (f : W ⟶ V) :
    OnefoldCoreComparison.targetHo.map f ≫ OnefoldCoreComparison.coreHoIso.hom.app V =
      OnefoldCoreComparison.coreHoIso.hom.app W ≫ OnefoldCoreComparison.nativeHo.map f :=
  OnefoldCoreComparison.coreHoIso_natural f

-- Only the target is assumed complete in these two fibrancy clients.
example (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    IsFibrant (FirstProjection.cssFunctorCategory W V) ∧
      IsFibrant (FirstProjection.nativeFunctorCategory W V) :=
  ⟨FirstProjection.cssFunctorCategory_isFibrant W V hV,
    FirstProjection.nativeFunctorCategory_isFibrant W V hV⟩

example (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
      (FirstProjection.functorCategoryComparison W V) :=
  FirstProjection.functorCategoryComparison_weak W V hW hV

example (W V : SimplicialSpace.{u}) :
    MonoidalClosed.uncurry
        (JoyalSSet.forget.map (FirstProjection.functorCategoryComparison W V)) =
      (FirstProjection.rightProductIso W ((ihom W).obj V)).inv ≫
        FirstProjection.right.map ((ihom.ev W).app V) :=
  FirstProjection.functorCategoryComparison_evaluation W V

example (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences.Q.obj
        (SSet.coreFunctor.obj (FirstProjection.nativeFunctorCategory W V).toSSet) ≅
      SSet.realizationWeakEquivalences.Q.obj
        (((SimplicialPresheaf.OriginalLocalDerived.localDerivedEnd
          (SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1)).obj
          (op (FirstProjection.originalImage W))).obj (FirstProjection.originalImage V)) :=
  FirstProjection.functorCategoryCoreMappingIso W V hW hV

example (K : SSet.{u}) (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences (FirstProjection.scalarCoreComparison K W V) :=
  FirstProjection.scalarCoreComparison_weak K W V hW hV

-- A directed nerve supplies a non-Kan quasicategory to the actual Gamma construction.
private abbrev Directed := AsSmall.{u} (Fin 2)
private abbrev directedNerve : SSet.{u} := nerve Directed.{u}
private abbrev directedGamma : SimplicialSpace.{u} :=
  ofSimplicialObject.obj (SSet.Rezk.gammaDiagram.obj directedNerve.{u})

private def forwardArrow :
    (AsSmall.up.obj (0 : Fin 2) : Directed.{u}) ⟶ AsSmall.up.obj (1 : Fin 2) :=
  AsSmall.up.map (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))

private theorem forwardArrowNotIso : ¬ IsIso forwardArrow.{u} := by
  intro h
  let _ : IsIso forwardArrow.{u} := h
  have impossible : (1 : Fin 2) ≤ 0 := leOfHom (AsSmall.down.map (inv forwardArrow.{u}))
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) impossible

example : ¬ SSet.KanComplex directedNerve.{u} := by
  intro h
  let _ : SSet.KanComplex directedNerve.{u} := h
  have inCore : ComposableArrows.mk₁ forwardArrow.{u} ∈
      (SSet.core directedNerve).obj (op ⦋1⦌) := by
    rw [SSet.core_eq_top_of_kanComplex]
    trivial
  exact forwardArrowNotIso ((SSet.mem_core_nerve_mk₁_iff forwardArrow).mp inCore)

private theorem directedGamma_complete : completeSegalSpaces directedGamma.{u} := by
  let _ : SSet.Quasicategory directedNerve.{u} := by
    change SSet.Quasicategory (nerve Directed.{u})
    infer_instance
  exact (SSet.Rezk.gammaDiagram_replacement directedNerve.{u}).1

example : IsFibrant directedGamma.{u} :=
  (RezkModel.isFibrant_iff_completeSegalSpaces _).mpr directedGamma_complete

example : JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (FirstProjection.functorCategoryComparison directedGamma.{u} directedGamma.{u}) :=
  FirstProjection.functorCategoryComparison_weak _ _
    directedGamma_complete directedGamma_complete

-- Completeness is unnecessary for the canonical Segal-groupoid loop comparison.
example (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, SegalHomotopy.IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (LeftDecalageObject.standardDiagonalLoopMap W x) :=
  LeftDecalageObject.standardDiagonalLoopMap_weak W hW hG x

-- The general representable criterion keeps all four independent universes.
example {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
    {I : Type i} [Small.{u} I] (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) :=
      SimplicialPresheaf.InjectiveKan.originalLocalSmithModel S
    CartesianPushoutProductAxiom (C := SimplicialPresheaf.{u} D) ↔
      ∀ a d, SimplicialPresheaf.InjectiveKan.originalLocalEquivalences S
        ((S a).hom ▷ SimplicialPresheaf.discreteYoneda.obj d) :=
  SimplicialPresheaf.InjectiveKan.originalLocalCartesianPP_iff_representableCriterion S

end MathlibExtTest.RezkComparisonAPI
