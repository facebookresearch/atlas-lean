/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceBranches
import MathlibExt.CategoryTheory.Adjunction.SourceHomColimit

/-!
# Original free operadic sources on their actual cell histories

Every occurring cell of the original enveloping filtration is classified in
the full arbitrary-coefficient cofibration-orbit class. The actual free functor
handles the caller's two coproduct cofans before forgetting the pushout.
Created ordinal colimits then retain the original outer history at every color.

Source Hom preservation is transported through the actual color insertion and
operadic free adjunctions. This produces the complete original free-I/free-J
small-object inputs at the caller's cardinal and bottom. Neither arrow-set
smallness nor a larger auxiliary rank is substituted for source Hom preservation.

The source is Pavlov--Scholbach, *Admissibility and rectification of colored
symmetric operads*, arXiv:1410.5675v4, Theorem 5.11 and Remark 5.13, and
*Symmetric operads in abstract symmetric spectra*, arXiv:1410.5699v2,
Appendix 9.3. The ordinary admissibly generated branch still needs its own
acyclic closure argument; the present file proves the actual source joins.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject Opposite
open CategoryTheory.Operad CategoryTheory.Operad.Tensor
open CategoryTheory.Operad.Tensor.Enveloping
open CategoryTheory.Operad.Tensor.Enveloping.Filtration
open CategoryTheory.Operad.Tensor.InitialAttachment
open CategoryTheory.Operad.Tensor.InitialAttachment.ProfileCells
open CategoryTheory.OperadicOrbitCells
open CategoryTheory.OperadicOrbitCells.ProfileGeometry
open CategoryTheory.OperadicOrbitCells.A5Comparison.CanonicalSupported

namespace HomotopicalAlgebra.OperadicTransfer.SourceProducers

variable (S : SourceContext.{uW, v, u, us})

/-- The original finite source tensor used by the full free-cell histories. -/
local instance sourceFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance sourceTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance sourceProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

local instance sourceCellsCobase :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderCobaseChange :=
  OperadicAcyclicCells.cofibrationCells_stable.1

local instance sourceCellsCoproducts :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderCoproducts.{us} :=
  OperadicAcyclicCells.cofibrationCells_stable.2.1

local instance sourceCellsTransfinite :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderTransfiniteComposition.{us} :=
  OperadicAcyclicCells.cofibrationCells_stable.2.2

local instance sourceCellsCountable :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderTransfiniteComposition.{0} :=
  IsStableUnderTransfiniteComposition.shrink₀ _

/-- Every actual positive Env layer is in the original cofibration-orbit class.
At another color the original map is an isomorphism. -/
theorem occurringOriginalCofibrationCell_mem
    (O : ColoredOperadObj S.W S.C) (A : Algebra O)
    {X Y : S.W → S.C} (x : X ⟶ Y) (hx : ∀ d, cofibrations S.C (x d))
    (d : S.W) (N : ℕ) (p : RawCellIndex S.W N) :
    OperadicAcyclicCells.cofibrationCells.{us, us} S.C (profileCellMap O A x N p d) := by
  let Q := OperadicAcyclicCells.cofibrationCells.{us, us} S.C
  by_cases hd : d = p.1
  · subst d
    have hP : 0 < inputCount (representativeProfile p.1 p.2) := by
      rw [representativeProfile_degree]
      exact Nat.zero_lt_succ N
    have hm := operadProfileArrow_mem_isoClosure (cofibrations S.C)
      (envelopingOperad O A) x (representativeProfile p.1 p.2) hP (fun i => hx _)
    have hOrbit : orbitGenerators (cofibrations S.C) ≤ Q :=
      (le_coproducts _).trans ((le_pushouts _).trans (le_transfiniteCompositions _))
    exact (Q.arrow_iso_iff (profileCellColorIso O A x N p)).2
      (((isoClosure_le_iff _ _).2 hOrbit) _ hm)
  · have hi : IsIso (profileCellMap O A x N p d) := by
      change IsIso (colorMap p.1
        (balancedProfileArrow (envelopingOperad O A) x (representativeProfile p.1 p.2)).hom d)
      dsimp only [colorMap]
      rw [dite_eq_right hd]
      infer_instance
    let := hi
    exact Q.of_isIso _

/-- Classify the entire original A5 history, including its zero-stage isomorphism,
actual endpoint cocone, and actual positive profile occurrences. -/
def originalCofibrationAttachmentHistory
    (O : ColoredOperadObj S.W S.C) (A : Algebra O)
    {X Y : S.W → S.C} (x : X ⟶ Y) (a : freeAlgebra O X ⟶ A)
    (hx : ∀ d, cofibrations S.C (x d)) (d : S.W) :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).TransfiniteCompositionOfShape ℕ
      ((OriginalAttachment.oldMap O A x a).hom d) := by
  let c := OperadicAcyclicCells.Attachments.evaluatedOriginalRelativeCellComplex O A x a d
  let Q := OperadicAcyclicCells.cofibrationCells.{us, us} S.C
  have hPush : Q.coproducts.{us}.pushouts ≤ Q :=
    (pushouts_le_iff (P := Q.coproducts.{us}) (Q := Q)).2 (coproducts_le Q)
  exact (c.transfiniteCompositionOfShape' (fun s =>
    occurringOriginalCofibrationCell_mem S O A x hx d s.j s.i)).ofLE hPush

/-- The old leg of the same actual free-algebra pushout has the derived source-cell property. -/
theorem originalCofibrationAttachment_mem
    (O : ColoredOperadObj S.W S.C) (A : Algebra O)
    {X Y : S.W → S.C} (x : X ⟶ Y) (a : freeAlgebra O X ⟶ A)
    (hx : ∀ d, cofibrations S.C (x d)) (d : S.W) :
    OperadicAcyclicCells.cofibrationCells.{us, us} S.C
      ((OriginalAttachment.oldMap O A x a).hom d) :=
  (OperadicAcyclicCells.cofibrationCells S.C).transfiniteCompositionsOfShape_le ℕ _
    (originalCofibrationAttachmentHistory S O A x a hx d).mem

/-- Preserve the caller's actual square when comparing it with the constructed A5 square. -/
theorem freeCofibrationPushout_mem
    (O : ColoredOperadObj S.W S.C) {X Y : S.W → S.C} (x : X ⟶ Y)
    (hx : ∀ d, cofibrations S.C (x d)) {A B : Algebra O}
    (a : freeAlgebra O X ⟶ A) (b : freeAlgebra O Y ⟶ B) (g : A ⟶ B)
    (sq : IsPushout a ((freeAlgebraFunctor O).map x) g b) (d : S.W) :
    OperadicAcyclicCells.cofibrationCells.{us, us} S.C ((carrierAt S O d).map g) := by
  let s := OriginalAttachment.isPushout O A x a
  let e := s.isColimit.coconePointUniqueUpToIso sq.isColimit
  have he : OriginalAttachment.oldMap O A x a ≫ e.hom = g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom s.isColimit sq.isColimit WalkingSpan.left
  let q : Arrow.mk (OriginalAttachment.oldMap O A x a) ≅ Arrow.mk g :=
    Arrow.isoMk (Iso.refl A) e (by
      change 𝟙 A ≫ g = OriginalAttachment.oldMap O A x a ≫ e.hom
      exact (Category.id_comp g).trans he.symm)
  exact ((OperadicAcyclicCells.cofibrationCells S.C).arrow_iso_iff
    ((carrierAt S O d).mapArrow.mapIso q)).mp
      (originalCofibrationAttachment_mem S O A x a hx d)

/-- The actual free cofans are compared before applying the forgetful functor;
no preservation of arbitrary algebra coproducts by that functor is used. -/
theorem freeCofibrationCoproductPushouts_mem
    (O : ColoredOperadObj S.W S.C) (d : S.W) :
    ((SemiModel.ColorSource.pointwiseProperty S.C S.W (cofibrations S.C)).strictMap
      (freeAlgebraFunctor O)).coproducts.{us}.pushouts ≤
        (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).inverseImage (carrierAt S O d) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  let : (SemiModel.ColorSource.pointwiseProperty S.C S.W (cofibrations S.C)).IsStableUnderCoproducts.{us} := by
    rw [← SemiModel.ColorSource.cofibrations_eq S.C S.W, ← trivialFibrations_llp]
    infer_instance
  let : (freeAlgebraFunctor O).IsLeftAdjoint := ⟨Algebra.forget O, ⟨S.operadicAdjunction O⟩⟩
  intro A B g hg
  obtain ⟨X, Y, m, a, b, hm, sq⟩ := hg
  have hFree := MorphismProperty.coproducts_strictMap_le_map
    (SemiModel.ColorSource.pointwiseProperty S.C S.W (cofibrations S.C))
    (freeAlgebraFunctor O) m hm
  obtain ⟨K, L, x, hx, ⟨q⟩⟩ := hFree
  let s := Arrow.leftFunc.mapIso q
  let t := Arrow.rightFunc.mapIso q
  have hq : s.hom ≫ m = (freeAlgebraFunctor O).map x ≫ t.hom := q.hom.w
  have sq' : IsPushout (s.hom ≫ a) ((freeAlgebraFunctor O).map x) g (t.hom ≫ b) :=
    sq.of_iso' s (Iso.refl A) t (Iso.refl B)
      (by simp) hq (by simp) (by simp)
  exact freeCofibrationPushout_mem S O x hx (s.hom ≫ a) (t.hom ≫ b) g sq' d

/-- A literal supported generator retains the original cofibration at its original color. -/
theorem colorGenerators_le_pointwiseCofibrations
    (P : MorphismProperty S.C) (hP : P ≤ cofibrations S.C) :
    SemiModel.ColorSource.colorGenerators S.C S.W P ≤
      SemiModel.ColorSource.pointwiseProperty S.C S.W (cofibrations S.C) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  rw [← SemiModel.ColorSource.cofibrations_eq S.C S.W,
    SemiModel.ColorSource.colorGenerators, adjointFamilyGenerators_eq_iSup_strictMap]
  refine iSup_le fun d => ?_
  intro X Y f hf
  cases hf with
  | map hi => exact SemiModel.ColorSource.colorFreeMap_cofibration S.C S.W d _ (hP _ hi)

/-- The entire original coproduct of the original supported free generators
has the earned source-cell class on its actual pushout old leg. -/
theorem freeGeneratorCoproductPushouts_mem
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C) (d : S.W) :
    (freeGenerators S O P).coproducts.{us}.pushouts ≤
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).inverseImage (carrierAt S O d) :=
  (pushouts_monotone (coproducts_monotone (monotone_strictMap (freeAlgebraFunctor O)
    (colorGenerators_le_pointwiseCofibrations S P hP)))).trans
      (freeCofibrationCoproductPushouts_mem S O d)

/-- Map the caller's entire original history, with its original bottom,
endpoint, and inclusion legs, into the derived structural source class. -/
def freeGeneratorMappedCellHistory
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : RelativeCellComplex.{us} (fun _ : T => (freeGenerators S O P).homFamily) f)
    (d : S.W) :
    (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).TransfiniteCompositionOfShape T
      ((carrierAt S O d).map f) := by
  letI : PreservesColimitsOfShape T (carrierAt S O d) :=
    carrierAt_preservesFilteredColimits S O d T
  letI : PreservesWellOrderContinuousOfShape T (carrierAt S O d) :=
    carrierAt_preservesWellOrderContinuous S O d T
  exact ((c.transfiniteCompositionOfShape' (fun s => s.i.2)).ofLE
    (freeGeneratorCoproductPushouts_mem S O P hP d)).map

/-- Every original outer transition is tested at the original output color. -/
theorem freeGeneratorRelativeTransitions_mem
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : RelativeCellComplex.{us} (fun _ : T => (freeGenerators S O P).homFamily) f)
    (d : S.W) : ∀ (i j : T) (φ : i ⟶ j),
    OperadicAcyclicCells.cofibrationCells.{us, us} S.C ((carrierAt S O d).map (c.F.map φ)) := by
  intro i j φ
  let Q := OperadicAcyclicCells.cofibrationCells.{us, us} S.C
  let : Q.IsStableUnderTransfiniteComposition.{us} := sourceCellsTransfinite S
  exact (freeGeneratorMappedCellHistory S O P hP c d).map_mem_of_stable φ

private def endpointProperty {C : Type u} [Category.{v} C] (H : C → Prop) :
    MorphismProperty C := fun A B _ => H A ∧ H B

/-- Both endpoints of each literal original supported free arrow preserve
the same given ordinal colimit through the two actual adjunctions. -/
theorem freeGeneratorEndpoints_preserveOrdinalColimit
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hSources : SourceHomPreservation.{u, v, us} P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    {T : Type us} [LinearOrder T] [OrderBot T] [WellFoundedLT T]
    (D : T ⥤ Algebra O)
    (hD : ∀ (i j : T) (φ : i ⟶ j) (d : S.W),
      OperadicAcyclicCells.cofibrationCells.{us, us} S.C ((carrierAt S O d).map (D.map φ)))
    {A B : Algebra O} (i : A ⟶ B) (hi : freeGenerators S O P i) :
    PreservesColimit D (coyoneda.obj (op A)) ∧
      PreservesColimit D (coyoneda.obj (op B)) := by
  let H : Algebra O → Prop := fun A => PreservesColimit D (coyoneda.obj (op A))
  have h : freeGenerators S O P ≤ endpointProperty H := by
    rw [freeGenerators, strictMap_le_iff_le_inverseImage,
      SemiModel.ColorSource.colorGenerators, adjointFamilyGenerators_eq_iSup_strictMap]
    refine iSup_le fun d => ?_
    rw [strictMap_le_iff_le_inverseImage]
    intro X Y f hf
    let adj := (SemiModel.ColorSource.colorFreeEvaluationAdjunction S.C S.W d).comp
      (S.operadicAdjunction O)
    let : PreservesColimitsOfShape T
        (Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d) :=
      carrierAt_preservesFilteredColimits S O d T
    let : PreservesColimit
        (D ⋙ Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d)
        (coyoneda.obj (op X)) :=
      hSources.domains ⟨Arrow.mk f, hf⟩ T
        (D ⋙ Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d)
        (fun a b φ => hD a b φ d)
    let : PreservesColimit
        (D ⋙ Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d)
        (coyoneda.obj (op Y)) :=
      hSources.codomains ⟨Arrow.mk f, hf⟩ T
        (D ⋙ Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d)
        (fun a b φ => hD a b φ d)
    exact ⟨adj.preservesColimit_leftAdjointSource X D,
      adj.preservesColimit_leftAdjointSource Y D⟩
  exact h i hi

/-- The actual original free-cell source smallness is produced on the
original cardinal diagram, using its derived original transition class. -/
theorem actualFreeCellSourceSmallness
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (κ : Cardinal.{us}) [OrderBot κ.ord.ToType] :
    ActualFreeCellSourceSmallness S O P κ := by
  intro A B X Y i hi f c
  exact (freeGeneratorEndpoints_preserveOrdinalColimit S O P hSources c.F
    (fun a b φ d => freeGeneratorRelativeTransitions_mem S O P hP c d a b φ) i hi).1

/-- Preserve the actual original endpoint cocone, rather than a new chosen colimit. -/
def mappedActualFreeCellCocone
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (κ : Cardinal.{us}) [OrderBot κ.ord.ToType]
    {A B X Y : Algebra O} (i : A ⟶ B) (hi : freeGenerators S O P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{us}
      (fun _ : κ.ord.ToType => (freeGenerators S O P).homFamily) f) :
    IsColimit ((coyoneda.obj (op A)).mapCocone (Cocone.mk Y c.incl)) := by
  let : PreservesColimit c.F (coyoneda.obj (op A)) :=
    actualFreeCellSourceSmallness S O P hP hSources κ i hi f c
  exact isColimitOfPreserves _ c.isColimit

/-- All six original free-source small-object fields are earned at the caller's
cardinal and bottom, from source Hom and the actual created colimits. -/
theorem freeGenerators_smallObject
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    [P.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hP : P ≤ cofibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] :
    (freeGenerators S O P).IsCardinalForSmallObjectArgument κ := by
  let : HasLimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasLimits S O
  let : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  let : HasColimitsOfSize.{0, 0} (Algebra O) := hasColimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  let : LocallySmall.{us} (S.W → S.C) :=
    { hom_small X Y := by
        change Small.{us} (∀ d, X d ⟶ Y d)
        infer_instance }
  let : LocallySmall.{us} (Algebra O) := locallySmall_of_faithful (Algebra.forget O)
  let : (freeGenerators S O P).IsSmall.{us} := freeGenerators_isSmall S O P
  exact
    { preservesColimit := fun i hi f c => actualFreeCellSourceSmallness S O P hP hSources κ i hi f c }


end HomotopicalAlgebra.OperadicTransfer.SourceProducers
