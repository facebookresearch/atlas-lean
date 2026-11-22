/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.OrdinalModel

/-!
# Original-cardinal continuous free sources

The native stable J bank includes the actual mapping-cylinder/scalar boundary
generators. Their bounded source theorem concerns the original continuous
realized-cardinal history. It need not preserve every ordinal diagram at every
rank. This file transports that precise source theorem through the original
color and free-algebra adjunctions.

The stronger original I endpoint comparisons are used only where ordinal
acyclic closure requires them. The complete free-I/free-J small-object arguments
retain the caller's original cardinal and bottom, and the algebra forgetful
functor creates the very same continuous colimits used by the source theorem.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject Opposite
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer.SourceProducers

variable (S : SourceContext.{uW, v, u, us})

/-- The original finite tensor used for continuous source diagrams. -/
local instance continuousFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance continuousTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance continuousProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

/-- The precise source-domain Hom condition on continuous original-cardinal
diagrams with the supplied actual structural transitions. -/
def SourcesPreserveContinuousColimits (P Q : MorphismProperty S.C)
    (κ : Cardinal.{us}) : Prop :=
  ∀ {X Y : S.C} (i : X ⟶ Y), P i →
    ∀ (D : κ.ord.ToType ⥤ S.C) [D.IsWellOrderContinuous],
      (∀ (a b : κ.ord.ToType) (f : a ⟶ b), Q (D.map f)) →
        PreservesColimit D (coyoneda.obj (op X))

/-- Original ordinal endpoint Hom supplies the needed continuous source condition
at the caller's cardinal, without constructing or changing a cardinal. -/
theorem sourcesPreserveContinuousOfOrdinal
    (P Q : MorphismProperty S.C) (hSources : SourceHomPreservation.{u, v, us} P Q)
    (κ : Cardinal.{us}) [OrderBot κ.ord.ToType] :
    SourcesPreserveContinuousColimits S P Q κ := by
  intro X Y i hi D _ hD
  exact hSources.domains ⟨Arrow.mk i, hi⟩ κ.ord.ToType D hD

private def sourceProperty (O : ColoredOperadObj S.W S.C) (H : Algebra O → Prop) :
    MorphismProperty (Algebra O) := fun A _ _ => H A

/-- The actual free endpoint Hom comparison uses the same original continuous
algebra diagram and the actual created colimit of its original color evaluation. -/
theorem freeGeneratorSource_preservesContinuousColimit
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (κ : Cardinal.{us}) [OrderBot κ.ord.ToType]
    (hSources : SourcesPreserveContinuousColimits S P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C) κ)
    (D : κ.ord.ToType ⥤ Algebra O) [D.IsWellOrderContinuous]
    (hD : ∀ (a b : κ.ord.ToType) (f : a ⟶ b) (d : S.W),
      OperadicAcyclicCells.cofibrationCells.{us, us} S.C ((carrierAt S O d).map (D.map f)))
    {A B : Algebra O} (i : A ⟶ B) (hi : freeGenerators S O P i) :
    PreservesColimit D (coyoneda.obj (op A)) := by
  let H : Algebra O → Prop := fun A => PreservesColimit D (coyoneda.obj (op A))
  have h : freeGenerators S O P ≤ sourceProperty S O H := by
    rw [freeGenerators, strictMap_le_iff_le_inverseImage,
      SemiModel.ColorSource.colorGenerators, adjointFamilyGenerators_eq_iSup_strictMap]
    refine iSup_le fun d => ?_
    rw [strictMap_le_iff_le_inverseImage]
    intro X Y f hf
    let ev := Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d
    let adj := (SemiModel.ColorSource.colorFreeEvaluationAdjunction S.C S.W d).comp
      (S.operadicAdjunction O)
    let : PreservesColimitsOfShape κ.ord.ToType ev :=
      carrierAt_preservesFilteredColimits S O d κ.ord.ToType
    let : PreservesWellOrderContinuousOfShape κ.ord.ToType ev :=
      carrierAt_preservesWellOrderContinuous S O d κ.ord.ToType
    let : (D ⋙ ev).IsWellOrderContinuous := inferInstance
    let : PreservesColimit (D ⋙ Algebra.forget O ⋙ SemiModel.ColorSource.colorEvaluation S.C S.W d)
        (coyoneda.obj (op X)) := hSources f hf (D ⋙ ev) (fun a b φ => hD a b φ d)
    exact adj.preservesColimit_leftAdjointSource X D
  exact h i hi

/-- The actual original free-cell source smallness follows from the precise
continuous source theorem and the derived complete original free-cell history. -/
theorem actualFreeCellSourceSmallnessOfContinuousSources
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C) (κ : Cardinal.{us}) [OrderBot κ.ord.ToType]
    (hSources : SourcesPreserveContinuousColimits S P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C) κ) :
    ActualFreeCellSourceSmallness S O P κ := by
  intro A B X Y i hi f c
  let : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact freeGeneratorSource_preservesContinuousColimit S O P κ hSources c.F
    (fun a b φ d => freeGeneratorRelativeTransitions_mem S O P hP c d a b φ) i hi

/-- The original endpoint and all the caller's original inclusion legs remain
colimiting after Hom from the same actual continuous free source. -/
def mappedContinuousFreeCellCocone
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    (hP : P ≤ cofibrations S.C) (κ : Cardinal.{us}) [OrderBot κ.ord.ToType]
    (hSources : SourcesPreserveContinuousColimits S P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C) κ)
    {A B X Y : Algebra O} (i : A ⟶ B) (hi : freeGenerators S O P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{us}
      (fun _ : κ.ord.ToType => (freeGenerators S O P).homFamily) f) :
    IsColimit ((coyoneda.obj (op A)).mapCocone (Cocone.mk Y c.incl)) := by
  letI : PreservesColimit c.F (coyoneda.obj (op A)) :=
    actualFreeCellSourceSmallnessOfContinuousSources S O P hP κ hSources i hi f c
  exact isColimitOfPreserves _ c.isColimit

/-- The continuous source theorem earns all six original small-object fields,
using created algebra colimits and the original free family. -/
theorem freeGeneratorsSmallObjectOfContinuousSources
    (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C)
    [P.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hP : P ≤ cofibrations S.C) (κ : Cardinal.{us})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hSources : SourcesPreserveContinuousColimits S P
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C) κ) :
    (freeGenerators S O P).IsCardinalForSmallObjectArgument κ := by
  let : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  let : HasColimitsOfSize.{0, 0} (Algebra O) := hasColimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  let : LocallySmall.{us} (S.W → S.C) :=
    { hom_small X Y := by
        change Small.{us} (∀ d, X d ⟶ Y d)
        infer_instance }
  let : LocallySmall.{us} (Algebra O) := locallySmall_of_faithful (Algebra.forget O)
  let : (freeGenerators S O P).IsSmall.{us} := freeGenerators_isSmall S O P
  exact
    { preservesColimit := fun i hi f c =>
        actualFreeCellSourceSmallnessOfContinuousSources S O P hP κ hSources i hi f c }

/-- Full original-cardinal transfer with rank-free original I endpoint Hom
for acyclic closure and precisely continuous original J-domain Hom for SOA. -/
def fullModelTransferOfContinuousSources
    (_hPP : MonoidalPushoutProductAxiom S.C)
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (hSourcesI : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hSourcesJ : SourcesPreserveContinuousColimits S J
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C) κ) :
    OriginalCardinalModelTransfer S O I J κ := by
  letI : HasLimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasLimits S O
  letI : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  letI : HasLimitsOfSize.{0, 0} (Algebra O) := hasLimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : HasColimitsOfSize.{0, 0} (Algebra O) := hasColimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : (freeGenerators S O I).IsCardinalForSmallObjectArgument κ :=
    freeGenerators_smallObject S O I
      (SemiModel.ColorSource.originalIGenerators_le_cofibrations S.C I hI) hSourcesI κ
  letI : (freeGenerators S O J).IsCardinalForSmallObjectArgument κ :=
    freeGeneratorsSmallObjectOfContinuousSources S O J
      ((SemiModel.ColorSource.originalJGenerators_le_trivialCofibrations S.C J hJ).trans inf_le_left)
      κ hSourcesJ
  let hAcyclicity := freeJLeft_underlying_weak_ordinal S I hI hSourcesI h O J hJ κ
  let m := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
  let d := generationDataAtCardinal S O I J hI hJ κ hAcyclicity
  exact
    { I_smallObject := inferInstance
      J_smallObject := inferInstance
      model := m
      weak_class := weakEquivalencesAtCardinal_eq S O I J hI hJ κ hAcyclicity
      fibration_class := fibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity
      cofibration_class := cofibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity
      I_rlp := d.I_rlp
      J_rlp := d.J_rlp }


end HomotopicalAlgebra.OperadicTransfer.SourceProducers
