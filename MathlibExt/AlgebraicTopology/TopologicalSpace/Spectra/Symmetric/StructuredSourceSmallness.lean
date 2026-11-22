/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.NativeFreeSourceSmallness
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.NativeClosedCellHistory
import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
import MathlibExt.CategoryTheory.Enriched.PointwiseColimitReflection

/-!
# Original structured generating sources on native closed cell histories

The original standard right-free spectrum source is retained through the
actual operator equivalence and the original module or tensor-operadic free
adjunction. Successor closedness comes from the constructed coefficient,
word and enveloping attachment histories. The same continuous ordinal
diagram and its original cocone are used in every source Hom comparison.

This is the native closed-inclusion transfer of Pavlov--Scholbach,
*Homotopy theory of symmetric powers*, §7.5, and *Symmetric operads in
abstract symmetric spectra*, Appendix 9.1 and 9.3, with the original
free/forgetful transfer of Schwede--Shipley, *Algebras and modules in
monoidal model categories*, Remark A.5.
-/

set_option autoImplicit false
noncomputable section

universe u v w uC vC uD vD vJ

open CategoryTheory Limits MonoidalCategory Topology HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory MonObj

namespace PointedCGWH.StructuredSourceSmallness

section OriginalFreeCoproduct

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- A whole original coproduct map compares to a free image of an actual base coproduct map. -/
structure OriginalFreeCoproductComparison (P : MorphismProperty C) (F : C ⥤ D)
    {X Y : D} (f : X ⟶ Y) where
  /-- The actual base coproduct arrow, with both of its original endpoints. -/
  arrow : Arrow C
  /-- Its membership is derived from the original base source labels. -/
  membership : P.coproducts.{w} arrow.hom
  /-- The full original source/target free-cofan comparison and its arrow square. -/
  comparison : Arrow.mk f ≅ F.mapArrow.obj arrow

/-- Construct both source/target comparisons from the original two cofan universal properties. -/
theorem existsOriginalFreeCoproductComparison
    (P : MorphismProperty C) (F : C ⥤ D) [HasColimitsOfSize.{w, w} C]
    [PreservesColimitsOfSize.{w, w} F] {X Y : D} (f : X ⟶ Y)
    (hf : (P.strictMap F).coproducts.{w} f) : Nonempty (OriginalFreeCoproductComparison.{w} P F f) := by
  rcases (MorphismProperty.coproducts_iff _ f).mp hf with ⟨J, hf⟩
  rcases hf with ⟨X₁, X₂, c₁, c₂, hc₁, hc₂, t, ht⟩
  have hPQ : P.strictMap F ≤ P.map F := by
    intro A B g hg
    cases hg with
    | map hp => exact P.map_mem_map F _ hp
  have hPre : ∀ j : Discrete J, ∃ q : P.toSet,
      Nonempty (Arrow.mk (t.app j) ≅ F.mapArrow.obj q.1) := by
    intro j
    obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hPQ _ (ht j)
    exact ⟨⟨Arrow.mk g, hg⟩, ⟨e.symm⟩⟩
  choose q hq using hPre
  let e : ∀ j : Discrete J, Arrow.mk (t.app j) ≅ F.mapArrow.obj (q j).1 := fun j => (hq j).some
  let A := Discrete.functor (fun j : J => (q ⟨j⟩).1.left)
  let B := Discrete.functor (fun j : J => (q ⟨j⟩).1.right)
  let t₀ : A ⟶ B := Discrete.natTrans (fun j => (q j).1.hom)
  let a : A ⋙ F ≅ X₁ := Discrete.natIso (fun j => Arrow.leftFunc.mapIso (e j).symm)
  let b : B ⋙ F ≅ X₂ := Discrete.natIso (fun j => Arrow.rightFunc.mapIso (e j).symm)
  let cAF := F.mapCocone (colimit.cocone A)
  let cBF := F.mapCocone (colimit.cocone B)
  let hAF : IsColimit cAF := isColimitOfPreserves F (colimit.isColimit A)
  let hBF : IsColimit cBF := isColimitOfPreserves F (colimit.isColimit B)
  let ca := (Cocone.precompose a.hom).obj c₁
  let cb := (Cocone.precompose b.hom).obj c₂
  let ha : IsColimit ca := (IsColimit.precomposeHomEquiv a c₁).symm hc₁
  let hb : IsColimit cb := (IsColimit.precomposeHomEquiv b c₂).symm hc₂
  let eA : F.obj (colimit A) ≅ c₁.pt := hAF.coconePointUniqueUpToIso ha
  let eB : F.obj (colimit B) ≅ c₂.pt := hBF.coconePointUniqueUpToIso hb
  let g := colimMap t₀
  let m := hc₁.desc (Cocone.mk c₂.pt (t ≫ c₂.ι))
  have hComm : F.map g ≫ eB.hom = eA.hom ≫ m := by
    apply hAF.hom_ext
    intro j
    have hA : F.map (colimit.ι A j) ≫ eA.hom = a.hom.app j ≫ c₁.ι.app j :=
      hAF.comp_coconePointUniqueUpToIso_hom ha j
    have hB : F.map (colimit.ι B j) ≫ eB.hom = b.hom.app j ≫ c₂.ι.app j :=
      hBF.comp_coconePointUniqueUpToIso_hom hb j
    have hMap : F.map (colimit.ι A j) ≫ F.map g = F.map (t₀.app j) ≫ F.map (colimit.ι B j) :=
      (F.map_comp _ _).symm.trans ((F.congr_map (ι_colimMap t₀ j)).trans (F.map_comp _ _))
    have hIso : a.hom.app j ≫ t.app j = F.map (t₀.app j) ≫ b.hom.app j := (e j).inv.w
    have hDesc : c₁.ι.app j ≫ m = t.app j ≫ c₂.ι.app j :=
      hc₁.fac (Cocone.mk c₂.pt (t ≫ c₂.ι)) j
    change F.map (colimit.ι A j) ≫ (F.map g ≫ eB.hom) = F.map (colimit.ι A j) ≫ (eA.hom ≫ m)
    calc
      _ = (F.map (colimit.ι A j) ≫ F.map g) ≫ eB.hom := (Category.assoc _ _ _).symm
      _ = (F.map (t₀.app j) ≫ F.map (colimit.ι B j)) ≫ eB.hom := congrArg (· ≫ eB.hom) hMap
      _ = F.map (t₀.app j) ≫ (b.hom.app j ≫ c₂.ι.app j) := by rw [Category.assoc, hB]
      _ = (a.hom.app j ≫ t.app j) ≫ c₂.ι.app j := by rw [← Category.assoc, ← hIso]
      _ = a.hom.app j ≫ (c₁.ι.app j ≫ m) := by rw [Category.assoc, ← hDesc]
      _ = (F.map (colimit.ι A j) ≫ eA.hom) ≫ m := by rw [← Category.assoc, ← hA]
      _ = _ := Category.assoc _ _ _
  refine ⟨⟨Arrow.mk g, ?_, (Arrow.isoMk eA eB hComm.symm).symm⟩⟩
  exact MorphismProperty.colimitsOfShape_le_coproducts P J _
    (MorphismProperty.colimitsOfShape_colimMap t₀ (fun j => (q j).2))

/-- Select the constructed full comparison for the same original coproduct arrow. -/
def originalFreeCoproductComparison
    (P : MorphismProperty C) (F : C ⥤ D) [HasColimitsOfSize.{w, w} C]
    [PreservesColimitsOfSize.{w, w} F] {X Y : D} (f : X ⟶ Y)
    (hf : (P.strictMap F).coproducts.{w} f) : OriginalFreeCoproductComparison.{w} P F f :=
  (existsOriginalFreeCoproductComparison P F f hf).some

end OriginalFreeCoproduct

open NativeFreeSourceSmallness NativeClosedCellHistory
open Operad Operad.Tensor Operad.Tensor.Enveloping.Filtration

/-- The original native symmetric spectrum carrier, without changing its presentation. -/
abbrev NativeCarrier := NativeClosedCellHistory.Carrier.{u, v}

attribute [local instance] copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  sphereSequenceMonObj sphereSequenceIsCommMonObj EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.symmetricCategory
  Spectra.NativeStableMonoidal.SymmetricSmash.monoidalClosed

section OriginalColorAdjunction

variable {W : Type w}

/-- Full Hom equivalence for the actual original color-supported source. -/
def originalColorHomEquiv (d : W) (X : NativeCarrier.{u, v}) (Y : W → NativeCarrier.{u, v}) :
    ((colorFunctor d).obj X ⟶ Y) ≃ (X ⟶ Y d) where
  toFun f := (atColorIso d X).inv ≫ f d
  invFun f := colorInclusion d f
  left_inv f := by
    apply colorHom_ext d X
    apply (cancel_epi (atColorIso d X).inv).mp
    exact colorInclusion_at d _
  right_inv f := colorInclusion_at d f

/-- The original color insertion and original component evaluation are adjoint on their actual maps. -/
def originalColorAdjunction (d : W) :
    colorFunctor (C := NativeCarrier.{u, v}) d ⊣ Pi.eval (fun _ : W => NativeCarrier.{u, v}) d :=
  Adjunction.mkOfHomEquiv
    { homEquiv := originalColorHomEquiv d
      homEquiv_naturality_left_symm := fun f g => (colorInclusion_pre d f g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change (atColorIso d X).inv ≫ (f d ≫ g d) = ((atColorIso d X).inv ≫ f d) ≫ g d
        exact (Category.assoc _ _ _).symm }

end OriginalColorAdjunction

section OriginalModules

variable (A : NativeCarrier.{u, v}) [MonObj A]

/-- The literal original module free source is built after the original standard RIGHT spectrum free. -/
def originalModuleFreeFunctor (n : Operad.SmallFinBijGroupoid) :
    PointedCGWH.{u, v} ⥤ Mod NativeCarrier.{u, v} A :=
  operatorOriginalFreeFunctor n ⋙ Mod.free A

/-- The original module forgetful functor followed by actual native operator evaluation. -/
def originalModuleEvaluation (n : Operad.SmallFinBijGroupoid) :
    Mod NativeCarrier.{u, v} A ⥤ PointedCGWH.{u, v} :=
  Mod.forget A ⋙ evaluation (symmetricOperatorObj n)

/-- Both original adjunctions give the actual module source Hom equivalence. -/
def originalModuleAdjunction (n : Operad.SmallFinBijGroupoid) :
    originalModuleFreeFunctor A n ⊣ originalModuleEvaluation A n :=
  (operatorOriginalAdjunction n).comp (Mod.freeForgetAdjunction A)

/-- Native closed smash gives the actual module forgetful functor's colimit creation. -/
@[instance_reducible] def originalModuleCreatesColimits :
    CreatesColimitsOfSize.{v, v} (Mod.forget (D := NativeCarrier.{u, v}) A) :=
  Mod.forgetCreatesColimits A

/-- Literal original module evaluation preserves the original pointwise colimits. -/
theorem originalModuleEvaluationPreservesColimits (n : Operad.SmallFinBijGroupoid) :
    PreservesColimitsOfSize.{v, v} (originalModuleEvaluation A n) := by
  let _ := originalModuleCreatesColimits A
  change PreservesColimitsOfSize.{v, v} (Mod.forget A ⋙ evaluation (symmetricOperatorObj n))
  infer_instance

/-- Every original free source label keeps its actual spectrum degree and realized generating arrow. -/
def moduleGenerators (K : MorphismProperty CGWH.{u, v}) :
    MorphismProperty (Mod NativeCarrier.{u, v} A) :=
  MorphismProperty.adjointFamilyGenerators (originalModuleFreeFunctor A)
    (K.strictMap (Under.costar CGWH.point))

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual free module map retains its tensor-map comparison and has closed original levels. -/
theorem moduleFreeMapClosed {X Y : NativeCarrier.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations NativeCarrier.{u, v} f) :
    NativeClosedCellHistory.closedInclusions ((Mod.free A).map f).hom := by
  let e : Arrow.mk ((Mod.free A).map f).hom ≅ Arrow.mk (A ◁ f) :=
    Arrow.isoMk (eqToIso (Mod.free_obj A X)) (eqToIso (Mod.free_obj A Y)) (Mod.free_map A f)
  exact (NativeClosedCellHistory.closedInclusions.arrow_mk_iso_iff e).mpr
    (NativeClosedCellHistory.leftTensorClosed A f hf)

/-- The same supplied module pushout square has a closed original old leg. -/
theorem originalModulePushoutClosed
    {X Y : NativeCarrier.{u, v}} (f : X ⟶ Y) (hf : cofibrations NativeCarrier.{u, v} f)
    {M N : Mod NativeCarrier.{u, v} A} (a : (Mod.free A).obj X ⟶ M)
    (old : M ⟶ N) (new : (Mod.free A).obj Y ⟶ N)
    (sq : IsPushout a ((Mod.free A).map f) old new) :
    NativeClosedCellHistory.closedInclusions old.hom := by
  let _ := originalModuleCreatesColimits A
  exact NativeClosedCellHistory.closedInclusions.of_isPushout (sq.map (Mod.forget A))
    (moduleFreeMapClosed A f hf)

variable (K : MorphismProperty CGWH.{u, v})
  (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)

include hK

/-- Closedness of every original module generator is derived from its actual realized free source. -/
theorem moduleGeneratorsEvaluateClosed (n : Operad.SmallFinBijGroupoid) :
    moduleGenerators A K ≤ NativeFreeSourceSmallness.closedInclusions.inverseImage
      (originalModuleEvaluation A n) := by
  rw [moduleGenerators, MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap]
  refine iSup_le fun e => ?_
  intro X Y f hf
  cases hf with
  | map hg =>
      exact moduleFreeMapClosed A _ (operatorOriginalGeneratorCofibration K hK _ hg e)
        (symmetricOperatorObj n)

/-- Every actual module relative-cell transition is evaluated on its original diagram and is closed. -/
theorem originalModuleRelativeTransitionsClosed
    {X Y : Mod NativeCarrier.{u, v} A} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (moduleGenerators A K).homFamily) f)
    (n : Operad.SmallFinBijGroupoid) :
    ∀ ⦃a b⦄ (φ : a ⟶ b), NativeFreeSourceSmallness.closedInclusions
      ((originalModuleEvaluation A n).map (c.F.map φ)) := by
  let _ := originalModuleCreatesColimits A
  let _ := originalModuleEvaluationPreservesColimits A n
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (originalModuleEvaluation A n) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  intro a b φ
  exact c.map_map_mem_of_le (originalModuleEvaluation A n) (moduleGenerators A K)
    NativeFreeSourceSmallness.closedInclusions (moduleGeneratorsEvaluateClosed A K hK n) φ

/-- Source Hom of every actual original free module generator preserves the same original cell colimit. -/
theorem preservesOriginalModuleRelativeColimit
    {Q R X Y : Mod NativeCarrier.{u, v} A} (i : Q ⟶ R) (hi : moduleGenerators A K i)
    (f : X ⟶ Y) (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (moduleGenerators A K).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op Q)) := by
  let _ := originalModuleCreatesColimits A
  let _ (n : Operad.SmallFinBijGroupoid) := originalModuleEvaluationPreservesColimits A n
  let _ (n : Operad.SmallFinBijGroupoid) :
      PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
        (originalModuleEvaluation A n) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  exact HomotopicalAlgebra.adjointFamilySource_preservesColimit
    (originalModuleFreeFunctor A) (originalModuleEvaluation A) (originalModuleAdjunction A)
    (K.strictMap (Under.costar CGWH.point)) NativeFreeSourceSmallness.closedInclusions
    (moduleGeneratorsEvaluateClosed A K hK)
    (fun g hg E _ hE =>
      PointedCGWH.realizedGeneratorSource_preservesClosedColimit K hK g hg E hE) i hi f c

/-- The actual endpoint and original inclusion legs remain colimiting after original module-source Hom. -/
def mappedOriginalModuleRelativeCocone
    {Q R X Y : Mod NativeCarrier.{u, v} A} (i : Q ⟶ R) (hi : moduleGenerators A K i)
    (f : X ⟶ Y) (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (moduleGenerators A K).homFamily) f) :
    IsColimit ((coyoneda.obj (Opposite.op Q)).mapCocone (Cocone.mk Y c.incl)) := by
  let _ := preservesOriginalModuleRelativeColimit A K hK i hi f c
  exact isColimitOfPreserves _ c.isColimit

end OriginalModules

section OriginalAlgebras

variable {W : Type w} [Small.{v} W]

local instance nativeFamilyColimits : HasColimitsOfSize.{v, v} (W → NativeCarrier.{u, v}) where
  has_colimits_of_shape _ := inferInstance

/-- The actual native symmetric smash supplies the original finite tensor operations. -/
local instance nativeFiniteTensor : FiniteTensor NativeCarrier.{u, v} := FiniteTensor.ofSymmetric _
local instance nativeTensorSlots :
    FiniteTensorPreservesColimitsInEachSlot.{_, _, v} NativeCarrier.{u, v} :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot _
local instance nativeProfileColimits (d : W) :
    HasColimitsOfShape (AnalyticIndex W d) NativeCarrier.{u, v} :=
  hasProfileColimitsOfSmallColors.{w, v} _ d

variable (O : ColoredOperadObj W NativeCarrier.{u, v})

local instance originalFreeAlgebraPreservesColimits :
    PreservesColimitsOfSize.{v, v} (freeAlgebraFunctor O) :=
  (tensorFreeAdjunction O).leftAdjoint_preservesColimits

/-- Insert the original standard RIGHT free spectrum into its original output color. -/
def originalColoredSpectrumFreeFunctor (d : W) (n : Operad.SmallFinBijGroupoid) :
    PointedCGWH.{u, v} ⥤ (W → NativeCarrier.{u, v}) :=
  operatorOriginalFreeFunctor n ⋙ colorFunctor d

/-- The actual original tensor-operadic free algebra on the original colored free spectrum source. -/
def originalAlgebraFreeFunctor (d : W) (n : Operad.SmallFinBijGroupoid) :
    PointedCGWH.{u, v} ⥤ Algebra O :=
  originalColoredSpectrumFreeFunctor d n ⋙ freeAlgebraFunctor O

/-- The original forgetful, output-color and operator evaluations retain their actual order. -/
def originalAlgebraEvaluation (d : W) (n : Operad.SmallFinBijGroupoid) :
    Algebra O ⥤ PointedCGWH.{u, v} :=
  Algebra.forget O ⋙ (Pi.eval (fun _ : W => NativeCarrier.{u, v}) d ⋙ evaluation (symmetricOperatorObj n))

/-- Compose all three original adjunctions without changing the original standard RIGHT free source. -/
def originalAlgebraAdjunction (d : W) (n : Operad.SmallFinBijGroupoid) :
    originalAlgebraFreeFunctor O d n ⊣ originalAlgebraEvaluation O d n :=
  ((operatorOriginalAdjunction n).comp (originalColorAdjunction d)).comp (tensorFreeAdjunction O)

/-- The original algebra forgetful functor creates each original source-sized filtered shape. -/
@[instance_reducible] def originalAlgebraCreatesFilteredColimits
    {J : Type v} [Category.{vJ} J] [IsFiltered J] [EssentiallySmall.{v} J] :
    CreatesColimitsOfShape J (Algebra.forget O) :=
  tensorAlgebraForgetCreatesFilteredColimits O

/-- The original ordered diagram has its colimits created by the same forgetful functor. -/
@[instance_reducible] def originalAlgebraCreatesOrderedColimits
    (J : Type v) [LinearOrder J] [OrderBot J] :
    CreatesColimitsOfShape J (Algebra.forget O) := by
  let _ : IsFiltered J := inferInstance
  let _ : EssentiallySmall.{v} J := essentiallySmall_of_small_of_locallySmall _
  exact originalAlgebraCreatesFilteredColimits O

/-- Every proper original ordinal segment is preserved with its same colimit cocone. -/
theorem originalAlgebraPreservesContinuous
    (J : Type v) [LinearOrder J] [OrderBot J] :
    PreservesWellOrderContinuousOfShape J (Algebra.forget O) where
  preservesColimitsOfShape m hm := by
    let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let _ : IsFiltered (Set.Iio m) := inferInstance
    let _ : EssentiallySmall.{v} (Set.Iio m) := essentiallySmall_of_small_of_locallySmall _
    let _ := originalAlgebraCreatesFilteredColimits (J := Set.Iio m) O
    infer_instance

/-- Joint evaluation reconstructs the original enriched colimit UP with its original point and full Hom action. -/
def originalNativeCoconeFromEvaluations
    {J : Type v} [Category.{vJ} J] {E : J ⥤ NativeCarrier.{u, v}} (c : Cocone E)
    (hc : ∀ a : SymmetricOperatorIndex.{u, v}, IsColimit ((evaluation a).mapCocone c)) :
    IsColimit c :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc

section SuppliedClosedDiagram

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (K : MorphismProperty CGWH.{u, v})
  (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
  {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
  (hg : (K.strictMap (Under.costar CGWH.point)) g)
  (d : W) (n : Operad.SmallFinBijGroupoid)
  (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ Algebra O) [E.IsWellOrderContinuous]
  (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), NativeClosedCellHistory.familyClosedInclusions W
    ((Algebra.forget O).map (E.map φ)))

include K hK g hg hE

/-- Hom of the actual original free algebra source preserves the supplied original closed diagram. -/
theorem preservesOriginalAlgebraClosedColimit :
    PreservesColimit E (coyoneda.obj (Opposite.op ((originalAlgebraFreeFunctor O d n).obj Q))) := by
  let J := realizedGeneratorCardinal.{v}.ord.ToType
  let U := Algebra.forget O
  let ev := originalAlgebraEvaluation O d n
  let _ := originalAlgebraCreatesOrderedColimits O J
  let _ : PreservesColimitsOfShape J ev := by
    change PreservesColimitsOfShape J
      (U ⋙ (Pi.eval (fun _ : W => NativeCarrier.{u, v}) d ⋙ evaluation (symmetricOperatorObj n)))
    infer_instance
  let _ : PreservesWellOrderContinuousOfShape J ev :=
    { preservesColimitsOfShape := fun m hm => by
        let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
        let _ : IsFiltered (Set.Iio m) := inferInstance
        let _ : EssentiallySmall.{v} (Set.Iio m) := essentiallySmall_of_small_of_locallySmall _
        let _ := originalAlgebraCreatesFilteredColimits (J := Set.Iio m) O
        change PreservesColimitsOfShape (Set.Iio m)
          (U ⋙ (Pi.eval (fun _ : W => NativeCarrier.{u, v}) d ⋙ evaluation (symmetricOperatorObj n)))
        infer_instance }
  let _ : (E ⋙ ev).IsWellOrderContinuous := inferInstance
  let _ : PreservesColimit (E ⋙ ev) (coyoneda.obj (Opposite.op Q)) :=
    PointedCGWH.realizedGeneratorSource_preservesClosedColimit K hK g hg (E ⋙ ev)
      (by intro a b φ; exact hE φ d (symmetricOperatorObj n))
  exact (originalAlgebraAdjunction O d n).preservesColimit_leftAdjointSource Q E

/-- The caller's original algebra colimit legs survive Hom from the same original free source. -/
def mappedOriginalAlgebraClosedCocone (c : Cocone E) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op ((originalAlgebraFreeFunctor O d n).obj Q))).mapCocone c) := by
  let _ := preservesOriginalAlgebraClosedColimit O K hK g hg d n E hE
  exact isColimitOfPreserves _ hc

end SuppliedClosedDiagram

section ActualAlgebraCells

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original carrier-family cofibration condition at every actual output color. -/
def familyCofibrations : MorphismProperty (W → NativeCarrier.{u, v}) :=
  fun _ _ f => ∀ d : W, cofibrations NativeCarrier.{u, v} (f d)

omit [Small.{v} W] in
/-- The actual source color is retained and every other color map is an isomorphism. -/
theorem colorMapCofibration (d : W) {X Y : NativeCarrier.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations NativeCarrier.{u, v} f) : familyCofibrations (colorMap d f) := by
  intro e
  by_cases he : e = d
  · subst e
    let q : Arrow.mk (colorMap d f d) ≅ Arrow.mk f :=
      Arrow.isoMk (atColorIso d X) (atColorIso d Y) (colorMap_at d f).symm
    exact ((cofibrations NativeCarrier.{u, v}).arrow_mk_iso_iff q).mpr hf
  · have hi : IsIso (colorMap d f e) := by
      let a := awayColorIso d X e he
      let b := awayColorIso d Y e he
      have h : colorMap d f e = a.hom ≫ b.inv := dite_eq_right he
      rw [h]
      infer_instance
    exact (cofibrations NativeCarrier.{u, v}).of_isIso _

omit [Small.{v} W] in
/-- Actual original coproduct cofibration maps are tested through their original cofan maps at every color. -/
theorem familyCoproductsCofibration (P : MorphismProperty (W → NativeCarrier.{u, v}))
    (hP : P ≤ familyCofibrations) : P.coproducts.{v} ≤ familyCofibrations := by
  intro X Y f hf d
  rcases (MorphismProperty.coproducts_iff _ f).mp hf with ⟨J, hf⟩
  rcases hf with ⟨X₁, X₂, c₁, c₂, hc₁, hc₂, t, ht⟩
  let E := Pi.eval (fun _ : W => NativeCarrier.{u, v}) d
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := cofibrations NativeCarrier.{u, v}) (X₁ ⋙ E) (X₂ ⋙ E)
    (E.mapCocone c₁) (E.mapCocone c₂) (isColimitOfPreserves E hc₁) (isColimitOfPreserves E hc₂)
    (Functor.whiskerRight t E) (fun j => hP _ (ht j) d) _ (by
      intro j
      exact (E.map_comp _ _).symm.trans
        ((E.congr_map (hc₁.fac (Cocone.mk c₂.pt (t ≫ c₂.ι)) j)).trans (E.map_comp _ _)))

/-- Keep each original source color, degree and actual freely pointed realized generator in the label. -/
def originalFamilyGenerators (K : MorphismProperty CGWH.{u, v}) :
    MorphismProperty (W → NativeCarrier.{u, v}) :=
  MorphismProperty.adjointFamilyGenerators
    (fun q : W × Operad.SmallFinBijGroupoid => originalColoredSpectrumFreeFunctor q.1 q.2)
    (K.strictMap (Under.costar CGWH.point))

/-- The actual free O-images of precisely those original correlated source labels. -/
def algebraGenerators (K : MorphismProperty CGWH.{u, v}) : MorphismProperty (Algebra O) :=
  (originalFamilyGenerators (W := W) K).strictMap (freeAlgebraFunctor O)

omit [Small.{v} W] in
/-- Original realized family cofibrations are derived before forming their algebra free images. -/
theorem originalFamilyGeneratorsCofibration (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    originalFamilyGenerators (W := W) K ≤ familyCofibrations := by
  rw [originalFamilyGenerators, MorphismProperty.adjointFamilyGenerators_eq_iSup_strictMap]
  refine iSup_le fun q => ?_
  intro X Y f hf
  cases hf with
  | map hg => exact colorMapCofibration q.1 _ (operatorOriginalGeneratorCofibration K hK _ hg q.2)

/-- Compare the original supplied free-algebra pushout old leg to the constructed original A5 old leg. -/
theorem originalAlgebraPushoutClosed
    {X Y : W → NativeCarrier.{u, v}} (x : X ⟶ Y) (hx : familyCofibrations x)
    {A D : Algebra O} (a : freeAlgebra O X ⟶ A) (old : A ⟶ D) (new : freeAlgebra O Y ⟶ D)
    (sq : IsPushout a ((freeAlgebraFunctor O).map x) old new) :
    NativeClosedCellHistory.familyClosedInclusions W old.hom := by
  let cs := Operad.Tensor.Enveloping.OriginalAttachment.isPushout O A x a
  let e := sq.isoIsPushout _ _ cs
  let q : Arrow.mk old ≅ Arrow.mk (Operad.Tensor.Enveloping.OriginalAttachment.oldMap O A x a) :=
    Arrow.isoMk (Iso.refl A) e (by simpa using (sq.inl_isoIsPushout_hom _ _ cs).symm)
  exact ((NativeClosedCellHistory.familyClosedInclusions W).arrow_mk_iso_iff
    ((Algebra.forget O).mapArrow.mapIso q)).mpr
      (NativeClosedCellHistory.originalEnvelopingOldMapClosed O A x a hx)

/-- The full original free-cofan comparison retains both source objects and the supplied pushout square. -/
theorem originalAlgebraCoproductPushoutClosed
    (P : MorphismProperty (W → NativeCarrier.{u, v})) (hP : P ≤ familyCofibrations)
    {X Y : Algebra O} (m : X ⟶ Y) (hm : (P.strictMap (freeAlgebraFunctor O)).coproducts.{v} m)
    {A D : Algebra O} (a : X ⟶ A) (old : A ⟶ D) (new : Y ⟶ D)
    (sq : IsPushout a m old new) : NativeClosedCellHistory.familyClosedInclusions W old.hom := by
  let q := originalFreeCoproductComparison P (freeAlgebraFunctor O) m hm
  let eX := Arrow.leftFunc.mapIso q.comparison
  let eY := Arrow.rightFunc.mapIso q.comparison
  let a' := eX.inv ≫ a
  let new' := eY.inv ≫ new
  have sq' : IsPushout a' ((freeAlgebraFunctor O).map q.arrow.hom) old new' := by
    apply sq.of_iso' eX.symm (Iso.refl A) eY.symm (Iso.refl D)
    · simp [a']
    · exact q.comparison.inv.w
    · simp
    · simp [new']
  exact originalAlgebraPushoutClosed O q.arrow.hom
    (familyCoproductsCofibration P hP _ q.membership) a' old new' sq'

/-- Every original successor attachment of a coproduct of the free generators has closed underlying levels. -/
theorem algebraGeneratorSuccessorsClosed (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions) :
    ((algebraGenerators O K).coproducts.{v}).pushouts ≤
      (NativeClosedCellHistory.familyClosedInclusions W).inverseImage (Algebra.forget O) := by
  rintro X Y f ⟨A, D, m, a, new, hm, sq⟩
  exact originalAlgebraCoproductPushoutClosed O (originalFamilyGenerators K)
    (originalFamilyGeneratorsCofibration K hK) m hm a f new sq

instance algebraClosed_isStableUnderTransfiniteComposition :
    ((NativeClosedCellHistory.familyClosedInclusions W).inverseImage
      (Algebra.forget O)).IsStableUnderTransfiniteComposition.{v} where
  isStableUnderTransfiniteCompositionOfShape J :=
    { le := by
        rintro X Y f ⟨c⟩
        let U := Algebra.forget O
        let _ := originalAlgebraCreatesOrderedColimits O J
        let _ := originalAlgebraPreservesContinuous O J
        let d : (NativeClosedCellHistory.familyClosedInclusions W).TransfiniteCompositionOfShape J
            (U.map f) :=
          { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map U
            map_mem j hj := c.map_mem j hj }
        exact (NativeClosedCellHistory.familyClosedInclusions W).transfiniteCompositionsOfShape_le J _ d.mem }

/-- The same original outer cell history is classified using the derived actual A5 successor maps. -/
def originalAlgebraClosedRelativeHistory (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {X Y : Algebra O} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    ((NativeClosedCellHistory.familyClosedInclusions W).inverseImage
      (Algebra.forget O)).TransfiniteCompositionOfShape realizedGeneratorCardinal.{v}.ord.ToType f :=
  (c.transfiniteCompositionOfShape (algebraGenerators O K).homFamily).ofLE
    (by simpa only [MorphismProperty.ofHoms_homFamily] using algebraGeneratorSuccessorsClosed O K hK)

/-- Every actual original algebra relative-cell transition is closed at every original color and operator. -/
theorem originalAlgebraRelativeTransitionsClosed (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {X Y : Algebra O} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    ∀ ⦃a b⦄ (φ : a ⟶ b), NativeClosedCellHistory.familyClosedInclusions W
      ((Algebra.forget O).map (c.F.map φ)) := by
  intro a b φ
  exact (originalAlgebraClosedRelativeHistory O K hK f c).mem_map φ

/-- The actual original free algebra source preserves the same actual original algebra cell colimit. -/
theorem preservesOriginalAlgebraRelativeColimit
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (K.strictMap (Under.costar CGWH.point)) g) (d : W) (n : Operad.SmallFinBijGroupoid)
    {X Y : Algebra O} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    PreservesColimit c.F
      (coyoneda.obj (Opposite.op ((originalAlgebraFreeFunctor O d n).obj Q))) := by
  let _ : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
  exact preservesOriginalAlgebraClosedColimit O K hK g hg d n c.F
    (originalAlgebraRelativeTransitionsClosed O K hK f c)

/-- The actual endpoint and all original algebra-cell inclusion legs remain colimiting after free-source Hom. -/
def mappedOriginalAlgebraRelativeCocone
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R : PointedCGWH.{u, v}} (g : Q ⟶ R)
    (hg : (K.strictMap (Under.costar CGWH.point)) g) (d : W) (n : Operad.SmallFinBijGroupoid)
    {X Y : Algebra O} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    IsColimit
      ((coyoneda.obj (Opposite.op ((originalAlgebraFreeFunctor O d n).obj Q))).mapCocone (Cocone.mk Y c.incl)) := by
  let _ := preservesOriginalAlgebraRelativeColimit O K hK g hg d n f c
  exact isColimitOfPreserves _ c.isColimit

/-- Every original free-generator source retains its full Arrow equality and the same actual cell diagram. -/
theorem preservesAlgebraGeneratorRelativeColimit
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R X Y : Algebra O} (i : Q ⟶ R) (hi : algebraGenerators O K i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op Q)) := by
  cases hi with
  | @map Q₀ R₀ j hj =>
      obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff
        (fun q : W × Operad.SmallFinBijGroupoid => originalColoredSpectrumFreeFunctor q.1 q.2)
        (K.strictMap (Under.costar CGWH.point)) j).mp hj
      let e : Q₀ ≅ (originalColoredSpectrumFreeFunctor q.1.1 q.1.2).obj q.2.1.left :=
        Arrow.leftFunc.mapIso (eqToIso hq)
      let p : (freeAlgebraFunctor O).obj Q₀ ≅ (originalAlgebraFreeFunctor O q.1.1 q.1.2).obj q.2.1.left :=
        (freeAlgebraFunctor O).mapIso e
      let _ : PreservesColimit c.F
          (coyoneda.obj (Opposite.op ((originalAlgebraFreeFunctor O q.1.1 q.1.2).obj q.2.1.left))) :=
        preservesOriginalAlgebraRelativeColimit O K hK q.2.1.hom q.2.2 q.1.1 q.1.2 f c
      exact preservesColimit_of_natIso c.F (coyoneda.mapIso p.op)

/-- Hom from any original actual algebra generator preserves the original endpoint and inclusion cocone. -/
def mappedAlgebraGeneratorRelativeCocone
    (K : MorphismProperty CGWH.{u, v})
    (hK : K ≤ CGWH.realizedBoundaryInclusions ⊔ CGWH.realizedHornInclusions)
    {Q R X Y : Algebra O} (i : Q ⟶ R) (hi : algebraGenerators O K i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun _ : realizedGeneratorCardinal.{v}.ord.ToType => (algebraGenerators O K).homFamily) f) :
    IsColimit ((coyoneda.obj (Opposite.op Q)).mapCocone (Cocone.mk Y c.incl)) := by
  let _ := preservesAlgebraGeneratorRelativeColimit O K hK i hi f c
  exact isColimitOfPreserves _ c.isColimit

end ActualAlgebraCells

end OriginalAlgebras

end PointedCGWH.StructuredSourceSmallness
