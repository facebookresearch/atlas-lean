/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorPresentation

/-!
# The original nested Day coend and its coupled presentation

Actual tensor-preserved inner quotients identify both object and relation
families with the original outer Day presentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uC1 uC2 uK uE uM
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorNested.Left

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C1 : Type uC1} [EnrichedCategory V C1]
  {C2 : Type uC2} [EnrichedCategory V C2]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
  {M : Type uM} [EnrichedCategory V M]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (K × E) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

variable
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p)]
  [∀ p : K × E, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
    (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq)]

/-- The unchanged actual diagram in the outer left Day kernel. -/
abbrev actualDiagram : EnrichedFunctor V (K × E) V :=
  AssociatorFaces.Left.originalOuterDiagram T F1 F2 H

/-- The actual original outer object family. -/
abbrev actualObjects : K × E → V :=
  EnrichedDayKernel.objects U (Output.functor T F1 F2) H m

/-- The actual original complete outer relation family. -/
abbrev actualRelations : (K × E) × (K × E) → V :=
  EnrichedDayKernel.relations U (Output.functor T F1 F2) H m

/-- The actual tensor-preserved inner quotient identifies each outer object word. -/
abbrev objectIso (p : K × E) :
    AssociatorPresentation.Left.innerObjects T U F1 F2 H m p ≅
      actualObjects T U F1 F2 H m p :=
  AssociatorFaces.Left.innerIso T U F1 F2 H m p

/-- The actual tensor-preserved relation quotient identifies the complete outer relation word. -/
abbrev relationIso (pq : (K × E) × (K × E)) :
    AssociatorPresentation.Left.outerRelations T U F1 F2 H m pq ≅
      actualRelations T U F1 F2 H m pq :=
  AssociatorPresentation.Left.relationIso T U F1 F2 H m pq

omit [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
  (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq)] in
/-- The inner projection is carried to the original actual inner-generator leg. -/
@[reassoc]
theorem innerProjection_objectIso (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.innerProjection T U F1 F2 H m p i ≫
        (objectIso T U F1 F2 H m p).hom =
      AssociatorFaces.Left.innerGenerator T U F1 F2 H m p i :=
  AssociatorFaces.Left.innerProjection_iso T U F1 F2 H m p i

omit [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p)]
  [∀ p : K × E, HasCoequalizer
  (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
  (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p)] in
/-- The relation projection is carried to the original actual relation-generator leg. -/
@[reassoc]
theorem relationProjection_relationIso (pq : (K × E) × (K × E)) (i : C1 × C2) :
    AssociatorPresentation.Left.relationProjection T U F1 F2 H m pq i ≫
        (relationIso T U F1 F2 H m pq).hom =
      AssociatorFaces.Left.relationGenerator T U F1 F2 H m pq.1 pq.2 i :=
  AssociatorPresentation.Left.relationProjection_iso T U F1 F2 H m pq i

/-- The complete descended outer weight face agrees with the original actual weight face. -/
@[reassoc]
theorem outerFace0_iso (pq : (K × E) × (K × E)) :
    AssociatorPresentation.Left.outerFace0 T U F1 F2 H m pq ≫
        (objectIso T U F1 F2 H m pq.1).hom =
      (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq) i ≫
      coequalizer.π (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
        (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq) ≫ _ = _
  rw [coequalizer.π_desc_assoc, Sigma.ι_comp_desc_assoc]
  rw [Category.assoc, innerProjection_objectIso]
  calc
    _ = AssociatorFaces.Left.relationGenerator T U F1 F2 H m pq.1 pq.2 i ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 :=
      (AssociatorFaces.Left.originalOuterFace0 T U F1 F2 H m pq.1 pq.2 i).symm
    _ = Sigma.ι (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq) i ≫
        coequalizer.π (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
          (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq) ≫
        (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
      simpa only [AssociatorPresentation.Left.relationProjection, Category.assoc] using
        congrArg (fun k => k ≫ Enriched.weightedCoend.face0
          (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2)
          (relationProjection_relationIso T U F1 F2 H m pq i).symm


/-- The complete descended outer diagram-action face agrees with the original actual action face. -/
@[reassoc]
theorem outerFace1_iso (pq : (K × E) × (K × E)) :
    AssociatorPresentation.Left.outerFace1 T U F1 F2 H m pq ≫
        (objectIso T U F1 F2 H m pq.2).hom =
      (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq) i ≫
      coequalizer.π (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
        (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq) ≫ _ = _
  rw [coequalizer.π_desc_assoc, Sigma.ι_comp_desc_assoc]
  rw [Category.assoc, innerProjection_objectIso]
  calc
    _ = AssociatorFaces.Left.relationGenerator T U F1 F2 H m pq.1 pq.2 i ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 :=
      (AssociatorFaces.Left.originalOuterFace1 T U F1 F2 H m pq.1 pq.2 i).symm
    _ = Sigma.ι (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq) i ≫
        coequalizer.π (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
          (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq) ≫
        (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
      simpa only [AssociatorPresentation.Left.relationProjection, Category.assoc] using
        congrArg (fun k => k ≫ Enriched.weightedCoend.face1
          (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2)
          (relationProjection_relationIso T U F1 F2 H m pq i).symm


variable [HasCoproduct (AssociatorPresentation.Left.innerObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Left.outerRelations T U F1 F2 H m)]
  [HasCoproduct (actualObjects T U F1 F2 H m)]
  [HasCoproduct (actualRelations T U F1 F2 H m)]

/-- The actual object-family comparison uses only these two particular coproducts. -/
abbrev objectCoproductIso :
    (∐ AssociatorPresentation.Left.innerObjects T U F1 F2 H m) ≅
      ∐ actualObjects T U F1 F2 H m :=
  HasColimit.isoOfNatIso
    (Discrete.natIso
      (F := Discrete.functor (AssociatorPresentation.Left.innerObjects T U F1 F2 H m))
      (G := Discrete.functor (actualObjects T U F1 F2 H m))
      (fun p => objectIso T U F1 F2 H m p.as))

/-- The actual relation-family comparison uses only these two particular coproducts. -/
abbrev relationCoproductIso :
    (∐ AssociatorPresentation.Left.outerRelations T U F1 F2 H m) ≅
      ∐ actualRelations T U F1 F2 H m :=
  HasColimit.isoOfNatIso
    (Discrete.natIso
      (F := Discrete.functor (AssociatorPresentation.Left.outerRelations T U F1 F2 H m))
      (G := Discrete.functor (actualRelations T U F1 F2 H m))
      (fun pq => relationIso T U F1 F2 H m pq.as))

omit [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Left.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Left.relationLeftMap T U F1 F2 H m pq)
  (AssociatorPresentation.Left.relationRightMap T U F1 F2 H m pq)] in
omit [HasCoproduct (actualRelations T U F1 F2 H m)] in
/-- The object coproduct comparison retains each original outer injection. -/
@[reassoc]
theorem objectι_coproductIso (p : K × E) :
    Sigma.ι (AssociatorPresentation.Left.innerObjects T U F1 F2 H m) p ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (objectIso T U F1 F2 H m p).hom ≫ Sigma.ι (actualObjects T U F1 F2 H m) p :=
  HasColimit.ι_isoOfNatIso_hom _ (Discrete.mk p)

omit [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p)]
  [∀ p : K × E, HasCoequalizer
  (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
  (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p)] in
omit [HasCoproduct (actualObjects T U F1 F2 H m)] in
/-- The relation coproduct comparison retains each complete outer relation injection. -/
@[reassoc]
theorem relationι_coproductIso (pq : (K × E) × (K × E)) :
    Sigma.ι (AssociatorPresentation.Left.outerRelations T U F1 F2 H m) pq ≫
        (relationCoproductIso T U F1 F2 H m).hom =
      (relationIso T U F1 F2 H m pq).hom ≫ Sigma.ι (actualRelations T U F1 F2 H m) pq :=
  HasColimit.ι_isoOfNatIso_hom _ (Discrete.mk pq)

/-- The original full outer weight-face coproduct map is preserved. -/
theorem outerLeftMap_iso :
    AssociatorPresentation.Left.outerLeftMap T U F1 F2 H m ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (relationCoproductIso T U F1 F2 H m).hom ≫
        EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m := by
  apply Sigma.hom_ext
  intro pq
  simp only [AssociatorPresentation.Left.outerLeftMap, Sigma.ι_comp_desc_assoc,
    Category.assoc, objectι_coproductIso, relationι_coproductIso_assoc]
  have hι : Sigma.ι (actualRelations T U F1 F2 H m) pq ≫
      EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m =
      Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 ≫
        Sigma.ι (actualObjects T U F1 F2 H m) pq.1 :=
    Sigma.ι_comp_desc _ pq
  have hc := congrArg (fun f => (relationIso T U F1 F2 H m pq).hom ≫ f) hι.symm
  exact (outerFace0_iso_assoc T U F1 F2 H m pq _).trans (by
    simpa only [Enriched.weightedCoend.face0, Category.assoc] using hc)

/-- The original full outer action-face coproduct map is preserved. -/
theorem outerRightMap_iso :
    AssociatorPresentation.Left.outerRightMap T U F1 F2 H m ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (relationCoproductIso T U F1 F2 H m).hom ≫
        EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m := by
  apply Sigma.hom_ext
  intro pq
  simp only [AssociatorPresentation.Left.outerRightMap, Sigma.ι_comp_desc_assoc,
    Category.assoc, objectι_coproductIso, relationι_coproductIso_assoc]
  have hι : Sigma.ι (actualRelations T U F1 F2 H m) pq ≫
      EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m =
      Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 ≫
        Sigma.ι (actualObjects T U F1 F2 H m) pq.2 :=
    Sigma.ι_comp_desc _ pq
  exact (outerFace1_iso_assoc T U F1 F2 H m pq _).trans
    (congrArg (fun f => (relationIso T U F1 F2 H m pq).hom ≫ f) hι.symm)

/-- Both complete original faces identify the actual parallel-pair diagrams. -/
def outerPresentationIso :
    parallelPair (AssociatorPresentation.Left.outerLeftMap T U F1 F2 H m)
      (AssociatorPresentation.Left.outerRightMap T U F1 F2 H m) ≅
    parallelPair (EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m)
      (EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m) :=
  parallelPairIso _ _ _ _ (relationCoproductIso T U F1 F2 H m)
    (objectCoproductIso T U F1 F2 H m)
    (outerLeftMap_iso T U F1 F2 H m) (outerRightMap_iso T U F1 F2 H m)

variable [HasCoequalizer (AssociatorPresentation.Left.outerLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Left.outerRightMap T U F1 F2 H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m)
    (EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m)]

/-- The chosen coupled nested quotient is the actual original nested Day value. -/
def actualIso : AssociatorPresentation.Left.nestedPoint T U F1 F2 H m ≅
    EnrichedDayKernel.obj U (Output.functor T F1 F2) H m :=
  HasColimit.isoOfNatIso (outerPresentationIso T U F1 F2 H m)

/-- The comparison preserves the original outer coequalizer projection. -/
@[reassoc]
theorem outerProjection_actualIso :
    coequalizer.π (AssociatorPresentation.Left.outerLeftMap T U F1 F2 H m)
        (AssociatorPresentation.Left.outerRightMap T U F1 F2 H m) ≫
        (actualIso T U F1 F2 H m).hom =
      (objectCoproductIso T U F1 F2 H m).hom ≫
        coequalizer.π (EnrichedDayKernel.leftMap U (Output.functor T F1 F2) H m)
          (EnrichedDayKernel.rightMap U (Output.functor T F1 F2) H m) :=
  HasColimit.ι_isoOfNatIso_hom _ WalkingParallelPair.one

/-- Both original inner and outer generator legs are preserved by the comparison. -/
@[reassoc]
theorem nestedProjection_actualIso (p : K × E) (i : C1 × C2) :
    AssociatorPresentation.Left.nestedProjection T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).hom =
      AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i := by
  simp only [AssociatorPresentation.Left.nestedProjection, Category.assoc,
    outerProjection_actualIso, objectι_coproductIso_assoc,
    innerProjection_objectIso_assoc, AssociatorFaces.Left.nestedGenerator,
    EnrichedDayKernel.gen, AssociatorFaces.Left.innerGenerator,
    Enriched.weightedCoend.ι, Functor.comp_map]
  rfl

/-- The inverse comparison retains the same original nested generators. -/
@[reassoc]
theorem nestedGenerator_actualIso_inv (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).inv =
      AssociatorPresentation.Left.nestedProjection T U F1 F2 H m p i := by
  apply (cancel_mono (actualIso T U F1 F2 H m).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (nestedProjection_actualIso T U F1 F2 H m p i).symm


/-- Equality from the actual nested Day value is checked on all original nested generators. -/
theorem hom_ext {X : V} {f g : EnrichedDayKernel.obj U (Output.functor T F1 F2) H m ⟶ X}
    (h : ∀ (p : K × E) (i : C1 × C2),
      AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫ f =
        AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫ g) : f = g := by
  apply (cancel_epi (actualIso T U F1 F2 H m).hom).1
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro p
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  have hf := nestedProjection_actualIso_assoc T U F1 F2 H m p i f
  have hg := nestedProjection_actualIso_assoc T U F1 F2 H m p i g
  simpa only [AssociatorPresentation.Left.nestedProjection,
    AssociatorFaces.Left.innerProjection, Category.assoc] using
    hf.trans ((h p i).trans hg.symm)

/-- The full parameter object is retained when checking maps out of a nested Day value. -/
theorem whiskerLeft_hom_ext (R : V) {X : V}
    {f g : R ⊗ EnrichedDayKernel.obj U (Output.functor T F1 F2) H m ⟶ X}
    (h : ∀ (p : K × E) (i : C1 × C2),
      R ◁ AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫ f =
        R ◁ AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply hom_ext T U F1 F2 H m
  intro p i
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  exact congrArg MonoidalClosed.curry (h p i)

variable [HasCoproduct (AssociatorPresentation.Left.simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Left.simultaneousRelations T U F1 F2 H m)]
  [HasCoequalizer (AssociatorPresentation.Left.simultaneousLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Left.simultaneousRightMap T U F1 F2 H m)]

/-- The actual original nested Day value identifies with its original simultaneous presentation. -/
def simultaneousIso : EnrichedDayKernel.obj U (Output.functor T F1 F2) H m ≅
    AssociatorPresentation.Left.simultaneousPoint T U F1 F2 H m :=
  (actualIso T U F1 F2 H m).symm ≪≫
    AssociatorPresentation.Left.fubiniIso T U F1 F2 H m

/-- The forward comparison retains the complete original nested generator. -/
@[reassoc]
theorem nestedGenerator_simultaneousIso_hom (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫
        (simultaneousIso T U F1 F2 H m).hom =
      AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i := by
  change AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i ≫
      (actualIso T U F1 F2 H m).inv ≫
      (AssociatorPresentation.Left.fubiniIso T U F1 F2 H m).hom = _
  calc
    _ = AssociatorPresentation.Left.nestedProjection T U F1 F2 H m p i ≫
        (AssociatorPresentation.Left.fubiniIso T U F1 F2 H m).hom :=
      by simpa only [AssociatorPresentation.Left.nestedProjection,
          AssociatorFaces.Left.innerProjection, Category.assoc] using
        nestedGenerator_actualIso_inv_assoc T U F1 F2 H m p i
          (AssociatorPresentation.Left.fubiniIso T U F1 F2 H m).hom
    _ = AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i :=
      AssociatorPresentation.Left.nestedProjection_fubini_hom T U F1 F2 H m p i

/-- The inverse comparison restores the exact same original nested generator. -/
@[reassoc]
theorem simultaneousProjection_simultaneousIso_inv (p : K × E) (i : C1 × C2) :
    AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i ≫
        (simultaneousIso T U F1 F2 H m).inv =
      AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i := by
  change AssociatorPresentation.Left.simultaneousProjection T U F1 F2 H m p i ≫
      (AssociatorPresentation.Left.fubiniIso T U F1 F2 H m).inv ≫
      (actualIso T U F1 F2 H m).hom = _
  calc
    _ = AssociatorPresentation.Left.nestedProjection T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).hom :=
      by simpa only [AssociatorPresentation.Left.simultaneousProjection,
          AssociatorPresentation.Left.nestedProjection,
          AssociatorFaces.Left.innerProjection, Category.assoc] using
        AssociatorPresentation.Left.simultaneousProjection_fubini_inv_assoc
          T U F1 F2 H m p i (actualIso T U F1 F2 H m).hom
    _ = AssociatorFaces.Left.nestedGenerator T U F1 F2 H m p i :=
      nestedProjection_actualIso T U F1 F2 H m p i

end CategoryTheory.EnrichedDayKernel.AssociatorNested.Left

namespace CategoryTheory.EnrichedDayKernel.AssociatorNested.Right

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {C1 : Type uC1} [EnrichedCategory V C1]
  {C2 : Type uC2} [EnrichedCategory V C2]
  {K : Type uK} [EnrichedCategory V K]
  {E : Type uE} [EnrichedCategory V E]
  {M : Type uM} [EnrichedCategory V M]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C1 × C2) K)
  (U : EnrichedFunctor V (E × K) M)
  (F1 : EnrichedFunctor V C1 V) (F2 : EnrichedFunctor V C2 V)
  (H : EnrichedFunctor V E V) (m : M)

variable
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p)]
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p)]
  [∀ p : E × K, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F1 F2 k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F1 F2 k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F1 F2 k)
    (EnrichedDayKernel.rightMap T F1 F2 k)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
    (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq)]

/-- The unchanged actual diagram in the outer right Day kernel. -/
abbrev actualDiagram : EnrichedFunctor V (E × K) V :=
  AssociatorFaces.Right.originalOuterDiagram T F1 F2 H

/-- The actual original outer object family. -/
abbrev actualObjects : E × K → V :=
  EnrichedDayKernel.objects U H (Output.functor T F1 F2) m

/-- The actual original complete outer relation family. -/
abbrev actualRelations : (E × K) × (E × K) → V :=
  EnrichedDayKernel.relations U H (Output.functor T F1 F2) m

/-- The actual tensor-preserved inner quotient identifies each outer object word. -/
abbrev objectIso (p : E × K) :
    AssociatorPresentation.Right.innerObjects T U F1 F2 H m p ≅
      actualObjects T U F1 F2 H m p :=
  AssociatorFaces.Right.innerIso T U F1 F2 H m p

/-- The actual tensor-preserved relation quotient identifies the complete outer relation word. -/
abbrev relationIso (pq : (E × K) × (E × K)) :
    AssociatorPresentation.Right.outerRelations T U F1 F2 H m pq ≅
      actualRelations T U F1 F2 H m pq :=
  AssociatorPresentation.Right.relationIso T U F1 F2 H m pq

omit [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
  (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq)] in
/-- The inner projection is carried to the original actual inner-generator leg. -/
@[reassoc]
theorem innerProjection_objectIso (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.innerProjection T U F1 F2 H m p i ≫
        (objectIso T U F1 F2 H m p).hom =
      AssociatorFaces.Right.innerGenerator T U F1 F2 H m p i :=
  AssociatorFaces.Right.innerProjection_iso T U F1 F2 H m p i

omit [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p)]
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p)]
  [∀ p : E × K, HasCoequalizer
  (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
  (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p)] in
/-- The relation projection is carried to the original actual relation-generator leg. -/
@[reassoc]
theorem relationProjection_relationIso (pq : (E × K) × (E × K)) (i : C1 × C2) :
    AssociatorPresentation.Right.relationProjection T U F1 F2 H m pq i ≫
        (relationIso T U F1 F2 H m pq).hom =
      AssociatorFaces.Right.relationGenerator T U F1 F2 H m pq.1 pq.2 i :=
  AssociatorPresentation.Right.relationProjection_iso T U F1 F2 H m pq i

/-- The complete descended outer weight face agrees with the original actual weight face. -/
@[reassoc]
theorem outerFace0_iso (pq : (E × K) × (E × K)) :
    AssociatorPresentation.Right.outerFace0 T U F1 F2 H m pq ≫
        (objectIso T U F1 F2 H m pq.1).hom =
      (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq) i ≫
      coequalizer.π (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
        (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq) ≫ _ = _
  rw [coequalizer.π_desc_assoc, Sigma.ι_comp_desc_assoc]
  rw [Category.assoc, innerProjection_objectIso]
  calc
    _ = AssociatorFaces.Right.relationGenerator T U F1 F2 H m pq.1 pq.2 i ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 :=
      (AssociatorFaces.Right.originalOuterFace0 T U F1 F2 H m pq.1 pq.2 i).symm
    _ = Sigma.ι (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq) i ≫
        coequalizer.π (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
          (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq) ≫
        (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
      simpa only [AssociatorPresentation.Right.relationProjection, Category.assoc] using
        congrArg (fun k => k ≫ Enriched.weightedCoend.face0
          (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2)
          (relationProjection_relationIso T U F1 F2 H m pq i).symm


/-- The complete descended outer diagram-action face agrees with the original actual action face. -/
@[reassoc]
theorem outerFace1_iso (pq : (E × K) × (E × K)) :
    AssociatorPresentation.Right.outerFace1 T U F1 F2 H m pq ≫
        (objectIso T U F1 F2 H m pq.2).hom =
      (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq) i ≫
      coequalizer.π (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
        (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq) ≫ _ = _
  rw [coequalizer.π_desc_assoc, Sigma.ι_comp_desc_assoc]
  rw [Category.assoc, innerProjection_objectIso]
  calc
    _ = AssociatorFaces.Right.relationGenerator T U F1 F2 H m pq.1 pq.2 i ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 :=
      (AssociatorFaces.Right.originalOuterFace1 T U F1 F2 H m pq.1 pq.2 i).symm
    _ = Sigma.ι (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq) i ≫
        coequalizer.π (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
          (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq) ≫
        (relationIso T U F1 F2 H m pq).hom ≫
        Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 := by
      simpa only [AssociatorPresentation.Right.relationProjection, Category.assoc] using
        congrArg (fun k => k ≫ Enriched.weightedCoend.face1
          (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2)
          (relationProjection_relationIso T U F1 F2 H m pq i).symm


variable [HasCoproduct (AssociatorPresentation.Right.innerObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Right.outerRelations T U F1 F2 H m)]
  [HasCoproduct (actualObjects T U F1 F2 H m)]
  [HasCoproduct (actualRelations T U F1 F2 H m)]

/-- The actual object-family comparison uses only these two particular coproducts. -/
abbrev objectCoproductIso :
    (∐ AssociatorPresentation.Right.innerObjects T U F1 F2 H m) ≅
      ∐ actualObjects T U F1 F2 H m :=
  HasColimit.isoOfNatIso
    (Discrete.natIso
      (F := Discrete.functor (AssociatorPresentation.Right.innerObjects T U F1 F2 H m))
      (G := Discrete.functor (actualObjects T U F1 F2 H m))
      (fun p => objectIso T U F1 F2 H m p.as))

/-- The actual relation-family comparison uses only these two particular coproducts. -/
abbrev relationCoproductIso :
    (∐ AssociatorPresentation.Right.outerRelations T U F1 F2 H m) ≅
      ∐ actualRelations T U F1 F2 H m :=
  HasColimit.isoOfNatIso
    (Discrete.natIso
      (F := Discrete.functor (AssociatorPresentation.Right.outerRelations T U F1 F2 H m))
      (G := Discrete.functor (actualRelations T U F1 F2 H m))
      (fun pq => relationIso T U F1 F2 H m pq.as))

omit [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (AssociatorPresentation.Right.relationRelations T U F1 F2 H m pq)]
  [∀ pq, HasCoequalizer (AssociatorPresentation.Right.relationLeftMap T U F1 F2 H m pq)
  (AssociatorPresentation.Right.relationRightMap T U F1 F2 H m pq)] in
omit [HasCoproduct (actualRelations T U F1 F2 H m)] in
/-- The object coproduct comparison retains each original outer injection. -/
@[reassoc]
theorem objectι_coproductIso (p : E × K) :
    Sigma.ι (AssociatorPresentation.Right.innerObjects T U F1 F2 H m) p ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (objectIso T U F1 F2 H m p).hom ≫ Sigma.ι (actualObjects T U F1 F2 H m) p :=
  HasColimit.ι_isoOfNatIso_hom _ (Discrete.mk p)

omit [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p)]
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p)]
  [∀ p : E × K, HasCoequalizer
  (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
  (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p)] in
omit [HasCoproduct (actualObjects T U F1 F2 H m)] in
/-- The relation coproduct comparison retains each complete outer relation injection. -/
@[reassoc]
theorem relationι_coproductIso (pq : (E × K) × (E × K)) :
    Sigma.ι (AssociatorPresentation.Right.outerRelations T U F1 F2 H m) pq ≫
        (relationCoproductIso T U F1 F2 H m).hom =
      (relationIso T U F1 F2 H m pq).hom ≫ Sigma.ι (actualRelations T U F1 F2 H m) pq :=
  HasColimit.ι_isoOfNatIso_hom _ (Discrete.mk pq)

/-- The original full outer weight-face coproduct map is preserved. -/
theorem outerLeftMap_iso :
    AssociatorPresentation.Right.outerLeftMap T U F1 F2 H m ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (relationCoproductIso T U F1 F2 H m).hom ≫
        EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m := by
  apply Sigma.hom_ext
  intro pq
  simp only [AssociatorPresentation.Right.outerLeftMap, Sigma.ι_comp_desc_assoc,
    Category.assoc, objectι_coproductIso, relationι_coproductIso_assoc]
  have hι : Sigma.ι (actualRelations T U F1 F2 H m) pq ≫
      EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m =
      Enriched.weightedCoend.face0 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 ≫
        Sigma.ι (actualObjects T U F1 F2 H m) pq.1 :=
    Sigma.ι_comp_desc _ pq
  have hc := congrArg (fun f => (relationIso T U F1 F2 H m pq).hom ≫ f) hι.symm
  exact (outerFace0_iso_assoc T U F1 F2 H m pq _).trans (by
    simpa only [Enriched.weightedCoend.face0, Category.assoc] using hc)

/-- The original full outer action-face coproduct map is preserved. -/
theorem outerRightMap_iso :
    AssociatorPresentation.Right.outerRightMap T U F1 F2 H m ≫
        (objectCoproductIso T U F1 F2 H m).hom =
      (relationCoproductIso T U F1 F2 H m).hom ≫
        EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m := by
  apply Sigma.hom_ext
  intro pq
  simp only [AssociatorPresentation.Right.outerRightMap, Sigma.ι_comp_desc_assoc,
    Category.assoc, objectι_coproductIso, relationι_coproductIso_assoc]
  have hι : Sigma.ι (actualRelations T U F1 F2 H m) pq ≫
      EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m =
      Enriched.weightedCoend.face1 (weight U m) (actualDiagram T F1 F2 H) pq.1 pq.2 ≫
        Sigma.ι (actualObjects T U F1 F2 H m) pq.2 :=
    Sigma.ι_comp_desc _ pq
  exact (outerFace1_iso_assoc T U F1 F2 H m pq _).trans
    (congrArg (fun f => (relationIso T U F1 F2 H m pq).hom ≫ f) hι.symm)

/-- Both complete original faces identify the actual parallel-pair diagrams. -/
def outerPresentationIso :
    parallelPair (AssociatorPresentation.Right.outerLeftMap T U F1 F2 H m)
      (AssociatorPresentation.Right.outerRightMap T U F1 F2 H m) ≅
    parallelPair (EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m)
      (EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m) :=
  parallelPairIso _ _ _ _ (relationCoproductIso T U F1 F2 H m)
    (objectCoproductIso T U F1 F2 H m)
    (outerLeftMap_iso T U F1 F2 H m) (outerRightMap_iso T U F1 F2 H m)

variable [HasCoequalizer (AssociatorPresentation.Right.outerLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Right.outerRightMap T U F1 F2 H m)]
  [HasCoequalizer (EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m)
    (EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m)]

/-- The chosen coupled nested quotient is the actual original nested Day value. -/
def actualIso : AssociatorPresentation.Right.nestedPoint T U F1 F2 H m ≅
    EnrichedDayKernel.obj U H (Output.functor T F1 F2) m :=
  HasColimit.isoOfNatIso (outerPresentationIso T U F1 F2 H m)

/-- The comparison preserves the original outer coequalizer projection. -/
@[reassoc]
theorem outerProjection_actualIso :
    coequalizer.π (AssociatorPresentation.Right.outerLeftMap T U F1 F2 H m)
        (AssociatorPresentation.Right.outerRightMap T U F1 F2 H m) ≫
        (actualIso T U F1 F2 H m).hom =
      (objectCoproductIso T U F1 F2 H m).hom ≫
        coequalizer.π (EnrichedDayKernel.leftMap U H (Output.functor T F1 F2) m)
          (EnrichedDayKernel.rightMap U H (Output.functor T F1 F2) m) :=
  HasColimit.ι_isoOfNatIso_hom _ WalkingParallelPair.one

/-- Both original inner and outer generator legs are preserved by the comparison. -/
@[reassoc]
theorem nestedProjection_actualIso (p : E × K) (i : C1 × C2) :
    AssociatorPresentation.Right.nestedProjection T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).hom =
      AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i := by
  simp only [AssociatorPresentation.Right.nestedProjection, Category.assoc,
    outerProjection_actualIso, objectι_coproductIso_assoc,
    innerProjection_objectIso_assoc, AssociatorFaces.Right.nestedGenerator,
    EnrichedDayKernel.gen, AssociatorFaces.Right.innerGenerator,
    Enriched.weightedCoend.ι, Functor.comp_map]
  rfl

/-- The inverse comparison retains the same original nested generators. -/
@[reassoc]
theorem nestedGenerator_actualIso_inv (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).inv =
      AssociatorPresentation.Right.nestedProjection T U F1 F2 H m p i := by
  apply (cancel_mono (actualIso T U F1 F2 H m).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (nestedProjection_actualIso T U F1 F2 H m p i).symm


/-- Equality from the actual nested Day value is checked on all original nested generators. -/
theorem hom_ext {X : V} {f g : EnrichedDayKernel.obj U H (Output.functor T F1 F2) m ⟶ X}
    (h : ∀ (p : E × K) (i : C1 × C2),
      AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫ f =
        AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫ g) : f = g := by
  apply (cancel_epi (actualIso T U F1 F2 H m).hom).1
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro p
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro i
  have hf := nestedProjection_actualIso_assoc T U F1 F2 H m p i f
  have hg := nestedProjection_actualIso_assoc T U F1 F2 H m p i g
  simpa only [AssociatorPresentation.Right.nestedProjection,
    AssociatorFaces.Right.innerProjection, Category.assoc] using
    hf.trans ((h p i).trans hg.symm)

/-- The full parameter object is retained when checking maps out of a nested Day value. -/
theorem whiskerLeft_hom_ext (R : V) {X : V}
    {f g : R ⊗ EnrichedDayKernel.obj U H (Output.functor T F1 F2) m ⟶ X}
    (h : ∀ (p : E × K) (i : C1 × C2),
      R ◁ AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫ f =
        R ◁ AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply hom_ext T U F1 F2 H m
  intro p i
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  exact congrArg MonoidalClosed.curry (h p i)

variable [HasCoproduct (AssociatorPresentation.Right.simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (AssociatorPresentation.Right.simultaneousRelations T U F1 F2 H m)]
  [HasCoequalizer (AssociatorPresentation.Right.simultaneousLeftMap T U F1 F2 H m)
    (AssociatorPresentation.Right.simultaneousRightMap T U F1 F2 H m)]

/-- The actual original nested Day value identifies with its original simultaneous presentation. -/
def simultaneousIso : EnrichedDayKernel.obj U H (Output.functor T F1 F2) m ≅
    AssociatorPresentation.Right.simultaneousPoint T U F1 F2 H m :=
  (actualIso T U F1 F2 H m).symm ≪≫
    AssociatorPresentation.Right.fubiniIso T U F1 F2 H m

/-- The forward comparison retains the complete original nested generator. -/
@[reassoc]
theorem nestedGenerator_simultaneousIso_hom (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫
        (simultaneousIso T U F1 F2 H m).hom =
      AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i := by
  change AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i ≫
      (actualIso T U F1 F2 H m).inv ≫
      (AssociatorPresentation.Right.fubiniIso T U F1 F2 H m).hom = _
  calc
    _ = AssociatorPresentation.Right.nestedProjection T U F1 F2 H m p i ≫
        (AssociatorPresentation.Right.fubiniIso T U F1 F2 H m).hom :=
      by simpa only [AssociatorPresentation.Right.nestedProjection,
          AssociatorFaces.Right.innerProjection, Category.assoc] using
        nestedGenerator_actualIso_inv_assoc T U F1 F2 H m p i
          (AssociatorPresentation.Right.fubiniIso T U F1 F2 H m).hom
    _ = AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i :=
      AssociatorPresentation.Right.nestedProjection_fubini_hom T U F1 F2 H m p i

/-- The inverse comparison restores the exact same original nested generator. -/
@[reassoc]
theorem simultaneousProjection_simultaneousIso_inv (p : E × K) (i : C1 × C2) :
    AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i ≫
        (simultaneousIso T U F1 F2 H m).inv =
      AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i := by
  change AssociatorPresentation.Right.simultaneousProjection T U F1 F2 H m p i ≫
      (AssociatorPresentation.Right.fubiniIso T U F1 F2 H m).inv ≫
      (actualIso T U F1 F2 H m).hom = _
  calc
    _ = AssociatorPresentation.Right.nestedProjection T U F1 F2 H m p i ≫
        (actualIso T U F1 F2 H m).hom :=
      by simpa only [AssociatorPresentation.Right.simultaneousProjection,
          AssociatorPresentation.Right.nestedProjection,
          AssociatorFaces.Right.innerProjection, Category.assoc] using
        AssociatorPresentation.Right.simultaneousProjection_fubini_inv_assoc
          T U F1 F2 H m p i (actualIso T U F1 F2 H m).hom
    _ = AssociatorFaces.Right.nestedGenerator T U F1 F2 H m p i :=
      nestedProjection_actualIso T U F1 F2 H m p i

end CategoryTheory.EnrichedDayKernel.AssociatorNested.Right
