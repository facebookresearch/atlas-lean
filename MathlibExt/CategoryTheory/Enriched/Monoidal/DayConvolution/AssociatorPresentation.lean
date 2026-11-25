/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFaces

/-!
# Actual nested Day presentations and their simultaneous quotient

The maps below use both complete relation faces from the original nested Day
presentation. Their Fubini comparison reuses the original weighted-coend theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uC1 uC2 uK uE uM
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorPresentation.Left

open AssociatorFaces

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

/-- The actual inner quotient family in the original left-nested presentation. -/
abbrev innerObjects : K × E → V := fun p => AssociatorFaces.Left.innerPoint T U F1 F2 H m p

/-- The original complete outer relation word before inner descent. -/
abbrev relationObjects (pq : (K × E) × (K × E)) : C1 × C2 → V :=
  AssociatorFaces.Left.outerRelations T U F1 F2 H m pq.1 pq.2

/-- Both original Hom factors are retained in the mixed relation family. -/
abbrev relationRelations (pq : (K × E) × (K × E)) :
    (C1 × C2) × (C1 × C2) → V :=
  AssociatorFaces.Left.mixedRelations T U F1 F2 H m pq.1 pq.2

variable
  [∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq)]

/-- The actual mapped inner weight face in the full outer relation word. -/
abbrev relationLeftMap (pq : (K × E) × (K × E)) :
    (∐ relationRelations T U F1 F2 H m pq) ⟶ ∐ relationObjects T U F1 F2 H m pq :=
  Sigma.desc fun ij => AssociatorFaces.Left.r0 T U F1 F2 H m pq.1 pq.2 ij.1 ij.2 ≫
    Sigma.ι (relationObjects T U F1 F2 H m pq) ij.1

/-- The actual mapped inner action face in the full outer relation word. -/
abbrev relationRightMap (pq : (K × E) × (K × E)) :
    (∐ relationRelations T U F1 F2 H m pq) ⟶ ∐ relationObjects T U F1 F2 H m pq :=
  Sigma.desc fun ij => AssociatorFaces.Left.r1 T U F1 F2 H m pq.1 pq.2 ij.1 ij.2 ≫
    Sigma.ι (relationObjects T U F1 F2 H m pq) ij.2

variable [∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
  (relationRightMap T U F1 F2 H m pq)]

/-- The original outer relation family after its actual inner quotient. -/
abbrev outerRelations : (K × E) × (K × E) → V := fun pq =>
  coequalizer (relationLeftMap T U F1 F2 H m pq) (relationRightMap T U F1 F2 H m pq)

/-- Descend the complete outer weight face using its proved compatibility with both inner faces. -/
abbrev outerFace0 (pq : (K × E) × (K × E)) :
    outerRelations T U F1 F2 H m pq ⟶ innerObjects T U F1 F2 H m pq.1 :=
  coequalizer.desc (Sigma.desc fun i =>
    AssociatorFaces.Left.a0 T U F1 F2 H m pq.1 pq.2 i ≫
      AssociatorFaces.Left.innerProjection T U F1 F2 H m pq.1 i) (by
        apply Sigma.hom_ext
        intro ij
        simp only [relationLeftMap, relationRightMap, Sigma.ι_comp_desc_assoc,
          Category.assoc, Sigma.ι_comp_desc]
        simpa only [AssociatorFaces.Left.a0, Category.assoc] using
          AssociatorFaces.Left.outerFace0_innerProjection
            T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)

/-- Descend the complete outer action face using its proved compatibility with both inner faces. -/
abbrev outerFace1 (pq : (K × E) × (K × E)) :
    outerRelations T U F1 F2 H m pq ⟶ innerObjects T U F1 F2 H m pq.2 :=
  coequalizer.desc (Sigma.desc fun i =>
    AssociatorFaces.Left.a1 T U F1 F2 H m pq.1 pq.2 i ≫
      AssociatorFaces.Left.innerProjection T U F1 F2 H m pq.2 i) (by
        apply Sigma.hom_ext
        intro ij
        simp only [relationLeftMap, relationRightMap, Sigma.ι_comp_desc_assoc,
          Category.assoc, Sigma.ι_comp_desc]
        exact AssociatorFaces.Left.outerFace1_innerProjection
          T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)


/-- The actual inner projection of the full outer relation word. -/
abbrev relationProjection (pq : (K × E) × (K × E)) (i : C1 × C2) :
    relationObjects T U F1 F2 H m pq i ⟶ outerRelations T U F1 F2 H m pq :=
  Sigma.ι (relationObjects T U F1 F2 H m pq) i ≫
    coequalizer.π (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq)

/-- Tensor preservation identifies the actual relation quotient with the original outer relation. -/
@[no_expose]
def relationIso (pq : (K × E) × (K × E)) :
    outerRelations T U F1 F2 H m pq ≅
      (AssociatorFaces.Left.relationFunctor U H m pq.1 pq.2).obj
        (EnrichedDayKernel.obj T F1 F2 pq.1.1) := by
  let W := EnrichedDayKernel.weight T pq.1.1
  let Q := F1.externalTensor F2
  let B := H.obj pq.1.2
  letI : PreservesColimit (Discrete.functor (Enriched.weightedCoend.objects W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  letI : PreservesColimit (Discrete.functor (Enriched.weightedCoend.relations W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  letI : PreservesColimit
      (parallelPair (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso W Q
    (AssociatorFaces.Left.relationFunctor U H m pq.1 pq.2)

omit [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p)]
  [∀ p : K × E, HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p)]
  [∀ p : K × E, HasCoequalizer
    (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p)] in
/-- The relation comparison preserves every original complete relation generator. -/
@[reassoc]
theorem relationProjection_iso (pq : (K × E) × (K × E)) (i : C1 × C2) :
    relationProjection T U F1 F2 H m pq i ≫ (relationIso T U F1 F2 H m pq).hom =
      (AssociatorFaces.Left.relationFunctor U H m pq.1 pq.2).map
        (EnrichedDayKernel.gen T F1 F2 pq.1.1 i) := by
  let W := EnrichedDayKernel.weight T pq.1.1
  let Q := F1.externalTensor F2
  let B := H.obj pq.1.2
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.objects W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit (Discrete.functor (Enriched.weightedCoend.relations W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  let : PreservesColimit
      (parallelPair (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q))
      (tensorRight B) :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight B)
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso_generator W Q
    (AssociatorFaces.Left.relationFunctor U H m pq.1 pq.2) i

variable [HasCoproduct (innerObjects T U F1 F2 H m)]
  [HasCoproduct (outerRelations T U F1 F2 H m)]

/-- The actual outer weight-face coproduct map after inner descent. -/
abbrev outerLeftMap : (∐ outerRelations T U F1 F2 H m) ⟶ ∐ innerObjects T U F1 F2 H m :=
  Sigma.desc fun pq => outerFace0 T U F1 F2 H m pq ≫
    Sigma.ι (innerObjects T U F1 F2 H m) pq.1

/-- The actual outer action-face coproduct map after inner descent. -/
abbrev outerRightMap : (∐ outerRelations T U F1 F2 H m) ⟶ ∐ innerObjects T U F1 F2 H m :=
  Sigma.desc fun pq => outerFace1 T U F1 F2 H m pq ≫
    Sigma.ι (innerObjects T U F1 F2 H m) pq.2

variable [HasCoequalizer (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)]

/-- The original coupled nested quotient. -/
abbrev nestedPoint : V :=
  coequalizer (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)

/-- Every actual nested generator retains its inner and outer projection legs. -/
abbrev nestedProjection (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.objects T U F1 F2 H m p i ⟶ nestedPoint T U F1 F2 H m :=
  AssociatorFaces.Left.innerProjection T U F1 F2 H m p i ≫
    Sigma.ι (innerObjects T U F1 F2 H m) p ≫
      coequalizer.π (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)

/-- The literal simultaneous original object family. -/
abbrev simultaneousObjects : (K × E) × (C1 × C2) → V := fun pi =>
  AssociatorFaces.Left.objects T U F1 F2 H m pi.1 pi.2

/-- The simultaneous relation family keeps the two complete original faces separately. -/
abbrev simultaneousRelations :
    Sum (((K × E) × (K × E)) × (C1 × C2))
      ((K × E) × ((C1 × C2) × (C1 × C2))) → V :=
  Sum.elim
    (fun pqi => AssociatorFaces.Left.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pij => AssociatorFaces.Left.innerRelations T U F1 F2 H m pij.1 pij.2)

variable [HasCoproduct (simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (simultaneousRelations T U F1 F2 H m)]

/-- The simultaneous weight-face map uses the original outer and inner weight faces. -/
abbrev simultaneousLeftMap :
    (∐ simultaneousRelations T U F1 F2 H m) ⟶ ∐ simultaneousObjects T U F1 F2 H m :=
  Sigma.desc (Sum.rec (motive := fun r =>
      simultaneousRelations T U F1 F2 H m r ⟶ ∐ simultaneousObjects T U F1 F2 H m)
    (fun pqi => AssociatorFaces.Left.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pqi.1.1, pqi.2))
    (fun pij => AssociatorFaces.Left.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pij.1, pij.2.1)))


/-- The simultaneous action-face map uses the original outer and inner action faces. -/
abbrev simultaneousRightMap :
    (∐ simultaneousRelations T U F1 F2 H m) ⟶ ∐ simultaneousObjects T U F1 F2 H m :=
  Sigma.desc (Sum.rec (motive := fun r =>
      simultaneousRelations T U F1 F2 H m r ⟶ ∐ simultaneousObjects T U F1 F2 H m)
    (fun pqi => AssociatorFaces.Left.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pqi.1.2, pqi.2))
    (fun pij => AssociatorFaces.Left.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pij.1, pij.2.2)))


variable [HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
  (simultaneousRightMap T U F1 F2 H m)]

/-- The simultaneous quotient of the actual original Day relation families. -/
abbrev simultaneousPoint : V :=
  coequalizer (simultaneousLeftMap T U F1 F2 H m) (simultaneousRightMap T U F1 F2 H m)

/-- The actual two-variable original generator in the simultaneous quotient. -/
abbrev simultaneousProjection (p : K × E) (i : C1 × C2) :
    AssociatorFaces.Left.objects T U F1 F2 H m p i ⟶ simultaneousPoint T U F1 F2 H m :=
  Sigma.ι (simultaneousObjects T U F1 F2 H m) (p, i) ≫
    coequalizer.π (simultaneousLeftMap T U F1 F2 H m) (simultaneousRightMap T U F1 F2 H m)

/-- The original Fubini theorem compares these actual presentations using the proved full faces. -/
@[no_expose]
def fubiniIso : nestedPoint T U F1 F2 H m ≅ simultaneousPoint T U F1 F2 H m := by
  exact @Enriched.weightedCoend.fubiniIso V _ (K × E) (C1 × C2)
    (simultaneousObjects T U F1 F2 H m)
    (fun pij => AssociatorFaces.Left.innerRelations T U F1 F2 H m pij.1 pij.2)
    (fun pij => AssociatorFaces.Left.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pij => AssociatorFaces.Left.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pqi => AssociatorFaces.Left.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqij => AssociatorFaces.Left.mixedRelations T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2)
    (fun pqij => AssociatorFaces.Left.r0 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqij => AssociatorFaces.Left.r1 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqi => AssociatorFaces.Left.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqi => AssociatorFaces.Left.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (inferInstance : ∀ p : K × E,
      HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p))
    (inferInstance : ∀ p : K × E,
      HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p))
    (inferInstance : ∀ p : K × E, HasCoequalizer
      (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
      (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p))
    (inferInstance : ∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq))
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Left.outerFace0_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Left.outerFace1_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (inferInstance : HasCoproduct (outerRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (innerObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (outerLeftMap T U F1 F2 H m)
      (outerRightMap T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
      (simultaneousRightMap T U F1 F2 H m))
private theorem fubiniIso_generators_private (p : K × E) (i : C1 × C2) :
    (nestedProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).hom =
      simultaneousProjection T U F1 F2 H m p i) ∧
    (simultaneousProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).inv =
      nestedProjection T U F1 F2 H m p i) := by
  exact @Enriched.weightedCoend.fubiniIso_generators V _ (K × E) (C1 × C2)
    (simultaneousObjects T U F1 F2 H m)
    (fun pij => AssociatorFaces.Left.innerRelations T U F1 F2 H m pij.1 pij.2)
    (fun pij => AssociatorFaces.Left.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pij => AssociatorFaces.Left.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pqi => AssociatorFaces.Left.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqij => AssociatorFaces.Left.mixedRelations T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2)
    (fun pqij => AssociatorFaces.Left.r0 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqij => AssociatorFaces.Left.r1 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqi => AssociatorFaces.Left.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqi => AssociatorFaces.Left.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (inferInstance : ∀ p : K × E,
      HasCoproduct (AssociatorFaces.Left.innerRelations T U F1 F2 H m p))
    (inferInstance : ∀ p : K × E,
      HasCoproduct (AssociatorFaces.Left.objects T U F1 F2 H m p))
    (inferInstance : ∀ p : K × E, HasCoequalizer
      (AssociatorFaces.Left.innerLeftMap T U F1 F2 H m p)
      (AssociatorFaces.Left.innerRightMap T U F1 F2 H m p))
    (inferInstance : ∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq))
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Left.outerFace0_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Left.outerFace1_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (inferInstance : HasCoproduct (outerRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (innerObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (outerLeftMap T U F1 F2 H m)
      (outerRightMap T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
      (simultaneousRightMap T U F1 F2 H m)) p i

/-- The forward Fubini map preserves both original nested generator legs. -/
@[reassoc]
theorem nestedProjection_fubini_hom (p : K × E) (i : C1 × C2) :
    nestedProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).hom =
      simultaneousProjection T U F1 F2 H m p i :=
  (fubiniIso_generators_private T U F1 F2 H m p i).1

/-- The inverse Fubini map restores both original nested generator legs. -/
@[reassoc]
theorem simultaneousProjection_fubini_inv (p : K × E) (i : C1 × C2) :
    simultaneousProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).inv =
      nestedProjection T U F1 F2 H m p i :=
  (fubiniIso_generators_private T U F1 F2 H m p i).2


end CategoryTheory.EnrichedDayKernel.AssociatorPresentation.Left

namespace CategoryTheory.EnrichedDayKernel.AssociatorPresentation.Right

open AssociatorFaces

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

/-- The actual inner quotient family in the original right-nested presentation. -/
abbrev innerObjects : E × K → V := fun p => AssociatorFaces.Right.innerPoint T U F1 F2 H m p

/-- The original complete outer relation word before inner descent. -/
abbrev relationObjects (pq : (E × K) × (E × K)) : C1 × C2 → V :=
  AssociatorFaces.Right.outerRelations T U F1 F2 H m pq.1 pq.2

/-- Both original Hom factors are retained in the mixed relation family. -/
abbrev relationRelations (pq : (E × K) × (E × K)) :
    (C1 × C2) × (C1 × C2) → V :=
  AssociatorFaces.Right.mixedRelations T U F1 F2 H m pq.1 pq.2

variable
  [∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq)]
  [∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq)]

/-- The actual mapped inner weight face in the full outer relation word. -/
abbrev relationLeftMap (pq : (E × K) × (E × K)) :
    (∐ relationRelations T U F1 F2 H m pq) ⟶ ∐ relationObjects T U F1 F2 H m pq :=
  Sigma.desc fun ij => AssociatorFaces.Right.r0 T U F1 F2 H m pq.1 pq.2 ij.1 ij.2 ≫
    Sigma.ι (relationObjects T U F1 F2 H m pq) ij.1

/-- The actual mapped inner action face in the full outer relation word. -/
abbrev relationRightMap (pq : (E × K) × (E × K)) :
    (∐ relationRelations T U F1 F2 H m pq) ⟶ ∐ relationObjects T U F1 F2 H m pq :=
  Sigma.desc fun ij => AssociatorFaces.Right.r1 T U F1 F2 H m pq.1 pq.2 ij.1 ij.2 ≫
    Sigma.ι (relationObjects T U F1 F2 H m pq) ij.2

variable [∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
  (relationRightMap T U F1 F2 H m pq)]

/-- The original outer relation family after its actual inner quotient. -/
abbrev outerRelations : (E × K) × (E × K) → V := fun pq =>
  coequalizer (relationLeftMap T U F1 F2 H m pq) (relationRightMap T U F1 F2 H m pq)

/-- Descend the complete outer weight face using its proved compatibility with both inner faces. -/
abbrev outerFace0 (pq : (E × K) × (E × K)) :
    outerRelations T U F1 F2 H m pq ⟶ innerObjects T U F1 F2 H m pq.1 :=
  coequalizer.desc (Sigma.desc fun i =>
    AssociatorFaces.Right.a0 T U F1 F2 H m pq.1 pq.2 i ≫
      AssociatorFaces.Right.innerProjection T U F1 F2 H m pq.1 i) (by
        apply Sigma.hom_ext
        intro ij
        simp only [relationLeftMap, relationRightMap, Sigma.ι_comp_desc_assoc,
          Category.assoc, Sigma.ι_comp_desc]
        simpa only [AssociatorFaces.Right.a0, Category.assoc] using
          AssociatorFaces.Right.outerFace0_innerProjection
            T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)

/-- Descend the complete outer action face using its proved compatibility with both inner faces. -/
abbrev outerFace1 (pq : (E × K) × (E × K)) :
    outerRelations T U F1 F2 H m pq ⟶ innerObjects T U F1 F2 H m pq.2 :=
  coequalizer.desc (Sigma.desc fun i =>
    AssociatorFaces.Right.a1 T U F1 F2 H m pq.1 pq.2 i ≫
      AssociatorFaces.Right.innerProjection T U F1 F2 H m pq.2 i) (by
        apply Sigma.hom_ext
        intro ij
        simp only [relationLeftMap, relationRightMap, Sigma.ι_comp_desc_assoc,
          Category.assoc, Sigma.ι_comp_desc]
        exact AssociatorFaces.Right.outerFace1_innerProjection
          T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)


/-- The actual inner projection of the full outer relation word. -/
abbrev relationProjection (pq : (E × K) × (E × K)) (i : C1 × C2) :
    relationObjects T U F1 F2 H m pq i ⟶ outerRelations T U F1 F2 H m pq :=
  Sigma.ι (relationObjects T U F1 F2 H m pq) i ≫
    coequalizer.π (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq)

/-- Tensor preservation identifies the actual relation quotient with the original outer relation. -/
@[no_expose]
def relationIso (pq : (E × K) × (E × K)) :
    outerRelations T U F1 F2 H m pq ≅
      (AssociatorFaces.Right.relationFunctor U H m pq.1 pq.2).obj
        (EnrichedDayKernel.obj T F1 F2 pq.1.2) := by
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso (EnrichedDayKernel.weight T pq.1.2)
    (F1.externalTensor F2) (AssociatorFaces.Right.relationFunctor U H m pq.1 pq.2)


omit [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p)]
  [∀ p : E × K, HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p)]
  [∀ p : E × K, HasCoequalizer
    (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
    (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p)] in
/-- The relation comparison preserves every original complete relation generator. -/
@[reassoc]
theorem relationProjection_iso (pq : (E × K) × (E × K)) (i : C1 × C2) :
    relationProjection T U F1 F2 H m pq i ≫ (relationIso T U F1 F2 H m pq).hom =
      (AssociatorFaces.Right.relationFunctor U H m pq.1 pq.2).map
        (EnrichedDayKernel.gen T F1 F2 pq.1.2 i) := by
  exact Enriched.weightedCoend.Mapped.mappedQuotientIso_generator
    (EnrichedDayKernel.weight T pq.1.2)
    (F1.externalTensor F2) (AssociatorFaces.Right.relationFunctor U H m pq.1 pq.2) i


variable [HasCoproduct (innerObjects T U F1 F2 H m)]
  [HasCoproduct (outerRelations T U F1 F2 H m)]

/-- The actual outer weight-face coproduct map after inner descent. -/
abbrev outerLeftMap : (∐ outerRelations T U F1 F2 H m) ⟶ ∐ innerObjects T U F1 F2 H m :=
  Sigma.desc fun pq => outerFace0 T U F1 F2 H m pq ≫
    Sigma.ι (innerObjects T U F1 F2 H m) pq.1

/-- The actual outer action-face coproduct map after inner descent. -/
abbrev outerRightMap : (∐ outerRelations T U F1 F2 H m) ⟶ ∐ innerObjects T U F1 F2 H m :=
  Sigma.desc fun pq => outerFace1 T U F1 F2 H m pq ≫
    Sigma.ι (innerObjects T U F1 F2 H m) pq.2

variable [HasCoequalizer (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)]

/-- The original coupled nested quotient. -/
abbrev nestedPoint : V :=
  coequalizer (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)

/-- Every actual nested generator retains its inner and outer projection legs. -/
abbrev nestedProjection (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.objects T U F1 F2 H m p i ⟶ nestedPoint T U F1 F2 H m :=
  AssociatorFaces.Right.innerProjection T U F1 F2 H m p i ≫
    Sigma.ι (innerObjects T U F1 F2 H m) p ≫
      coequalizer.π (outerLeftMap T U F1 F2 H m) (outerRightMap T U F1 F2 H m)

/-- The literal simultaneous original object family. -/
abbrev simultaneousObjects : (E × K) × (C1 × C2) → V := fun pi =>
  AssociatorFaces.Right.objects T U F1 F2 H m pi.1 pi.2

/-- The simultaneous relation family keeps the two complete original faces separately. -/
abbrev simultaneousRelations :
    Sum (((E × K) × (E × K)) × (C1 × C2))
      ((E × K) × ((C1 × C2) × (C1 × C2))) → V :=
  Sum.elim
    (fun pqi => AssociatorFaces.Right.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pij => AssociatorFaces.Right.innerRelations T U F1 F2 H m pij.1 pij.2)

variable [HasCoproduct (simultaneousObjects T U F1 F2 H m)]
  [HasCoproduct (simultaneousRelations T U F1 F2 H m)]

/-- The simultaneous weight-face map uses the original outer and inner weight faces. -/
abbrev simultaneousLeftMap :
    (∐ simultaneousRelations T U F1 F2 H m) ⟶ ∐ simultaneousObjects T U F1 F2 H m :=
  Sigma.desc (Sum.rec (motive := fun r =>
      simultaneousRelations T U F1 F2 H m r ⟶ ∐ simultaneousObjects T U F1 F2 H m)
    (fun pqi => AssociatorFaces.Right.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pqi.1.1, pqi.2))
    (fun pij => AssociatorFaces.Right.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pij.1, pij.2.1)))


/-- The simultaneous action-face map uses the original outer and inner action faces. -/
abbrev simultaneousRightMap :
    (∐ simultaneousRelations T U F1 F2 H m) ⟶ ∐ simultaneousObjects T U F1 F2 H m :=
  Sigma.desc (Sum.rec (motive := fun r =>
      simultaneousRelations T U F1 F2 H m r ⟶ ∐ simultaneousObjects T U F1 F2 H m)
    (fun pqi => AssociatorFaces.Right.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pqi.1.2, pqi.2))
    (fun pij => AssociatorFaces.Right.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2 ≫
      Sigma.ι (simultaneousObjects T U F1 F2 H m) (pij.1, pij.2.2)))


variable [HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
  (simultaneousRightMap T U F1 F2 H m)]

/-- The simultaneous quotient of the actual original Day relation families. -/
abbrev simultaneousPoint : V :=
  coequalizer (simultaneousLeftMap T U F1 F2 H m) (simultaneousRightMap T U F1 F2 H m)

/-- The actual two-variable original generator in the simultaneous quotient. -/
abbrev simultaneousProjection (p : E × K) (i : C1 × C2) :
    AssociatorFaces.Right.objects T U F1 F2 H m p i ⟶ simultaneousPoint T U F1 F2 H m :=
  Sigma.ι (simultaneousObjects T U F1 F2 H m) (p, i) ≫
    coequalizer.π (simultaneousLeftMap T U F1 F2 H m) (simultaneousRightMap T U F1 F2 H m)

/-- The original Fubini theorem compares these actual presentations using the proved full faces. -/
@[no_expose]
def fubiniIso : nestedPoint T U F1 F2 H m ≅ simultaneousPoint T U F1 F2 H m := by
  exact @Enriched.weightedCoend.fubiniIso V _ (E × K) (C1 × C2)
    (simultaneousObjects T U F1 F2 H m)
    (fun pij => AssociatorFaces.Right.innerRelations T U F1 F2 H m pij.1 pij.2)
    (fun pij => AssociatorFaces.Right.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pij => AssociatorFaces.Right.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pqi => AssociatorFaces.Right.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqij => AssociatorFaces.Right.mixedRelations T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2)
    (fun pqij => AssociatorFaces.Right.r0 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqij => AssociatorFaces.Right.r1 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqi => AssociatorFaces.Right.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqi => AssociatorFaces.Right.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (inferInstance : ∀ p : E × K,
      HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p))
    (inferInstance : ∀ p : E × K,
      HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p))
    (inferInstance : ∀ p : E × K, HasCoequalizer
      (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
      (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p))
    (inferInstance : ∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq))
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Right.outerFace0_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Right.outerFace1_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (inferInstance : HasCoproduct (outerRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (innerObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (outerLeftMap T U F1 F2 H m)
      (outerRightMap T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
      (simultaneousRightMap T U F1 F2 H m))
private theorem fubiniIso_generators_private (p : E × K) (i : C1 × C2) :
    (nestedProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).hom =
      simultaneousProjection T U F1 F2 H m p i) ∧
    (simultaneousProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).inv =
      nestedProjection T U F1 F2 H m p i) := by
  exact @Enriched.weightedCoend.fubiniIso_generators V _ (E × K) (C1 × C2)
    (simultaneousObjects T U F1 F2 H m)
    (fun pij => AssociatorFaces.Right.innerRelations T U F1 F2 H m pij.1 pij.2)
    (fun pij => AssociatorFaces.Right.b0 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pij => AssociatorFaces.Right.b1 T U F1 F2 H m pij.1 pij.2.1 pij.2.2)
    (fun pqi => AssociatorFaces.Right.outerRelations T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqij => AssociatorFaces.Right.mixedRelations T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2)
    (fun pqij => AssociatorFaces.Right.r0 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqij => AssociatorFaces.Right.r1 T U F1 F2 H m
      pqij.1.1 pqij.1.2 pqij.2.1 pqij.2.2)
    (fun pqi => AssociatorFaces.Right.a0 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (fun pqi => AssociatorFaces.Right.a1 T U F1 F2 H m pqi.1.1 pqi.1.2 pqi.2)
    (inferInstance : ∀ p : E × K,
      HasCoproduct (AssociatorFaces.Right.innerRelations T U F1 F2 H m p))
    (inferInstance : ∀ p : E × K,
      HasCoproduct (AssociatorFaces.Right.objects T U F1 F2 H m p))
    (inferInstance : ∀ p : E × K, HasCoequalizer
      (AssociatorFaces.Right.innerLeftMap T U F1 F2 H m p)
      (AssociatorFaces.Right.innerRightMap T U F1 F2 H m p))
    (inferInstance : ∀ pq, HasCoproduct (relationRelations T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoproduct (relationObjects T U F1 F2 H m pq))
    (inferInstance : ∀ pq, HasCoequalizer (relationLeftMap T U F1 F2 H m pq)
      (relationRightMap T U F1 F2 H m pq))
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Right.outerFace0_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (fun pq ij => by
      simpa only [Category.assoc] using AssociatorFaces.Right.outerFace1_innerProjection
        T U F1 F2 H m pq.1 pq.2 ij.1 ij.2)
    (inferInstance : HasCoproduct (outerRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (innerObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (outerLeftMap T U F1 F2 H m)
      (outerRightMap T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousRelations T U F1 F2 H m))
    (inferInstance : HasCoproduct (simultaneousObjects T U F1 F2 H m))
    (inferInstance : HasCoequalizer (simultaneousLeftMap T U F1 F2 H m)
      (simultaneousRightMap T U F1 F2 H m)) p i

/-- The forward Fubini map preserves both original nested generator legs. -/
@[reassoc]
theorem nestedProjection_fubini_hom (p : E × K) (i : C1 × C2) :
    nestedProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).hom =
      simultaneousProjection T U F1 F2 H m p i :=
  (fubiniIso_generators_private T U F1 F2 H m p i).1

/-- The inverse Fubini map restores both original nested generator legs. -/
@[reassoc]
theorem simultaneousProjection_fubini_inv (p : E × K) (i : C1 × C2) :
    simultaneousProjection T U F1 F2 H m p i ≫ (fubiniIso T U F1 F2 H m).inv =
      nestedProjection T U F1 F2 H m p i :=
  (fubiniIso_generators_private T U F1 F2 H m p i).2


end CategoryTheory.EnrichedDayKernel.AssociatorPresentation.Right
