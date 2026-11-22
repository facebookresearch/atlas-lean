/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFiniteKanProductWeakEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrown
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Actual replacement products and the original derived core comparison

The product comparison is the native product comparison of the same original
Smith replacement functor. Its legs are `R.map` of the original projections.
The unit square proves weakness for genuinely local-fibrant targets. Evaluation
and scalar internal Hom give the mapping comparison, with the original gamma
and independently chosen scalar conventions retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.CoreProducts

private theorem fibrantProductMapWeak {K : Type a} [Category.{b} K] [ModelCategory K]
    [HasFiniteProducts K] {A B C D : K} (f : A ⟶ B) (g : C ⟶ D)
    [IsFibrant A] [IsFibrant B] [IsFibrant C] [IsFibrant D]
    [WeakEquivalence f] [WeakEquivalence g] : WeakEquivalence (prod.map f g) := by
  have hIso : isomorphisms K ≤ weakEquivalences K := by
    intro X Y h hh
    let _ : IsIso h := hh
    exact mem_weakEquivalences h
  have hl : weakEquivalences K (prod.map f (𝟙 C)) :=
    Functor.map_mem_of_weakEquivalence_of_fibrant (prod.functor.flip.obj C)
      (weakEquivalences K) hIso (by
        intro X Y p _ _ hp
        have ht : trivialFibrations K (prod.map p (𝟙 C)) := by
          apply MorphismProperty.limMap
          rintro (_ | _)
          · exact hp
          · exact mem_trivialFibrations (𝟙 C)
        exact ht.2) f
  have hr : weakEquivalences K (prod.map (𝟙 B) g) :=
    Functor.map_mem_of_weakEquivalence_of_fibrant (prod.functor.obj B)
      (weakEquivalences K) hIso (by
        intro X Y p _ _ hp
        have ht : trivialFibrations K (prod.map (𝟙 B) p) := by
          apply MorphismProperty.limMap
          rintro (_ | _)
          · exact mem_trivialFibrations (𝟙 B)
          · exact hp
        exact ht.2) g
  have h : prod.map f (𝟙 C) ≫ prod.map (𝟙 B) g = prod.map f g := by
    rw [prod.map_map, Category.comp_id, Category.id_comp]
  exact (weakEquivalence_iff _).mpr
    (h ▸ (weakEquivalences K).comp_mem _ _ hl hr)

private theorem kanProductWeak {A B C D : SSet.{u}} (f : A ⟶ B) (g : C ⟶ D)
    [SSet.KanComplex A] [SSet.KanComplex B] [SSet.KanComplex C] [SSet.KanComplex D]
    (hf : SSet.realizationWeakEquivalences f) (hg : SSet.realizationWeakEquivalences g) :
    SSet.realizationWeakEquivalences (prod.map f g) := by
  have h := SSet.KanComplex.W.prodMap
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence f).mpr hf)
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence g).mpr hg)
  let _ : SSet.KanComplex (A ⨯ C) := h.kanComplex_source
  let _ : SSet.KanComplex (B ⨯ D) := h.kanComplex_target
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp h

private theorem scalarPostWeak (A : SSet.{u}) {Y Z : SSet.{u}} (g : Y ⟶ Z)
    (hg : SSet.realizationWeakEquivalences g) (hY : IsFibrant Y) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences ((ihom A).map g) := by
  let _ : IsFibrant Y := hY
  let _ : IsFibrant Z := hZ
  let _ : WeakEquivalence g := (weakEquivalence_iff _).mpr hg
  let _ : (ihom.adjunction A).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant A
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := ihom.adjunction A) g)

private theorem scalarHomFibrant (A Y : SSet.{u}) (hY : IsFibrant Y) :
    IsFibrant ((ihom A).obj Y) := by
  let _ : (ihom.adjunction A).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant A
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := ihom.adjunction A) hY

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- Original local-fibrant targets have a genuine local-fibrant native product. -/
theorem product_localFibrant (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : isOriginalLocalFibrant S (C ⨯ E) := by
  let q := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  let _ : IsFibrant C := (q.isFibrant_iff C).mpr hC
  let _ : IsFibrant E := (q.isFibrant_iff E).mpr hE
  have h : IsFibrant (C ⨯ E) := isFibrant_of_fibration (prod.snd : C ⨯ E ⟶ E)
  exact (q.isFibrant_iff _).mp h

/-- The native terminal target is local-fibrant for the same original Smith model. -/
theorem terminal_localFibrant (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    isOriginalLocalFibrant S (⊤_ (SimplicialPresheaf.{u} D)) := by
  let q := originalLocalSmithData S
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  have h : IsFibrant (⊤_ (SimplicialPresheaf.{u} D)) :=
    (isFibrant_iff_of_isTerminal (𝟙 (⊤_ (SimplicialPresheaf.{u} D))) terminalIsTerminal).mpr
      inferInstance
  exact (q.isFibrant_iff _).mp h

/-- The actual original replacement comparison uses R of the two original projections. -/
def rComparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (C E : SimplicialPresheaf.{u} D) :
    (localR S).obj (C ⨯ E) ⟶ (localR S).obj C ⨯ (localR S).obj E :=
  prodComparison (localR S) C E

/-- The first replacement comparison leg is the same original R map. -/
@[reassoc]
theorem rComparison_fst (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) :
    rComparison S C E ≫ prod.fst = (localR S).map (prod.fst : C ⨯ E ⟶ C) :=
  prodComparison_fst _ _ _

/-- The second replacement comparison leg retains the other original R map. -/
@[reassoc]
theorem rComparison_snd (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) :
    rComparison S C E ≫ prod.snd = (localR S).map (prod.snd : C ⨯ E ⟶ E) :=
  prodComparison_snd _ _ _

/-- The unit square relates the actual product replacement to the two actual factor replacements. -/
theorem rComparison_unit (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) :
    (localRUnit S).app (C ⨯ E) ≫ rComparison S C E =
      prod.map ((localRUnit S).app C) ((localRUnit S).app E) := by
  apply prod.hom_ext
  · rw [Category.assoc, rComparison_fst, prod.map_fst]
    exact ((localRUnit S).naturality (prod.fst : C ⨯ E ⟶ C)).symm
  · rw [Category.assoc, rComparison_snd, prod.map_snd]
    exact ((localRUnit S).naturality (prod.snd : C ⨯ E ⟶ E)).symm

/-- Both-variable naturality keeps every original projection and replacement map. -/
theorem rComparison_naturality (S : I → Arrow (SimplicialPresheaf.{u} D))
    {C E C' E' : SimplicialPresheaf.{u} D} (f : C ⟶ C') (g : E ⟶ E') :
    (localR S).map (prod.map f g) ≫ rComparison S C' E' =
      rComparison S C E ≫ prod.map ((localR S).map f) ((localR S).map g) :=
  prodComparison_natural _ f g

/-- Product preservation up to weakness is derived from fibrancy and the actual unit square. -/
theorem rComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : originalLocalEquivalences S (rComparison S C E) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  let _ : IsFibrant C := hC.1
  let _ : IsFibrant E := hE.1
  let _ : IsFibrant ((localR S).obj C) := (localR_isOriginalLocalFibrant S C).1
  let _ : IsFibrant ((localR S).obj E) := (localR_isOriginalLocalFibrant S E).1
  let _ : WeakEquivalence ((localRUnit S).app C) := (weakEquivalence_iff _).mpr
    ((originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S _ hC
      (localR_isOriginalLocalFibrant S C)).mp (localRUnit_localTrivialCofibration S C).2)
  let _ : WeakEquivalence ((localRUnit S).app E) := (weakEquivalence_iff _).mpr
    ((originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S _ hE
      (localR_isOriginalLocalFibrant S E)).mp (localRUnit_localTrivialCofibration S E).2)
  let _ : WeakEquivalence ((localRUnit S).app (C ⨯ E)) := (weakEquivalence_iff _).mpr
    ((originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S _
      (product_localFibrant S C E hC hE) (localR_isOriginalLocalFibrant S (C ⨯ E))).mp
        (localRUnit_localTrivialCofibration S (C ⨯ E)).2)
  let _ : WeakEquivalence (prod.map ((localRUnit S).app C) ((localRUnit S).app E)) :=
    fibrantProductMapWeak (A := C) (B := (localR S).obj C)
      (C := E) (D := (localR S).obj E) ((localRUnit S).app C) ((localRUnit S).app E)
  have h : WeakEquivalence (rComparison S C E) :=
    weakEquivalence_of_precomp_of_fac (rComparison_unit S C E)
  exact weakEquivalences_le_originalLocalEquivalences S _ ((weakEquivalence_iff _).mp h)

/-- Local Whitehead supplies the same objectwise weakness at every original coefficient. -/
theorem rComparison_objectwiseWeak (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : objectwiseKanWeakEquivalences D (rComparison S C E) :=
  (originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S _
    (localR_isOriginalLocalFibrant S (C ⨯ E))
    (product_localFibrant S _ _ (localR_isOriginalLocalFibrant S C)
      (localR_isOriginalLocalFibrant S E))).mp (rComparison_weak S C E hC hE)

/-- The actual terminal replacement comparison is the native map to the original terminal. -/
def rTerminal (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localR S).obj (⊤_ (SimplicialPresheaf.{u} D)) ⟶ ⊤_ (SimplicialPresheaf.{u} D) :=
  terminal.from _

/-- The chosen R unit at the terminal has the identity as its composite. -/
theorem rTerminal_unit (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (localRUnit S).app (⊤_ (SimplicialPresheaf.{u} D)) ≫ rTerminal S = 𝟙 _ :=
  terminal.hom_ext _ _

/-- The terminal replacement comparison is weak, without identifying R with the identity. -/
theorem rTerminal_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    originalLocalEquivalences S (rTerminal S) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := (data D).model
  let _ : WeakEquivalence ((localRUnit S).app (⊤_ (SimplicialPresheaf.{u} D))) :=
    (weakEquivalence_iff _).mpr
      ((originalLocalEquivalence_iff_weakEquivalence_of_localFibrant S _
        (terminal_localFibrant S) (localR_isOriginalLocalFibrant S _)).mp
          (localRUnit_localTrivialCofibration S _).2)
  have h : WeakEquivalence (rTerminal S) := weakEquivalence_of_precomp_of_fac (rTerminal_unit S)
  exact weakEquivalences_le_originalLocalEquivalences S _ ((weakEquivalence_iff _).mp h)

/-- The scalar replacement comparison evaluates the actual R maps of the original projections. -/
def coreComparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) :
    (TransferredCoreReplacements.rReplacement S z).obj (C ⨯ E) ⟶
      (TransferredCoreReplacements.rReplacement S z).obj C ⨯
        (TransferredCoreReplacements.rReplacement S z).obj E :=
  prodComparison (TransferredCoreReplacements.rReplacement S z) C E

/-- Evaluation of the actual R comparison is followed by the native product evaluation Iso. -/
theorem coreComparison_factorization (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) :
    coreComparison S z C E = (rComparison S C E).app (op z) ≫
      (PreservesLimitPair.iso (ConstantEvaluation.evaluation z) ((localR S).obj C)
        ((localR S).obj E)).hom :=
  prodComparison_comp (localR S) (ConstantEvaluation.evaluation z)

/-- The scalar R/core comparison is weak for genuine local-fibrant targets. -/
theorem coreComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : SSet.realizationWeakEquivalences (coreComparison S z C E) := by
  let e := PreservesLimitPair.iso (ConstantEvaluation.evaluation z) ((localR S).obj C)
    ((localR S).obj E)
  have he : SSet.realizationWeakEquivalences e.hom := by
    let _ : IsIso e.hom := e.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have h := SSet.realizationWeakEquivalences.comp_mem _ _
    (rComparison_objectwiseWeak S C E hC hE (op z)) he
  exact (coreComparison_factorization S z C E).symm ▸ h

/-- The core/unit product square keeps the original evaluated units and original core product Iso. -/
theorem coreComparison_unit (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) :
    (TransferredCoreReplacements.rUnit S z).app (C ⨯ E) ≫ coreComparison S z C E =
      (PreservesLimitPair.iso (ConstantEvaluation.evaluation z) C E).hom ≫
        prod.map ((TransferredCoreReplacements.rUnit S z).app C)
          ((TransferredCoreReplacements.rUnit S z).app E) :=
  prodComparison_natural_of_natTrans (TransferredCoreReplacements.rUnit S z)

/-- The first evaluated replacement leg is the same R projection at the original site object. -/
@[reassoc]
theorem coreComparison_fst (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) :
    coreComparison S z C E ≫ prod.fst = ((localR S).map (prod.fst : C ⨯ E ⟶ C)).app (op z) :=
  prodComparison_fst _ _ _

/-- The second evaluated replacement leg retains the other original R projection. -/
@[reassoc]
theorem coreComparison_snd (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (C E : SimplicialPresheaf.{u} D) :
    coreComparison S z C E ≫ prod.snd = ((localR S).map (prod.snd : C ⨯ E ⟶ E)).app (op z) :=
  prodComparison_snd _ _ _

/-- The evaluated replacement comparison is natural in both original target maps. -/
theorem coreComparison_naturality (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    {C E C' E' : SimplicialPresheaf.{u} D} (f : C ⟶ C') (g : E ⟶ E') :
    ((localR S).map (prod.map f g)).app (op z) ≫ coreComparison S z C' E' =
      coreComparison S z C E ≫
        prod.map (((localR S).map f).app (op z)) (((localR S).map g).app (op z)) :=
  prodComparison_natural (TransferredCoreReplacements.rReplacement S z) f g

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem mappingProductWeak (T : SimplicialPresheaf.{u} D ⥤ SSet.{u})
    (A : SSet.{u}) (C E : SimplicialPresheaf.{u} D)
    (hC : IsFibrant (T.obj C)) (hE : IsFibrant (T.obj E))
    (hP : IsFibrant (T.obj (C ⨯ E)))
    (hc : SSet.realizationWeakEquivalences (prodComparison T C E)) :
    SSet.realizationWeakEquivalences (prodComparison (T ⋙ ihom A) C E) := by
  let _ : SSet.KanComplex (T.obj C) := hC
  let _ : SSet.KanComplex (T.obj E) := hE
  have hCE : IsFibrant (T.obj C ⨯ T.obj E) := SSet.KanComplex.prod_kanComplex _ _
  let e := PreservesLimitPair.iso (ihom A) (T.obj C) (T.obj E)
  have he : SSet.realizationWeakEquivalences e.hom := by
    let _ : IsIso e.hom := e.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have h := SSet.realizationWeakEquivalences.comp_mem _ _
    (scalarPostWeak A _ hc hP hCE) he
  exact (prodComparison_comp (A := C) (B := E) T (ihom A)).symm ▸ h

/-- The scalar derived mapping comparison uses precisely the transferred original Q and R. -/
def mappingComparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) :
    TransferredCoreReplacements.mappingModel S z K (C ⨯ E) ⟶
      TransferredCoreReplacements.mappingModel S z K C ⨯
        TransferredCoreReplacements.mappingModel S z K E :=
  prodComparison ((TransferredCoreReplacements.rReplacement S z) ⋙
    ihom ((TransferredCoreReplacements.qReplacement S z).obj K)) C E

/-- The first scalar mapping comparison is postcomposition by the actual R projection. -/
@[reassoc]
theorem mappingComparison_fst (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    mappingComparison S z K C E ≫ prod.fst =
      (ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
        (((localR S).map (prod.fst : C ⨯ E ⟶ C)).app (op z)) :=
  prodComparison_fst _ _ _

/-- The second scalar mapping comparison is the other literal R projection map. -/
@[reassoc]
theorem mappingComparison_snd (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    mappingComparison S z K C E ≫ prod.snd =
      (ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
        (((localR S).map (prod.snd : C ⨯ E ⟶ E)).app (op z)) :=
  prodComparison_snd _ _ _

/-- The native scalar Hom product Iso follows the actual evaluated replacement comparison. -/
theorem mappingComparison_factorization (S : I → Arrow (SimplicialPresheaf.{u} D))
    (z : D) (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    mappingComparison S z K C E =
      (ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
        (coreComparison S z C E) ≫
      (PreservesLimitPair.iso (ihom ((TransferredCoreReplacements.qReplacement S z).obj K))
        ((TransferredCoreReplacements.rReplacement S z).obj C)
        ((TransferredCoreReplacements.rReplacement S z).obj E)).hom :=
  prodComparison_comp _ _

/-- Genuine local fibrancy proves the scalar derived mapping product comparison weak. -/
theorem mappingComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) (hE : isOriginalLocalFibrant S E) :
    SSet.realizationWeakEquivalences (mappingComparison S z K C E) :=
  mappingProductWeak (TransferredCoreReplacements.rReplacement S z)
    ((TransferredCoreReplacements.qReplacement S z).obj K) C E
    (TransferredCoreReplacements.rReplacement_isKan S hz C)
    (TransferredCoreReplacements.rReplacement_isKan S hz E)
    (TransferredCoreReplacements.rReplacement_isKan S hz (C ⨯ E))
    (coreComparison_weak S z C E hC hE)

/-- Scalar-source naturality keeps the same transferred Q map and every target factor. -/
theorem mappingComparison_source (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    {K L : SSet.{u}} (k : K ⟶ L) (C E : SimplicialPresheaf.{u} D) :
    (pre ((TransferredCoreReplacements.qReplacement S z).map k)).app
        ((TransferredCoreReplacements.rReplacement S z).obj (C ⨯ E)) ≫
        mappingComparison S z K C E =
      mappingComparison S z L C E ≫ prod.map
        ((pre ((TransferredCoreReplacements.qReplacement S z).map k)).app
          ((TransferredCoreReplacements.rReplacement S z).obj C))
        ((pre ((TransferredCoreReplacements.qReplacement S z).map k)).app
          ((TransferredCoreReplacements.rReplacement S z).obj E)) :=
  prodComparison_natural_of_natTrans
    ((ScalarCoreReplacementSpans.transferredMapping S z).map k.op)

/-- Target naturality is the same original R map on both target variables. -/
theorem mappingComparison_target (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) {C E C' E' : SimplicialPresheaf.{u} D} (f : C ⟶ C') (g : E ⟶ E') :
    (ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
        (((localR S).map (prod.map f g)).app (op z)) ≫ mappingComparison S z K C' E' =
      mappingComparison S z K C E ≫ prod.map
        ((ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
          (((localR S).map f).app (op z)))
        ((ihom ((TransferredCoreReplacements.qReplacement S z).obj K)).map
          (((localR S).map g).app (op z))) :=
  prodComparison_natural (TransferredCoreReplacements.rReplacement S z ⋙
    ihom ((TransferredCoreReplacements.qReplacement S z).obj K)) f g

/-- The original end projection is a natural transformation into its actual transferred scalar model. -/
def gammaTransformation (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u}) :
    (localDerivedEnd S).obj (op (ConstantEvaluation.constant.obj K)) ⟶
      TransferredCoreReplacements.rReplacement S z ⋙
        ihom ((TransferredCoreReplacements.qReplacement S z).obj K) where
  app C := DerivedZeroProjection.gamma S z K C
  naturality _ _ f := DerivedZeroProjection.gamma_target S z K f

/-- The literal gamma square commutes with the original product maps and scalar comparison. -/
theorem gamma_product (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) :
    DerivedZeroProjection.gamma S z K (C ⨯ E) ≫ mappingComparison S z K C E =
      prodComparison ((localDerivedEnd S).obj (op (ConstantEvaluation.constant.obj K))) C E ≫
        prod.map (DerivedZeroProjection.gamma S z K C) (DerivedZeroProjection.gamma S z K E) :=
  prodComparison_natural_of_natTrans (gammaTransformation S z K)

/-- The actual groupoidal-source derived product comparison uses the original chosen end action. -/
def derivedComparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) :
    ((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj (C ⨯ E) ⟶
      ((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj C ⨯
        ((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj E :=
  prodComparison ((CoreUniversalMapping.groupoidalMapping S).obj (op K)) C E

/-- The genuine original core comparison, including its baseline unit, has the same product square. -/
theorem derivedComparison_gamma (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    BaselineConstantCoreComparison.comparison S z K (C ⨯ E) ≫ mappingComparison S z K C E =
      derivedComparison S K C E ≫ prod.map
        (BaselineConstantCoreComparison.comparison S z K C)
        (BaselineConstantCoreComparison.comparison S z K E) :=
  prodComparison_natural_of_natTrans ((CoreUniversalMapping.baselineComparison S z).app (op K))

/-- The actual original derived comparison is weak by its commuting gamma square. -/
theorem derivedComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D)
    (hC : isOriginalLocalFibrant S C) (hE : isOriginalLocalFibrant S E) :
    SSet.realizationWeakEquivalences (derivedComparison S K C E) := by
  let A := (BaselineConstantCoreComparison.constantReplacement (D := D)).obj K
  let _ : SSet.KanComplex (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj C) :=
    localDerivedEnd_isKan S A C
  let _ : SSet.KanComplex (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj E) :=
    localDerivedEnd_isKan S A E
  let _ : SSet.KanComplex (TransferredCoreReplacements.mappingModel S z K C) :=
    scalarHomFibrant _ _ (TransferredCoreReplacements.rReplacement_isKan S hz C)
  let _ : SSet.KanComplex (TransferredCoreReplacements.mappingModel S z K E) :=
    scalarHomFibrant _ _ (TransferredCoreReplacements.rReplacement_isKan S hz E)
  have hp := kanProductWeak
    (A := ((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj C)
    (B := TransferredCoreReplacements.mappingModel S z K C)
    (C := ((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj E)
    (D := TransferredCoreReplacements.mappingModel S z K E)
    (BaselineConstantCoreComparison.comparison S z K C)
    (BaselineConstantCoreComparison.comparison S z K E)
    (BaselineConstantCoreComparison.comparison_weak S hz K C)
    (BaselineConstantCoreComparison.comparison_weak S hz K E)
  apply SSet.realizationWeakEquivalences.of_postcomp _ _ hp
  have h := SSet.realizationWeakEquivalences.comp_mem _ _
    (BaselineConstantCoreComparison.comparison_weak S hz K (C ⨯ E))
    (mappingComparison_weak S hz K C E hC hE)
  exact derivedComparison_gamma S z K C E ▸ h

/-- The original derived source map acts contravariantly on the same product comparison. -/
theorem derivedComparison_source (S : I → Arrow (SimplicialPresheaf.{u} D))
    {K L : SSet.{u}} (k : K ⟶ L) (C E : SimplicialPresheaf.{u} D) :
    localDerivedPrecomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k)
        (C ⨯ E) ≫ derivedComparison S K C E =
      derivedComparison S L C E ≫ prod.map
        (localDerivedPrecomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) C)
        (localDerivedPrecomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).map k) E) :=
  prodComparison_natural_of_natTrans ((CoreUniversalMapping.groupoidalMapping S).map k.op)

/-- The original derived target map acts covariantly on both target factors. -/
theorem derivedComparison_target (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    {C E C' E' : SimplicialPresheaf.{u} D} (f : C ⟶ C') (g : E ⟶ E') :
    localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K)
        (prod.map f g) ≫ derivedComparison S K C' E' =
      derivedComparison S K C E ≫ prod.map
        (localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) f)
        (localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K) g) :=
  prodComparison_natural _ f g

/-- Independently fixed scalar R uses its actual maps of the original zero-core projections. -/
def fixedCoreComparison (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (C E : SimplicialPresheaf.{u} D) :
    e.R.obj ((C ⨯ E).obj (op z)) ⟶ e.R.obj (C.obj (op z)) ⨯ e.R.obj (E.obj (op z)) :=
  prodComparison (ScalarCoreReplacementSpans.fixedTarget z e) C E

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The independent scalar units retain the same original core product Iso. -/
theorem fixedCoreComparison_unit (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (C E : SimplicialPresheaf.{u} D) :
    e.r.app ((C ⨯ E).obj (op z)) ≫ fixedCoreComparison z e C E =
      (PreservesLimitPair.iso (ConstantEvaluation.evaluation z) C E).hom ≫
        prod.map (e.r.app (C.obj (op z))) (e.r.app (E.obj (op z))) :=
  prodComparison_natural_of_natTrans (ScalarCoreReplacementSpans.fixedUnit z e)

/-- The independent scalar replacement product comparison is weak on actual Kan cores. -/
theorem fixedCoreComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : SSet.realizationWeakEquivalences (fixedCoreComparison z e C E) := by
  let _ : SSet.KanComplex (C.obj (op z)) := ConstantEvaluation.evaluation_isFibrant S hz C hC
  let _ : SSet.KanComplex (E.obj (op z)) := ConstantEvaluation.evaluation_isFibrant S hz E hE
  let _ : SSet.KanComplex (e.R.obj (C.obj (op z))) := e.R_isFibrant _
  let _ : SSet.KanComplex (e.R.obj (E.obj (op z))) := e.R_isFibrant _
  have hp := kanProductWeak (A := C.obj (op z)) (B := e.R.obj (C.obj (op z)))
    (C := E.obj (op z)) (D := e.R.obj (E.obj (op z)))
    (e.r.app (C.obj (op z))) (e.r.app (E.obj (op z)))
    (e.r_trivialCofibration _).2 (e.r_trivialCofibration _).2
  let b := PreservesLimitPair.iso (ConstantEvaluation.evaluation z) C E
  have hb : SSet.realizationWeakEquivalences b.hom := by
    let _ : IsIso b.hom := b.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have hu : SSet.realizationWeakEquivalences (e.r.app ((C ⨯ E).obj (op z))) :=
    (e.r_trivialCofibration _).2
  apply SSet.realizationWeakEquivalences.of_precomp _ _ hu
  exact (fixedCoreComparison_unit z e C E).symm ▸
    SSet.realizationWeakEquivalences.comp_mem _ _ hb hp

/-- The independently fixed scalar derived mapping comparison retains both actual factor functors. -/
def fixedMappingComparison (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    (ihom (e.Q.obj K)).obj (e.R.obj ((C ⨯ E).obj (op z))) ⟶
      (ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z))) ⨯
        (ihom (e.Q.obj K)).obj (e.R.obj (E.obj (op z))) :=
  prodComparison (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K)) C E

/-- The fixed scalar mapping comparison is weak by the actual replacement comparison and SM7. -/
theorem fixedMappingComparison_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E) : SSet.realizationWeakEquivalences (fixedMappingComparison z e K C E) :=
  mappingProductWeak (ScalarCoreReplacementSpans.fixedTarget z e) (e.Q.obj K) C E
    (e.R_isFibrant _) (e.R_isFibrant _) (e.R_isFibrant _)
    (fixedCoreComparison_weak S hz e C E hC hE)

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The fixed scalar comparison retains its first original core projection. -/
@[reassoc]
theorem fixedMappingComparison_fst (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    fixedMappingComparison z e K C E ≫ prod.fst =
      (ihom (e.Q.obj K)).map (e.R.map ((prod.fst : C ⨯ E ⟶ C).app (op z))) :=
  prodComparison_fst _ _ _

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The fixed scalar comparison retains its second original core projection. -/
@[reassoc]
theorem fixedMappingComparison_snd (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D) :
    fixedMappingComparison z e K C E ≫ prod.snd =
      (ihom (e.Q.obj K)).map (e.R.map ((prod.snd : C ⨯ E ⟶ E).app (op z))) :=
  prodComparison_snd _ _ _

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The independent Q functor gives source naturality of the fixed mapping comparison. -/
theorem fixedMappingComparison_source (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    {K L : SSet.{u}} (k : K ⟶ L) (C E : SimplicialPresheaf.{u} D) :
    (pre (e.Q.map k)).app (e.R.obj ((C ⨯ E).obj (op z))) ≫ fixedMappingComparison z e K C E =
      fixedMappingComparison z e L C E ≫ prod.map
        ((pre (e.Q.map k)).app (e.R.obj (C.obj (op z))))
        ((pre (e.Q.map k)).app (e.R.obj (E.obj (op z)))) :=
  prodComparison_natural_of_natTrans ((ScalarCoreReplacementSpans.fixedMapping z e).map k.op)

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- Both independent scalar target maps are the same R maps of the original core maps. -/
theorem fixedMappingComparison_target (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) {C E C' E' : SimplicialPresheaf.{u} D} (f : C ⟶ C') (g : E ⟶ E') :
    (ihom (e.Q.obj K)).map (e.R.map ((prod.map f g).app (op z))) ≫
        fixedMappingComparison z e K C' E' =
      fixedMappingComparison z e K C E ≫ prod.map
        ((ihom (e.Q.obj K)).map (e.R.map (f.app (op z))))
        ((ihom (e.Q.obj K)).map (e.R.map (g.app (op z)))) :=
  prodComparison_natural (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K)) f g

/-- The actual original derived product map keeps its first original target projection. -/
@[reassoc]
theorem derivedComparison_fst (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) :
    derivedComparison S K C E ≫ prod.fst =
      localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K)
        (prod.fst : C ⨯ E ⟶ C) :=
  prodComparison_fst _ _ _

/-- The second actual original derived projection is the other original target action. -/
@[reassoc]
theorem derivedComparison_snd (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) :
    derivedComparison S K C E ≫ prod.snd =
      localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K)
        (prod.snd : C ⨯ E ⟶ E) :=
  prodComparison_snd _ _ _

omit [Small.{u} D] [LocallySmall.{u} D] in
private def terminalEvaluationIso (z : D) :
    (⊤_ (SimplicialPresheaf.{u} D)).obj (op z) ≅ ⊤_ SSet.{u} := by
  let T : SimplicialPresheaf.{u} D := (Functor.const Dᵒᵖ).obj (⊤_ SSet.{u})
  let ht : IsTerminal T := Functor.isTerminal (fun _ => terminalIsTerminal)
  exact (ConstantEvaluation.evaluation z).mapIso (terminalIsTerminal.uniqueUpToIso ht)

private theorem terminalCoreWeak (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    SSet.realizationWeakEquivalences
      (terminalComparison (TransferredCoreReplacements.rReplacement S z)) := by
  have hw := (originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S (rTerminal S)
    (localR_isOriginalLocalFibrant S _) (terminal_localFibrant S)).mp (rTerminal_weak S)
  let e := terminalEvaluationIso.{u} z
  have he : SSet.realizationWeakEquivalences e.hom := by
    let _ : IsIso e.hom := e.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have hc : (rTerminal S).app (op z) ≫ e.hom =
      terminalComparison (TransferredCoreReplacements.rReplacement S z) := terminal.hom_ext _ _
  exact hc ▸ SSet.realizationWeakEquivalences.comp_mem _ _ (hw (op z)) he

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem mappingTerminalWeak (T : SimplicialPresheaf.{u} D ⥤ SSet.{u})
    (A : SSet.{u}) (hT : IsFibrant (T.obj (⊤_ (SimplicialPresheaf.{u} D))))
    (ht : SSet.realizationWeakEquivalences (terminalComparison T)) :
    SSet.realizationWeakEquivalences (terminalComparison (T ⋙ ihom A)) := by
  have hterm : IsFibrant (⊤_ SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (⊤_ SSet.{u})) terminalIsTerminal).mpr inferInstance
  let e := PreservesTerminal.iso (ihom A)
  have he : SSet.realizationWeakEquivalences e.hom := by
    let _ : IsIso e.hom := e.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have hc : (ihom A).map (terminalComparison T) ≫ e.hom =
      terminalComparison (T ⋙ ihom A) := terminal.hom_ext _ _
  exact hc ▸ SSet.realizationWeakEquivalences.comp_mem _ _
    (scalarPostWeak A _ ht hT hterm) he

/-- The actual transferred scalar mapping comparison has a weak terminal map. -/
theorem mappingTerminal_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) :
    SSet.realizationWeakEquivalences (terminalComparison
      (TransferredCoreReplacements.rReplacement S z ⋙
        ihom ((TransferredCoreReplacements.qReplacement S z).obj K))) :=
  mappingTerminalWeak _ _ (TransferredCoreReplacements.rReplacement_isKan S hz _)
    (terminalCoreWeak S z)

/-- The actual original derived mapping space of the terminal has its weak terminal comparison. -/
theorem derivedTerminal_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (K : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (terminalComparison ((CoreUniversalMapping.groupoidalMapping S).obj (op K))) := by
  let p := BaselineConstantCoreComparison.comparison S z K (⊤_ (SimplicialPresheaf.{u} D))
  let t := terminalComparison (TransferredCoreReplacements.rReplacement S z ⋙
    ihom ((TransferredCoreReplacements.qReplacement S z).obj K))
  have h : p ≫ t = terminalComparison ((CoreUniversalMapping.groupoidalMapping S).obj (op K)) :=
    terminal.hom_ext _ _
  exact h ▸ SSet.realizationWeakEquivalences.comp_mem _ _
    (BaselineConstantCoreComparison.comparison_weak S hz K _) (mappingTerminal_weak S hz K)

/-- The original product comparison induces its literal pair of component projections. -/
def originalComponentPair (S : I → Arrow (SimplicialPresheaf.{u} D)) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D)
    (c : SSet.π₀ (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj (C ⨯ E))) :
    SSet.π₀ (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj C) ×
      SSet.π₀ (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj E) :=
  (SSet.mapπ₀ prod.fst (SSet.mapπ₀ (derivedComparison S K C E) c),
    SSet.mapπ₀ prod.snd (SSet.mapπ₀ (derivedComparison S K C E) c))

/-- The fixed scalar product comparison induces the corresponding literal component pair. -/
def fixedComponentPair (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C E : SimplicialPresheaf.{u} D)
    (c : SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj ((C ⨯ E).obj (op z))))) :
    SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (C.obj (op z)))) ×
      SSet.π₀ ((ihom (e.Q.obj K)).obj (e.R.obj (E.obj (op z)))) :=
  (SSet.mapπ₀ prod.fst (SSet.mapπ₀ (fixedMappingComparison z e K C E) c),
    SSet.mapπ₀ prod.snd (SSet.mapπ₀ (fixedMappingComparison z e K C E) c))

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem componentProjectionFst (F : SimplicialPresheaf.{u} D ⥤ SSet.{u})
    (C E : SimplicialPresheaf.{u} D) (c : SSet.π₀ (F.obj (C ⨯ E))) :
    SSet.mapπ₀ prod.fst (SSet.mapπ₀ (prodComparison F C E) c) =
      SSet.mapπ₀ (F.map (prod.fst : C ⨯ E ⟶ C)) c :=
  (SSet.mapπ₀_comp_apply (prodComparison F C E) prod.fst c).symm.trans
    (congrArg (fun f => SSet.mapπ₀ f c) (prodComparison_fst F C E))

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem componentProjectionSnd (F : SimplicialPresheaf.{u} D ⥤ SSet.{u})
    (C E : SimplicialPresheaf.{u} D) (c : SSet.π₀ (F.obj (C ⨯ E))) :
    SSet.mapπ₀ prod.snd (SSet.mapπ₀ (prodComparison F C E) c) =
      SSet.mapπ₀ (F.map (prod.snd : C ⨯ E ⟶ E)) c :=
  (SSet.mapπ₀_comp_apply (prodComparison F C E) prod.snd c).symm.trans
    (congrArg (fun f => SSet.mapπ₀ f c) (prodComparison_snd F C E))

/-- The genuine derived core component bijections commute with both original product projections. -/
theorem universalComponentPair_commutes (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C E : SimplicialPresheaf.{u} D) (hC : isOriginalLocalFibrant S C)
    (hE : isOriginalLocalFibrant S E)
    (c : SSet.π₀ (((CoreUniversalMapping.groupoidalMapping S).obj (op K)).obj (C ⨯ E))) :
    Prod.map (CoreMappingComponents.universalHomEquiv S hz e K C hC)
        (CoreMappingComponents.universalHomEquiv S hz e K E hE) (originalComponentPair S K C E c) =
      fixedComponentPair z e K C E
        (CoreMappingComponents.universalHomEquiv S hz e K (C ⨯ E)
          (product_localFibrant S C E hC hE) c) := by
  let G := (CoreUniversalMapping.groupoidalMapping S).obj (op K)
  let H := ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K)
  let u := CoreMappingComponents.universalHomEquiv S hz e K (C ⨯ E)
    (product_localFibrant S C E hC hE) c
  apply Prod.ext
  · change CoreMappingComponents.universalHomEquiv S hz e K C hC
        (SSet.mapπ₀ prod.fst (SSet.mapπ₀ (prodComparison G C E) c)) =
      SSet.mapπ₀ prod.fst (SSet.mapπ₀ (prodComparison H C E) u)
    exact (congrArg (CoreMappingComponents.universalHomEquiv S hz e K C hC)
      (componentProjectionFst G C E c)).trans
      ((CoreMappingComponents.universalHomEquiv_target S hz e K
        (product_localFibrant S C E hC hE) hC (prod.fst : C ⨯ E ⟶ C) c).trans
        (componentProjectionFst H C E u).symm)
  · change CoreMappingComponents.universalHomEquiv S hz e K E hE
        (SSet.mapπ₀ prod.snd (SSet.mapπ₀ (prodComparison G C E) c)) =
      SSet.mapπ₀ prod.snd (SSet.mapπ₀ (prodComparison H C E) u)
    exact (congrArg (CoreMappingComponents.universalHomEquiv S hz e K E hE)
      (componentProjectionSnd G C E c)).trans
      ((CoreMappingComponents.universalHomEquiv_target S hz e K
        (product_localFibrant S C E hC hE) hE (prod.snd : C ⨯ E ⟶ E) c).trans
        (componentProjectionSnd H C E u).symm)

/-- The native product is packaged with its proved actual local-fibrant predicate. -/
def productTarget (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : CoreUniversalMapping.LocalTargets S) : CoreUniversalMapping.LocalTargets S :=
  ⟨C.obj ⨯ E.obj, product_localFibrant S C.obj E.obj C.property E.property⟩

/-- The first map from the packaged product is the same original projection. -/
def productTargetFst (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : CoreUniversalMapping.LocalTargets S) : productTarget S C E ⟶ C :=
  ObjectProperty.homMk prod.fst

/-- The second packaged map retains the other original projection. -/
def productTargetSnd (S : I → Arrow (SimplicialPresheaf.{u} D))
    (C E : CoreUniversalMapping.LocalTargets S) : productTarget S C E ⟶ E :=
  ObjectProperty.homMk prod.snd

/-- The genuine localized mapping Iso commutes with the first original core product projection. -/
theorem mappingIso_product_fst (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C E : CoreUniversalMapping.LocalTargets S) :
    ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app (productTarget S C E) ≫
        SSet.realizationWeakEquivalences.Q.map
          ((ihom (e.Q.obj K)).map (e.R.map ((prod.fst : C.obj ⨯ E.obj ⟶ C.obj).app (op z)))) =
      SSet.realizationWeakEquivalences.Q.map
        (localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K)
          (prod.fst : C.obj ⨯ E.obj ⟶ C.obj)) ≫
        ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app C :=
  (((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).naturality
    (productTargetFst S C E)).symm

/-- The localized mapping Iso retains the second original core product projection as well. -/
theorem mappingIso_product_snd (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C E : CoreUniversalMapping.LocalTargets S) :
    ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app (productTarget S C E) ≫
        SSet.realizationWeakEquivalences.Q.map
          ((ihom (e.Q.obj K)).map (e.R.map ((prod.snd : C.obj ⨯ E.obj ⟶ E.obj).app (op z)))) =
      SSet.realizationWeakEquivalences.Q.map
        (localDerivedPostcomp S ((BaselineConstantCoreComparison.constantReplacement (D := D)).obj K)
          (prod.snd : C.obj ⨯ E.obj ⟶ E.obj)) ≫
        ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app E :=
  (((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).naturality
    (productTargetSnd S C E)).symm

/-- Package the genuine original terminal as an actual local-fibrant target. -/
def terminalTarget (S : I → Arrow (SimplicialPresheaf.{u} D)) : CoreUniversalMapping.LocalTargets S :=
  ⟨⊤_ (SimplicialPresheaf.{u} D), terminal_localFibrant S⟩

omit [Small.{u} D] [LocallySmall.{u} D] in
private theorem fixedCoreTerminalWeak (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.realizationWeakEquivalences (terminalComparison (ScalarCoreReplacementSpans.fixedTarget z e)) := by
  let b := terminalEvaluationIso.{u} z
  have hb : SSet.realizationWeakEquivalences b.hom := by
    let _ : IsIso b.hom := b.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso _
  have hu : SSet.realizationWeakEquivalences
      (e.r.app ((⊤_ (SimplicialPresheaf.{u} D)).obj (op z))) := (e.r_trivialCofibration _).2
  have h : e.r.app ((⊤_ (SimplicialPresheaf.{u} D)).obj (op z)) ≫
      terminalComparison (ScalarCoreReplacementSpans.fixedTarget z e) = b.hom := terminal.hom_ext _ _
  exact SSet.realizationWeakEquivalences.of_precomp _ _ hu (h.symm ▸ hb)

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The fixed scalar presentation of maps into the terminal has its actual weak terminal map. -/
theorem fixedMappingTerminal_weak (z : D) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) : SSet.realizationWeakEquivalences
      (terminalComparison (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K))) :=
  mappingTerminalWeak _ _ (e.R_isFibrant _) (fixedCoreTerminalWeak z e)

/-- The genuine mapping Iso commutes with the two actual maps to the scalar terminal value. -/
theorem mappingIso_terminal (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u}) :
    ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app (terminalTarget S) ≫
        SSet.realizationWeakEquivalences.Q.map
          (terminalComparison (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K))) =
      SSet.realizationWeakEquivalences.Q.map
        (terminalComparison ((CoreUniversalMapping.groupoidalMapping S).obj (op K))) := by
  let Q := SSet.realizationWeakEquivalences.Q
  let φ := ((CoreUniversalMapping.mappingIso S hz e).hom.app (op K)).app (terminalTarget S)
  let a := ((CoreUniversalMapping.toCommon S z e).app (op K)).app
    (⊤_ (SimplicialPresheaf.{u} D))
  let b := ((ScalarCoreReplacementSpans.fixedToCommon S z e).app (op K)).app
    (⊤_ (SimplicialPresheaf.{u} D))
  let t := terminal.from (((ScalarCoreReplacementSpans.commonMapping S z e).obj (op K)).obj
    (⊤_ (SimplicialPresheaf.{u} D)))
  have htri : φ ≫ Q.map b = Q.map a :=
    congrArg (fun θ => (θ.app (op K)).app (terminalTarget S))
      (CoreUniversalProperty.mappingIso_triangle S hz e)
  have hb : b ≫ t = terminalComparison
      (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K)) := terminal.hom_ext _ _
  have ha : a ≫ t = terminalComparison ((CoreUniversalMapping.groupoidalMapping S).obj (op K)) :=
    terminal.hom_ext _ _
  change φ ≫ Q.map (terminalComparison
    (ScalarCoreReplacementSpans.fixedTarget z e ⋙ ihom (e.Q.obj K))) = _
  exact (congrArg (fun f => φ ≫ Q.map f) hb.symm).trans
    ((congrArg (fun f => φ ≫ f) (Q.map_comp b t)).trans
      ((Category.assoc φ (Q.map b) (Q.map t)).symm.trans
        ((congrArg (fun f => f ≫ Q.map t) htri).trans
          ((Q.map_comp a t).symm.trans (Q.congr_map ha)))))

end SimplicialPresheaf.CoreProducts
