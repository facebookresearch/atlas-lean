/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.ModuleMappingR
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedMaps
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ClosedGraded
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingTriple

/-!
# Complete original generator balancing for Mapping_R

The action condition on the right-translation end is equivalent to equality
on every full Day generator. Each generator retains both original source
indices and its whole output Hom object. Currying proves detection on the
entire parameter tensor; no unit separator or restriction to parameter points
is used. Source components are the literal original right action followed by
the right-translation family component.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.Enriched.ModuleMappingR

open EnrichedFunctorCat EnrichedDayKernel

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] SphereModuleMappingEnd.moduleCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every whole parameter tensor is detected by the complete original Day coend generators. -/
theorem tensor_hom_ext (M : Module d S L) (k : I) {P Z : V}
    {f g : (sourceTensor d S L M).toEnrichedFunctor.obj k ⊗ P ⟶ Z}
    (h : ∀ p : I × I,
      (EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ▷ P) ≫ f =
      (EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ▷ P) ≫ g) : f = g := by
  apply (cancel_epi (β_ P ((sourceTensor d S L M).toEnrichedFunctor.obj k)).hom).1
  apply MonoidalClosed.curry_injective
  apply EnrichedDayKernel.hom_ext d.tensorEnrichedFunctor
    (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k
  intro p
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  exact (braiding_naturality_right_assoc P
    (EnrichedDayKernel.gen d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p) f).trans
    ((congrArg
      (fun z => (β_ P (EnrichedDayKernel.objects d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p)).hom ≫ z)
      (h p)).trans
      (braiding_naturality_right_assoc P
        (EnrichedDayKernel.gen d.tensorEnrichedFunctor
          (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p) g).symm)

/-- The whole original ambient end map of a genuine parameterized right-translation family. -/
abbrev ambientFamily (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    P ⟶ (ambient d S L M N).toEnrichedFunctor.obj c :=
  GradingConvention.endFromPositive (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
    (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor t

/-- The complete source-action component at each original output index. -/
def sourceFamilyComponent (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (k : I) : P ⟶
      (ihom ((sourceTensor d S L M).toEnrichedFunctor.obj k)).obj
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (k ⊗ c)) :=
  ambientFamily d S L M N c t ≫ component (sourceActionMap d S L M N) c ≫
    Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N) c k

/-- The complete target-action component at the same original output index. -/
def targetFamilyComponent (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (k : I) : P ⟶
      (ihom ((sourceTensor d S L M).toEnrichedFunctor.obj k)).obj
        ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (k ⊗ c)) :=
  ambientFamily d S L M N c t ≫ component (targetActionMap d b S L M N) c ≫
    Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N) c k

/-- Every full source-action generator retains its whole Hom weight and both input indices. -/
def balanceLeft (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (k : I) (p : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ⊗ P ⟶
        (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (k ⊗ c) :=
  (EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ▷ P) ≫
      MonoidalClosed.uncurry (sourceFamilyComponent d S L M N c t k)

/-- Every full target-action generator retains exactly the same original source tensor. -/
def balanceRight (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (k : I) (p : I × I) :
    EnrichedDayKernel.objects d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ⊗ P ⟶
        (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (k ⊗ c) :=
  (EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ▷ P) ≫
      MonoidalClosed.uncurry (targetFamilyComponent d b S L M N c t k)

/-- The original whole action equalizer condition is exactly full original generator balance. -/
theorem condition_iff_balance (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor) :
    (ambientFamily d S L M N c t ≫ component (sourceActionMap d S L M N) c =
      ambientFamily d S L M N c t ≫ component (targetActionMap d b S L M N) c) ↔
    (∀ k p, balanceLeft d S L M N c t k p = balanceRight d b S L M N c t k p) := by
  constructor
  · intro h k p
    simpa only [balanceLeft, balanceRight, sourceFamilyComponent,
      targetFamilyComponent, Category.assoc] using congrArg
      (fun z => (EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ▷ P) ≫
          MonoidalClosed.uncurry
            (z ≫ Closed.π d (sourceTensor d S L M)
              (SphereModuleMappingEnd.diagram d S L N) c k)) h
  · intro h
    apply Closed.hom_ext d (sourceTensor d S L M)
      (SphereModuleMappingEnd.diagram d S L N) c
    intro k
    apply MonoidalClosed.uncurry_injective
    apply tensor_hom_ext d S L M k
    intro p
    simpa only [balanceLeft, balanceRight, sourceFamilyComponent,
      targetFamilyComponent, Category.assoc] using h k p

/-- A genuine family with all original weighted generator balances is a complete Mapping_R
family. -/
def familyOfBalance (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (h : ∀ k p, balanceLeft d S L M N c t k p = balanceRight d b S L M N c t k p) :
    Family d b S L M N c P where
  transformation := t
  condition := (condition_iff_balance d b S L M N c t).2 h

/-- Every constructed complete Mapping_R family satisfies every original full weighted balance. -/
theorem Family.balance {M N : Module d S L} {c : I} {P : V}
    (q : Family d b S L M N c P) (k : I) (p : I × I) :
    balanceLeft d S L M N c q.transformation k p =
      balanceRight d b S L M N c q.transformation k p :=
  (condition_iff_balance d b S L M N c q.transformation).1 q.condition k p

omit [SymmetricCategory I] in
/-- The full source action arrow retains its original source-action precomposition projection. -/
@[reassoc]
theorem sourceActionMap_component_π (M N : Module d S L) (c k : I) :
    component (sourceActionMap d S L M N) c ≫
        Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N) c k =
      Closed.π d (SphereModuleMappingEnd.diagram d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c k ≫
        (MonoidalClosed.pre (component (SphereModuleMappingEnd.action d S L M) k)).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj (k ⊗ c)) := by
  let := ColimitMonoidal.monoidalCategory d
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  dsimp only [sourceActionMap, RightModuleMappingEnd.sourceActionMap,
    SphereModuleMappingEnd.action, SphereModuleMappingEnd.diagram]
  exact Closed.closedPre_π d (SphereModuleMappingEnd.action d S L M)
    (SphereModuleMappingEnd.diagram d S L N) c k

omit [SymmetricCategory I] in
/-- Every full source balance component is the original entire weighted right action followed
by the unchanged right-translation family component. -/
theorem balanceLeft_eq (M N : Module d S L) (c : I) {P : V}
    (t : GradedNatTrans ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c).toEnrichedFunctor)
    (k : I) (p : I × I) :
    balanceLeft d S L M N c t k p =
      ((EnrichedDayKernel.gen d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S k p ≫
        component (SphereModuleMappingEnd.action d S L M) k) ▷ P) ≫
        MonoidalClosed.uncurry (t.app k) := by
  rw [balanceLeft, sourceFamilyComponent, sourceActionMap_component_π]
  have hp : ambientFamily d S L M N c t ≫
      Closed.π d (SphereModuleMappingEnd.diagram d S L M)
        (SphereModuleMappingEnd.diagram d S L N) c k = t.app k :=
    GradingConvention.endFromPositive_symmetric_π _ _ _ k
  rw [← Category.assoc, hp,
    MonoidalClosed.uncurry_pre_app, ← comp_whiskerRight_assoc]

/-- The complete original coefficient block swap, with its unchanged α/β factors. -/
def coefficientSwap (A B C : V) : (A ⊗ B) ⊗ C ⟶ (A ⊗ C) ⊗ B :=
  (α_ A B C).hom ≫ (A ◁ (β_ B C).hom) ≫ (α_ A C B).inv

/-- The whole original Day reassociation, inner braid and inverse reassociation. -/
def parameterSwapComponent (F G H : EnrichedFunctor V I V) (k : I) :
    EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G)
        H k ⟶
      EnrichedDayKernel.obj d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F H)
        G k :=
  (AssociatorConstruction.componentIso d F G H k).hom ≫
    Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
      (BraidingFunctor.functorIso d b G H).hom k ≫
    (AssociatorConstruction.componentIso d F H G k).inv

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every complete triple generator retains the literal κ index map and the whole coefficient
block swap. Its output Hom weight is never reduced to an identity point. -/
@[reassoc]
theorem parameterSwapComponent_generator (F G H : EnrichedFunctor V I V) (k j a c : I) :
    BraidingTriple.leftAt d F G H k j a c ≫ parameterSwapComponent d b F G H k =
      (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
        coefficientSwap (F.obj j) (G.obj a) (H.obj c)) ≫
        BraidingTriple.leftAt d F H G k j c a := by
  let g₀ := BraidingTriple.leftAt d F G H k j a c
  let g₁ := BraidingTriple.rightAt d F G H k j a c
  let g₂ := BraidingTriple.rightAt d F H G k j c a
  let g₃ := BraidingTriple.leftAt d F H G k j c a
  let p := (AssociatorConstruction.componentIso d F G H k).hom
  let q := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F)
    (BraidingFunctor.functorIso d b G H).hom k
  let r := (AssociatorConstruction.componentIso d F H G k).inv
  let w₁ := eHomWhiskerRight V (α_ j a c).inv k
  let w₂ := eHomWhiskerRight V (j ◁ (β_ a c).inv) k
  let w₃ := eHomWhiskerRight V (α_ j c a).hom k
  let v₁ := (α_ (F.obj j) (G.obj a) (H.obj c)).hom
  let v₂ := 𝟙 (F.obj j) ⊗ₘ (β_ (G.obj a) (H.obj c)).hom
  let v₃ := (α_ (F.obj j) (H.obj c) (G.obj a)).inv
  have h₁ : g₀ ≫ p = (w₁ ⊗ₘ v₁) ≫ g₁ :=
    (Category.assoc (AssociatorFlat.leftGenerator d F G H k ((j, a), c))
      (AssociatorFlattening.flatToNested d F G H k) p).trans
      (AssociatorConstruction.tripleGenerator_hom d F G H k ((j, a), c))
  have h₂ : g₁ ≫ q = (w₂ ⊗ₘ v₂) ≫ g₂ :=
    BraidingTriple.inner_right d b F G H k j a c
  have h₃ : g₂ ≫ r = (w₃ ⊗ₘ v₃) ≫ g₃ :=
    (Category.assoc (AssociatorFlat.rightGenerator d F H G k ((j, c), a))
      (AssociatorRightFlattening.flatToNested d F H G k) r).trans
      (AssociatorConstruction.tripleGenerator_inv d F H G k ((j, c), a))
  have hw : w₁ ≫ w₂ ≫ w₃ = eHomWhiskerRight V (translationSwap j a c) k := by
    dsimp only [w₁, w₂, w₃, translationSwap]
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding a c,
      eHomWhiskerRight_comp, eHomWhiskerRight_comp]
    exact (Category.assoc _ _ _).symm
  have hv : v₁ ≫ v₂ ≫ v₃ = coefficientSwap (F.obj j) (G.obj a) (H.obj c) := by
    simp only [v₁, v₂, v₃, coefficientSwap, id_tensorHom]
  have ht : (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ (w₃ ⊗ₘ v₃) =
      (w₁ ≫ w₂ ≫ w₃) ⊗ₘ (v₁ ≫ v₂ ≫ v₃) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  change g₀ ≫ p ≫ q ≫ r =
    (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
      coefficientSwap (F.obj j) (G.obj a) (H.obj c)) ≫ g₃
  calc
    _ = (w₁ ⊗ₘ v₁) ≫ g₁ ≫ q ≫ r := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ q ≫ r) h₁
    _ = (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ g₂ ≫ r := by
      simpa only [Category.assoc] using congrArg (fun t => (w₁ ⊗ₘ v₁) ≫ t ≫ r) h₂
    _ = (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ (w₃ ⊗ₘ v₃) ≫ g₃ :=
      congrArg (fun t => (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ t) h₃
    _ = ((w₁ ≫ w₂ ≫ w₃) ⊗ₘ (v₁ ≫ v₂ ≫ v₃)) ≫ g₃ := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ g₃) ht
    _ = _ := congrArg₂ (fun w v => (w ⊗ₘ v) ≫ g₃) hw hv

/-- The actual selected Day block swap on the whole original tensor diagrams. -/
def parameterSwap (F G H : EnrichedFunctorCat V I) :
    Closed.tensorObject d (Closed.tensorObject d F G) H ⟶
      Closed.tensorObject d (Closed.tensorObject d F H) G := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  exact (α_ F G H).hom ≫ (F ◁ (β_ G H).hom) ≫ (α_ F H G).inv

omit [HasProducts.{uI} V] [HasEqualizers V] in
/-- The actual selected Day block swap retains the complete original component construction. -/
theorem parameterSwap_component (F G H : EnrichedFunctorCat V I) (k : I) :
    component (parameterSwap d b F G H) k =
      parameterSwapComponent d b F.toEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor k := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  have h₁ : component (α_ F G H).hom k =
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor G.toEnrichedFunctor
        H.toEnrichedFunctor k).hom :=
    (congrArg (fun e => component e.hom k) (ColimitMonoidal.associator_eq d F G H)).trans
      (AssociatorConstruction.functorIso_hom_component d F.toEnrichedFunctor
        G.toEnrichedFunctor H.toEnrichedFunctor k)
  have h₃ : component (α_ F H G).inv k =
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor H.toEnrichedFunctor
        G.toEnrichedFunctor k).inv :=
    (congrArg (fun e => component e.inv k) (ColimitMonoidal.associator_eq d F H G)).trans
      (AssociatorConstruction.functorIso_inv_component d F.toEnrichedFunctor
        H.toEnrichedFunctor G.toEnrichedFunctor k)
  have h₂ : component (F ◁ (β_ G H).hom) k =
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId F.toEnrichedFunctor)
        (BraidingFunctor.functorIso d b G.toEnrichedFunctor H.toEnrichedFunctor).hom k := by
    rw [← id_tensorHom, ColimitMonoidal.tensorHom_eq]
    exact Input.bifunctor_map_component d.tensorEnrichedFunctor (𝟙 F) (β_ G H).hom k
  change component ((α_ F G H).hom ≫ (F ◁ (β_ G H).hom) ≫ (α_ F H G).inv) k = _
  rw [component_comp, component_comp]
  exact congrArg₂ (fun p q => p ≫ q) h₁ (congrArg₂ (fun p q => p ≫ q) h₂ h₃)

omit [SymmetricCategory I] in
/-- The constructed closed-class evaluation is the actual original Day descent. -/
theorem selectedEvaluation_eq (F Y : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    letI := Closed.monoidalClosed d
    (ihom.ev F).app Y = Closed.evaluation d F Y := by
  let := ColimitMonoidal.monoidalCategory d
  let := Closed.monoidalClosed d
  change (Closed.adjunction d F).counit.app Y = _
  exact Closed.adjunction_counit_app d F Y

/-- The original target-action descent swaps the parameter and coefficient blocks,
evaluates the original end, and applies the unchanged right action of N. -/
def targetDescent (M N : Module d S L) :
    Closed.tensorObject d (sourceTensor d S L M) (ambient d S L M N) ⟶
      SphereModuleMappingEnd.diagram d S L N := by
  letI := ColimitMonoidal.monoidalCategory d
  exact parameterSwap d b (SphereModuleMappingEnd.diagram d S L M) ⟨S⟩
      (ambient d S L M N) ≫
    (Closed.evaluation d (SphereModuleMappingEnd.diagram d S L M)
      (SphereModuleMappingEnd.diagram d S L N) ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫
    SphereModuleMappingEnd.action d S L N

/-- The unchanged closed-class descent of the original complete target parallel arrow. -/
def selectedTargetDescent (M N : Module d S L) :
    Closed.tensorObject d (sourceTensor d S L M) (ambient d S L M N) ⟶
      SphereModuleMappingEnd.diagram d S L N := by
  letI := ColimitMonoidal.monoidalCategory d
  letI := BraidingMonoidal.symmetricCategory d b
  letI := Closed.monoidalClosed d
  let F := SphereModuleMappingEnd.diagram d S L M
  let Y := SphereModuleMappingEnd.diagram d S L N
  let H := ambient d S L M N
  exact ((β_ F (⟨S⟩ : EnrichedFunctorCat V I)).hom ▷ H) ≫
    (α_ (⟨S⟩ : EnrichedFunctorCat V I) F H).hom ≫
    ((⟨S⟩ : EnrichedFunctorCat V I) ◁ (ihom.ev F).app Y) ≫
    (β_ (⟨S⟩ : EnrichedFunctorCat V I) Y).hom ≫ SphereModuleMappingEnd.action d S L N

/-- The entire original target descent equals the actual coefficient-swap evaluation descent. -/
theorem selectedTargetDescent_eq (M N : Module d S L) :
    selectedTargetDescent d b S L M N = targetDescent d b S L M N := by
  have coherence {C : Type (max (max uI uV) vV)} [Category.{max vV uI} C]
      [MonoidalCategory C] [SymmetricCategory C]
      (F R H Y Z : C) (ev : F ⊗ H ⟶ Y) (g : Y ⊗ R ⟶ Z) :
      ((β_ F R).hom ▷ H) ≫ (α_ R F H).hom ≫ (R ◁ ev) ≫ (β_ R Y).hom ≫ g =
        (α_ F R H).hom ≫ (F ◁ (β_ R H).hom) ≫ (α_ F H R).inv ≫ (ev ▷ R) ≫ g := by
    rw [braiding_naturality_right_assoc R ev g, braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry, id_whiskerRight,
      Category.id_comp]
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let F := SphereModuleMappingEnd.diagram d S L M
  let Y := SphereModuleMappingEnd.diagram d S L N
  let H := ambient d S L M N
  have he : (ihom.ev F).app Y = Closed.evaluation d F Y := selectedEvaluation_eq d F Y
  have hc := @coherence (EnrichedFunctorCat V I)
    (inferInstance : Category.{max vV uI} (EnrichedFunctorCat V I))
    (ColimitMonoidal.monoidalCategory d) (BraidingMonoidal.symmetricCategory d b)
    F (⟨S⟩ : EnrichedFunctorCat V I) H Y Y
    (Closed.evaluation d F Y) (SphereModuleMappingEnd.action d S L N)
  simpa only [selectedTargetDescent, targetDescent, parameterSwap, F, Y, H, Category.assoc] using
    (congrArg (fun ev => ((β_ F (⟨S⟩ : EnrichedFunctorCat V I)).hom ▷ H) ≫
    (α_ (⟨S⟩ : EnrichedFunctorCat V I) F H).hom ≫
    ((⟨S⟩ : EnrichedFunctorCat V I) ◁ ev) ≫
    (β_ (⟨S⟩ : EnrichedFunctorCat V I) Y).hom ≫
    SphereModuleMappingEnd.action d S L N) he).trans hc

/-- The original complete target parallel arrow is exactly the transpose of this original
coefficient swap, evaluation and right-action descent. -/
theorem targetActionMap_eq_transpose (M N : Module d S L) :
    targetActionMap d b S L M N =
      Closed.transpose d (sourceTensor d S L M) (ambient d S L M N)
        (SphereModuleMappingEnd.diagram d S L N) (targetDescent d b S L M N) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  let := Closed.monoidalClosed d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  have hc : targetActionMap d b S L M N =
      MonoidalClosed.curry (selectedTargetDescent d b S L M N) := rfl
  have ht : MonoidalClosed.curry (targetDescent d b S L M N) =
      Closed.transpose d (sourceTensor d S L M) (ambient d S L M N)
        (SphereModuleMappingEnd.diagram d S L N) (targetDescent d b S L M N) :=
    Closed.adjunction_homEquiv d (sourceTensor d S L M) (ambient d S L M N)
      (SphereModuleMappingEnd.diagram d S L N) (targetDescent d b S L M N)
  exact hc.trans ((congrArg MonoidalClosed.curry
    (selectedTargetDescent_eq d b S L M N)).trans ht)

omit [SymmetricCategory I] [HasProducts.{uI} V] [HasEqualizers V] in
/-- Every full triple weight evaluates its original inner Day point before the unchanged
outer target right action. No generator weight or parameter is discarded. -/
theorem evaluatedTriple_action (F G : EnrichedFunctorCat V I) (N : Module d S L)
    (f : Closed.tensorObject d F G ⟶ SphereModuleMappingEnd.diagram d S L N)
    (k j c a : I) :
    BraidingTriple.leftAt d F.toEnrichedFunctor G.toEnrichedFunctor S k j c a ≫
        Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k =
      (𝟙 (((j ⊗ c) ⊗ a) ⟶[V] k) ⊗ₘ
        (((Generators.point d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor
            (j, c) ≫ component f (j ⊗ c)) ▷ S.obj a) ≫
          ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
            (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a)) ≫
        ActionFromTransformation.targetAction
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor ((j ⊗ c) ⊗ a) k := by
  let W : V := ((j ⊗ c) ⊗ a) ⟶[V] k
  let C := S.obj a
  let u := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor
    F.toEnrichedFunctor G.toEnrichedFunctor (j, c)
  let v := component f (j ⊗ c)
  let outerGenerator := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F.toEnrichedFunctor G.toEnrichedFunctor) S k
    (j ⊗ c, a)
  let targetGenerator := EnrichedDayKernel.gen d.tensorEnrichedFunctor
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor S k (j ⊗ c, a)
  let actionAt := ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
    (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a
  let z := ActionFromTransformation.targetAction
    (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor ((j ⊗ c) ⊗ a) k
  have hf : BraidingTriple.leftAt d F.toEnrichedFunctor G.toEnrichedFunctor S k j c a =
      (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ outerGenerator :=
    AssociatorFlattening.leftGenerator_flatToNested d F.toEnrichedFunctor
      G.toEnrichedFunctor S k ((j, c), a)
  have hm : outerGenerator ≫
      Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) k =
      (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ targetGenerator := by
    have h := Input.gen_mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) k
      (j ⊗ c, a)
    rw [GradedNatTrans.unitId_component] at h
    exact h
  have hn : targetGenerator ≫ component (SphereModuleMappingEnd.action d S L N) k =
      (𝟙 W ⊗ₘ actionAt) ≫ z :=
    ExternalRightModule.gen_action d S (SphereModuleMappingEnd.diagram d S L N)
      (SphereModuleMappingEnd.action d S L N) k (j ⊗ c) a
  have hp : u ≫ v = Generators.point d.tensorEnrichedFunctor
      F.toEnrichedFunctor G.toEnrichedFunctor (j, c) ≫ component f (j ⊗ c) :=
    congrArg (fun t => t ≫ v) (Category.assoc _ _ _)
  have hc : (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) =
      𝟙 W ⊗ₘ ((u ≫ v) ▷ C) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      Category.id_comp, tensorHom_id]
  have hs : (𝟙 W ⊗ₘ ((u ≫ v) ▷ C)) ≫ (𝟙 W ⊗ₘ actionAt) =
      𝟙 W ⊗ₘ (((u ≫ v) ▷ C) ≫ actionAt) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  calc
    _ = (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ outerGenerator ≫
        Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫
        Input.mapAt d.tensorEnrichedFunctor f (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k) hf
    _ = (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 W ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ targetGenerator ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
      simpa only [Category.assoc] using congrArg (fun t =>
        (𝟙 W ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ t ≫ component (SphereModuleMappingEnd.action d S L N) k) hm
    _ = (𝟙 W ⊗ₘ ((u ≫ v) ▷ C)) ≫ targetGenerator ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ targetGenerator ≫
        component (SphereModuleMappingEnd.action d S L N) k) hc
    _ = (𝟙 W ⊗ₘ ((u ≫ v) ▷ C)) ≫ (𝟙 W ⊗ₘ actionAt) ≫ z :=
      congrArg (fun t => (𝟙 W ⊗ₘ ((u ≫ v) ▷ C)) ≫ t) hn
    _ = (𝟙 W ⊗ₘ (((u ≫ v) ▷ C) ≫ actionAt)) ≫ z := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ z) hs
    _ = _ := congrArg (fun t => (𝟙 W ⊗ₘ ((t ▷ C) ≫ actionAt)) ≫ z) hp

/-- The full original target descent keeps every output Hom weight, literal κ and original
target right action after evaluating the unchanged right-translation end projection. -/
theorem targetDescent_generator (M N : Module d S L) (k j a c : I) :
    BraidingTriple.leftAt d (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S
        (ambient d S L M N).toEnrichedFunctor k j a c ≫
        component (targetDescent d b S L M N) k =
      (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
        coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
          (S.obj a) ((ambient d S L M N).toEnrichedFunctor.obj c)) ≫
      (𝟙 (((j ⊗ c) ⊗ a) ⟶[V] k) ⊗ₘ
        ((MonoidalClosed.uncurry
            (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
              (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
          ExternalRightModule.sigma d S (SphereModuleMappingEnd.diagram d S L N)
            (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a)) ≫
        ActionFromTransformation.targetAction
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor ((j ⊗ c) ⊗ a) k := by
  let := ColimitMonoidal.monoidalCategory d
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let ev := Closed.evaluation d F Y
  have ht : component (ev ▷ (⟨S⟩ : EnrichedFunctorCat V I)) k =
      Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k := by
    rw [← tensorHom_id, ColimitMonoidal.tensorHom_eq]
    exact Input.bifunctor_map_component d.tensorEnrichedFunctor ev
      (𝟙 (⟨S⟩ : EnrichedFunctorCat V I)) k
  have hd : component (targetDescent d b S L M N) k =
      parameterSwapComponent d b F.toEnrichedFunctor S H.toEnrichedFunctor k ≫
        Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
    change component (parameterSwap d b F (⟨S⟩ : EnrichedFunctorCat V I) H ≫
      (ev ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ SphereModuleMappingEnd.action d S L N) k = _
    rw [component_comp, component_comp]
    exact congrArg₂ (fun p q => p ≫ q)
      (parameterSwap_component d b F (⟨S⟩ : EnrichedFunctorCat V I) H k)
      (congrArg (fun p => p ≫ component (SphereModuleMappingEnd.action d S L N) k) ht)
  have he := evaluatedTriple_action d S L F H N ev k j c a
  have hp := Closed.evaluation_point d F Y j c
  calc
    _ = BraidingTriple.leftAt d F.toEnrichedFunctor S H.toEnrichedFunctor k j a c ≫
        parameterSwapComponent d b F.toEnrichedFunctor S H.toEnrichedFunctor k ≫
        Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k := congrArg (fun x =>
          BraidingTriple.leftAt d F.toEnrichedFunctor S H.toEnrichedFunctor k j a c ≫ x) hd
    _ = (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
        coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c)) ≫
        BraidingTriple.leftAt d F.toEnrichedFunctor H.toEnrichedFunctor S k j c a ≫
        Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
        component (SphereModuleMappingEnd.action d S L N) k := by
      simpa only [BraidingTriple.leftAt, Category.assoc] using
        parameterSwapComponent_generator_assoc d b F.toEnrichedFunctor S
        H.toEnrichedFunctor k j a c
        (Input.mapAt d.tensorEnrichedFunctor ev (GradedNatTrans.unitId S) k ≫
          component (SphereModuleMappingEnd.action d S L N) k)
    _ = _ := (congrArg (fun x =>
      (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
        coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c)) ≫ x)
      he).trans (congrArg (fun x =>
        (eHomWhiskerRight V (translationSwap j a c) k ⊗ₘ
          coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c)) ≫
          (𝟙 (((j ⊗ c) ⊗ a) ⟶[V] k) ⊗ₘ ((x ▷ S.obj a) ≫
            ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N)
              (j ⊗ c) a)) ≫
          ActionFromTransformation.targetAction Y.toEnrichedFunctor ((j ⊗ c) ⊗ a) k) hp)

/-- The literal index block swap is the composite of the original associators and inner braid. -/
def translationSwapIso (j a c : I) : (j ⊗ c) ⊗ a ≅ (j ⊗ a) ⊗ c :=
  (α_ j c a) ≪≫ (whiskerLeftIso j (β_ c a)) ≪≫ (α_ j a c).symm

/-- Its forward arrow is exactly the original translated-action index map. -/
@[simp]
theorem translationSwapIso_hom (j a c : I) :
    (translationSwapIso j a c).hom = translationSwap j a c := rfl

/-- Every whole target generator applies the original translated target action σ_N followed
by N(κ). The full output Hom object and all three ordered coefficient blocks are retained. -/
@[reassoc]
theorem targetDescent_generator_translated (M N : Module d S L) (k j a c : I) :
    BraidingTriple.leftAt d (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S
        (ambient d S L M N).toEnrichedFunctor k j a c ≫
        component (targetDescent d b S L M N) k =
      (𝟙 (((j ⊗ a) ⊗ c) ⟶[V] k) ⊗ₘ
        (coefficientSwap ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.obj j)
            (S.obj a) ((ambient d S L M N).toEnrichedFunctor.obj c) ≫
          (MonoidalClosed.uncurry
            (Closed.π d (SphereModuleMappingEnd.diagram d S L M)
              (SphereModuleMappingEnd.diagram d S L N) c j) ▷ S.obj a) ≫
          translatedAction d S L N c j a)) ≫
        ActionFromTransformation.targetAction
          (SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor ((j ⊗ a) ⊗ c) k := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let H := ambient d S L M N
  let Y := SphereModuleMappingEnd.diagram d S L N
  let e := translationSwapIso j a c
  let W : V := ((j ⊗ c) ⊗ a) ⟶[V] k
  let W' : V := ((j ⊗ a) ⊗ c) ⟶[V] k
  let q := coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c)
  let u := (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
    ExternalRightModule.sigma d S Y (SphereModuleMappingEnd.action d S L N) (j ⊗ c) a
  let p := eHomWhiskerRight V e.hom k
  let z := ActionFromTransformation.targetAction Y.toEnrichedFunctor ((j ⊗ c) ⊗ a) k
  let z' := ActionFromTransformation.targetAction Y.toEnrichedFunctor ((j ⊗ a) ⊗ c) k
  have hg : BraidingTriple.leftAt d F.toEnrichedFunctor S H.toEnrichedFunctor k j a c ≫
      component (targetDescent d b S L M N) k = (p ⊗ₘ q) ≫ (𝟙 W ⊗ₘ u) ≫ z :=
    targetDescent_generator d b S L M N k j a c
  have ht : (p ⊗ₘ q) ≫ (𝟙 W ⊗ₘ u) = p ⊗ₘ (q ≫ u) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have hh : p ≫ eHomWhiskerRight V e.inv k = 𝟙 W' :=
    (eHomWhiskerRightIso V I e (Y := k)).hom_inv_id
  have hn : (p ⊗ₘ (q ≫ u)) ≫ z =
      (𝟙 W' ⊗ₘ ((q ≫ u) ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map e.hom)) ≫ z' := by
    have h := LaxMonoid.targetAction_sourceIso Y.toEnrichedFunctor e k (q ≫ u) p
    exact h.trans (congrArg (fun w =>
      (w ⊗ₘ ((q ≫ u) ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map e.hom)) ≫ z') hh)
  have hu : (q ≫ u) ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map e.hom =
      coefficientSwap (F.toEnrichedFunctor.obj j) (S.obj a) (H.toEnrichedFunctor.obj c) ≫
        (MonoidalClosed.uncurry (Closed.π d F Y c j) ▷ S.obj a) ≫
        translatedAction d S L N c j a := by
    simp only [q, u, e, translationSwapIso_hom, translatedAction, F, Y, Category.assoc]
  exact hg.trans (((Category.assoc (p ⊗ₘ q) (𝟙 W ⊗ₘ u) z).symm.trans
    (congrArg (fun v => v ≫ z) ht)).trans
      (hn.trans (congrArg (fun v => (𝟙 W' ⊗ₘ v) ≫ z') hu)))

omit [SymmetricCategory I] in
/-- The original action-target end represents every whole parameterized binary source
transformation by the actual Day/Kan graded universal property. -/
def actionPairEquiv (M N : Module d S L) (c : I) (P : V) :
    (P ⟶ (actionTarget d S L M N).toEnrichedFunctor.obj c) ≃
      GradedNatTrans ((Center.ofBraided V).obj P)
        ((SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor.externalTensor
          S)
        (d.tensorEnrichedFunctor.comp V
          (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N)
            c).toEnrichedFunctor) :=
  (GradingConvention.endHomEquiv (sourceTensor d S L M).toEnrichedFunctor
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N)
        c).toEnrichedFunctor P).trans
    ((Closed.gradedSourceEquiv d ((Center.ofBraided V).obj P)
      (SphereModuleMappingEnd.diagram d S L M) ⟨S⟩
      (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c)).trans
      (leftKanGradedHomEquiv d.tensorEnrichedFunctor ((Center.ofBraided V).obj P)
        (LeftKanComparison.externalObject
          (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S)
        (Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c)))

omit [SymmetricCategory I] in
/-- Every original binary source component is literal precomposition by the actual Day point. -/
theorem actionPairEquiv_app (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ (actionTarget d S L M N).toEnrichedFunctor.obj c) (j a : I) :
    (actionPairEquiv d S L M N c P f).app (j, a) =
      (f ≫ Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N)
        c (j ⊗ a)) ≫
        (MonoidalClosed.pre (Generators.point d.tensorEnrichedFunctor
          (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a))).app
          ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj ((j ⊗ a) ⊗ c)) := by
  let F := SphereModuleMappingEnd.diagram d S L M
  let Y := Closed.translatedTarget d (SphereModuleMappingEnd.diagram d S L N) c
  let Γ := (Center.ofBraided V).obj P
  change P ⟶ Enriched.weightedEnd (sourceTensor d S L M).toEnrichedFunctor
    Y.toEnrichedFunctor at f
  have hvalue : actionPairEquiv d S L M N c P f =
      leftKanGradedHomEquiv d.tensorEnrichedFunctor Γ
        (LeftKanComparison.externalObject F.toEnrichedFunctor S) Y
        (gradedPrecomp Γ
          (LeftKanComparison.fromKan d.tensorEnrichedFunctor F.toEnrichedFunctor S)
          (GradingConvention.endToPositive (sourceTensor d S L M).toEnrichedFunctor
            Y.toEnrichedFunctor f)) := by
    change leftKanGradedHomEquiv d.tensorEnrichedFunctor Γ
      (LeftKanComparison.externalObject F.toEnrichedFunctor S) Y
      (Closed.gradedSourceEquiv d Γ F ⟨S⟩ Y
        (GradingConvention.endHomEquiv (sourceTensor d S L M).toEnrichedFunctor
          Y.toEnrichedFunctor P f)) = _
    rw [GradingConvention.endHomEquiv_apply]
    rfl
  rw [hvalue, leftKanGradedHomEquiv_app, gradedPrecomp_app,
    GradingConvention.endToPositive_app_symmetric]
  have hp :
      (MonoidalClosed.pre (component
        (LeftKanComparison.fromKan d.tensorEnrichedFunctor F.toEnrichedFunctor S)
          (j ⊗ a))).app (Y.toEnrichedFunctor.obj (j ⊗ a)) ≫
        (MonoidalClosed.pre (leftKanUnitComponent d.tensorEnrichedFunctor
          (LeftKanComparison.externalObject F.toEnrichedFunctor S) (j, a))).app
          (Y.toEnrichedFunctor.obj (j ⊗ a)) =
      (MonoidalClosed.pre (Generators.point d.tensorEnrichedFunctor
        F.toEnrichedFunctor S (j, a))).app (Y.toEnrichedFunctor.obj (j ⊗ a)) := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map]
    exact congrArg (fun z => (MonoidalClosed.pre z).app
      (Y.toEnrichedFunctor.obj (j ⊗ a))) (Closed.unit_fromKan_component d F ⟨S⟩ (j, a))
  exact (Category.assoc _ _ _).trans (congrArg (fun z =>
    (f ≫ Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N)
      c (j ⊗ a)) ≫ z) hp)

omit [SymmetricCategory I] in
/-- Each full binary component evaluates the whole original source point and parameter. -/
theorem actionPairEquiv_uncurry_app (M N : Module d S L) (c : I) {P : V}
    (f : P ⟶ (actionTarget d S L M N).toEnrichedFunctor.obj c) (j a : I) :
    MonoidalClosed.uncurry ((actionPairEquiv d S L M N c P f).app (j, a)) =
      (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
        MonoidalClosed.uncurry (f ≫ Closed.π d (sourceTensor d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a)) := by
  rw [actionPairEquiv_app]
  exact MonoidalClosed.uncurry_pre_app
    ((SphereModuleMappingEnd.diagram d S L N).toEnrichedFunctor.obj ((j ⊗ a) ⊗ c))
    (f ≫ Closed.π d (sourceTensor d S L M) (SphereModuleMappingEnd.diagram d S L N)
      c (j ⊗ a))
    (Generators.point d.tensorEnrichedFunctor
      (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a))

omit [SymmetricCategory I] in
/-- Whole action-target end maps are detected by all original binary components at every
parameter object. This is the full graded Day/Kan universal property. -/
theorem actionPair_hom_ext (M N : Module d S L) (c : I) {P : V}
    {f g : P ⟶ (actionTarget d S L M N).toEnrichedFunctor.obj c}
    (h : ∀ j a,
      (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
        MonoidalClosed.uncurry (f ≫ Closed.π d (sourceTensor d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a)) =
      (Generators.point d.tensorEnrichedFunctor
        (SphereModuleMappingEnd.diagram d S L M).toEnrichedFunctor S (j, a) ▷ P) ≫
        MonoidalClosed.uncurry (g ≫ Closed.π d (sourceTensor d S L M)
          (SphereModuleMappingEnd.diagram d S L N) c (j ⊗ a))) : f = g := by
  apply (actionPairEquiv d S L M N c P).injective
  apply GradedNatTrans.ext
  funext p
  apply MonoidalClosed.uncurry_injective
  rw [actionPairEquiv_uncurry_app, actionPairEquiv_uncurry_app]
  exact h p.1 p.2

end CategoryTheory.Enriched.ModuleMappingR
