/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.Representable
import MathlibExt.CategoryTheory.Enriched.Limits.Products
import Mathlib.CategoryTheory.Enriched.FunctorCategory
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Enriched weighted coends

This file constructs weighted coends from object-indexed coproducts and one
coequalizer. The balancing relation is parametrized by the whole enriched
hom object. It also provides functoriality, a two-variable Fubini
isomorphism, and the enriched co-Yoneda isomorphism.

## Public imports

The enriched monoidal/natural-transformation API and enriched representables
are intentional public dependencies. Product/coequalizer implementation and
functor-category machinery remain private imports.

## Public API

The public surface is `weightedCoend`, its `ι`/`condition`/`desc`/`hom_ext`
interface, graded and ordinary weight/diagram maps with identity and
composition laws, `coyonedaIso`, and the general `fubiniIso`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Opposite BraidedCategory

universe uV vV uA vA uB vB

namespace CategoryTheory.Enriched

open Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
section EnrichedSource

variable {A : Type uA} [EnrichedCategory V A]

private def gradedNatApp
    {F G : EnrichedFunctor V A V}
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    (a : A) : F.obj a ⟶ G.obj a :=
  (eHomEquiv V).symm (t.app a)

omit [BraidedCategory V] in
private theorem uncurry_comp
    {P Q R H K : V}
    (p : H ⟶ (ihom P).obj Q) (q : K ⟶ (ihom Q).obj R) :
    MonoidalClosed.uncurry
        ((p ⊗ₘ q) ≫ eComp V P Q R) =
      (α_ P H K).inv ≫
        (MonoidalClosed.uncurry p ▷ K) ≫
        MonoidalClosed.uncurry q := by
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_comp,
    MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  have hTensor :
      P ◁ (p ⊗ₘ q) ≫
          (α_ P ((ihom P).obj Q) ((ihom Q).obj R)).inv =
        (α_ P H K).inv ≫
          ((P ◁ p) ▷ K) ≫
          (P ⊗ (ihom P).obj Q) ◁ q := by
    simpa only [id_tensorHom, tensorHom_def,
      MonoidalCategory.id_whiskerRight, Category.id_comp,
      comp_whiskerRight] using
      (associator_inv_naturality (𝟙 P) p q)
  rw [← Category.assoc, hTensor]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [← MonoidalClosed.uncurry_eq]
  dsimp
  rw [← MonoidalClosed.uncurry_eq]

private def rightAction
    (F : EnrichedFunctor V A V) (a b : A) :
    ((a ⟶[V] b) ⊗ F.obj a) ⟶ F.obj b :=
  (β_ (a ⟶[V] b) (F.obj a)).hom ≫
    MonoidalClosed.uncurry (F.map a b)

private theorem rightAction_id
    (F : EnrichedFunctor V A V) (a : A) :
    (λ_ (F.obj a)).inv ≫
        (eId V a ⊗ₘ 𝟙 (F.obj a)) ≫
        rightAction F a a =
      𝟙 (F.obj a) := by
  have h := congrArg MonoidalClosed.uncurry (F.map_id a)
  rw [MonoidalClosed.uncurry_natural_left] at h
  rw [MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry] at h
  dsimp only [rightAction]
  slice_lhs 2 3 =>
    rw [braiding_naturality]
  simp only [Category.assoc]
  rw [leftUnitor_inv_braiding_assoc]
  rw [id_tensorHom]
  rw [h]
  simp

private def coyonedaReorder
    (F : EnrichedFunctor V A V) (a b c : A) :
    F.obj a ⊗ ((a ⟶[V] b) ⊗ (b ⟶[V] c)) ⟶
      (b ⟶[V] c) ⊗ ((a ⟶[V] b) ⊗ F.obj a) :=
  ((α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).symm ≪≫
      whiskerRightIso (β_ (b ⟶[V] c) (a ⟶[V] b)) (F.obj a) ≪≫
      α_ (a ⟶[V] b) (b ⟶[V] c) (F.obj a) ≪≫
      whiskerLeftIso (a ⟶[V] b) (β_ (b ⟶[V] c) (F.obj a)) ≪≫
      (α_ (a ⟶[V] b) (F.obj a) (b ⟶[V] c)).symm ≪≫
      whiskerRightIso (β_ (a ⟶[V] b) (F.obj a)) (b ⟶[V] c) ≪≫
      α_ (F.obj a) (a ⟶[V] b) (b ⟶[V] c)).inv

private abbrev coendTarget
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) : A → V :=
  fun a ↦ W.obj (op a) ⊗ F.obj a

private abbrev coendSource
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) : A × A → V :=
  fun ab ↦ W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)

private abbrev weightAction
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    (a b : A) :
    coendSource W F (a, b) ⟶ coendTarget W F a :=
  (α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
    (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))

private abbrev diagramAction
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    (a b : A) :
    coendSource W F (a, b) ⟶ coendTarget W F b :=
  W.obj (op b) ◁
    ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
      MonoidalClosed.uncurry (F.map a b))

private theorem coyoneda_balance
    (F : EnrichedFunctor V A V) (c a b : A) :
    weightAction
          (EnrichedFunctor.contravariantRepresentable V A c) F a b ≫
        rightAction F a c =
      diagramAction
          (EnrichedFunctor.contravariantRepresentable V A c) F a b ≫
        rightAction F b c := by
  dsimp only [weightAction, diagramAction,
    EnrichedFunctor.contravariantRepresentable,
    rightAction]
  rw [MonoidalClosed.uncurry_curry]
  change
    ((α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).inv ≫
        (((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫
            eComp V a b c) ⊗ₘ 𝟙 (F.obj a))) ≫
          (β_ (a ⟶[V] c) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a c) =
      (b ⟶[V] c) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b)) ≫
        (β_ (b ⟶[V] c) (F.obj b)).hom ≫
          MonoidalClosed.uncurry (F.map b c)
  have hWeight :
      coyonedaReorder F a b c ≫
          (α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).inv ≫
          (((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫
              eComp V a b c) ⊗ₘ 𝟙 (F.obj a)) ≫
          (β_ (a ⟶[V] c) (F.obj a)).hom =
        F.obj a ◁ eComp V a b c := by
    dsimp only [coyonedaReorder]
    simp
  have hDiagram :
      coyonedaReorder F a b c ≫
          (b ⟶[V] c) ◁ (β_ (a ⟶[V] b) (F.obj a)).hom ≫
          (β_ (b ⟶[V] c) (F.obj a ⊗ (a ⟶[V] b))).hom =
        (α_ (F.obj a) (a ⟶[V] b) (b ⟶[V] c)).inv := by
    dsimp only [coyonedaReorder]
    rw [braiding_tensor_right_hom]
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerRightIso_inv,
      whiskerLeftIso_inv, Category.assoc]
    rw [← yang_baxter_assoc]
    simp
  let _ : IsIso (coyonedaReorder F a b c) := by
    dsimp only [coyonedaReorder]
    infer_instance
  rw [← cancel_epi (coyonedaReorder F a b c)]
  slice_lhs 1 4 =>
    rw [hWeight]
  conv_rhs =>
    rw [MonoidalCategory.whiskerLeft_comp]
  slice_rhs 3 4 =>
    rw [braiding_naturality_right]
  slice_rhs 1 3 =>
    rw [hDiagram]
  have hAssoc := congrArg MonoidalClosed.uncurry (F.map_comp a b c)
  rw [uncurry_comp] at hAssoc
  simpa only [Category.assoc] using
    (show F.obj a ◁ eComp V a b c ≫
          MonoidalClosed.uncurry (F.map a c) =
        (α_ (F.obj a) (a ⟶[V] b) (b ⟶[V] c)).inv ≫
          (MonoidalClosed.uncurry (F.map a b) ▷ (b ⟶[V] c)) ≫
          MonoidalClosed.uncurry (F.map b c) by
      simpa only [MonoidalClosed.uncurry_natural_left] using hAssoc)

private abbrev coyonedaCocone
    (F : EnrichedFunctor V A V) (c a : A) :
    coendTarget
        (EnrichedFunctor.contravariantRepresentable V A c) F a ⟶
      F.obj c :=
  rightAction F a c

private abbrev coyonedaUnit
    (F : EnrichedFunctor V A V) (c : A) :
    F.obj c ⟶
      coendTarget
        (EnrichedFunctor.contravariantRepresentable V A c) F c := by
  change F.obj c ⟶ (c ⟶[V] c) ⊗ F.obj c
  exact (λ_ (F.obj c)).inv ≫
    (eId V c ⊗ₘ 𝟙 (F.obj c))

private abbrev coyonedaInsert
    (F : EnrichedFunctor V A V) (c a : A) :
    coendTarget
          (EnrichedFunctor.contravariantRepresentable V A c) F a ⟶
      coendSource
          (EnrichedFunctor.contravariantRepresentable V A c) F (a, c) := by
  change ((a ⟶[V] c) ⊗ F.obj a) ⟶
    (c ⟶[V] c) ⊗ ((a ⟶[V] c) ⊗ F.obj a)
  exact (λ_ ((a ⟶[V] c) ⊗ F.obj a)).inv ≫
    (eId V c ▷ ((a ⟶[V] c) ⊗ F.obj a))

private theorem coyonedaInsert_weight
    (F : EnrichedFunctor V A V) (c a : A) :
    coyonedaInsert F c a ≫
        weightAction
          (EnrichedFunctor.contravariantRepresentable V A c) F a c =
      𝟙 _ := by
  dsimp only [coyonedaInsert, weightAction,
    EnrichedFunctor.contravariantRepresentable]
  simp only [coendTarget, coendSource,
    id_eq]
  rw [MonoidalClosed.uncurry_curry]
  simp only [Category.assoc, whiskerRight_tensor, tensorHom_id,
    comp_whiskerRight]
  rw [leftUnitor_tensor_inv_assoc]
  simp only [Iso.hom_inv_id_assoc]
  have hBase :
      ((λ_ (a ⟶[V] c)).inv ≫ eId V c ▷ (a ⟶[V] c)) ≫
          (β_ (c ⟶[V] c) (a ⟶[V] c)).hom ≫
          eComp V a c c =
        𝟙 (a ⟶[V] c) := by
    simp only [Category.assoc]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, braiding_naturality]
    simp only [Category.assoc]
    rw [leftUnitor_inv_braiding_assoc]
    rw [id_tensorHom]
    exact e_comp_id V a c
  have hBase' :
      (((λ_ (a ⟶[V] c)).inv ≫ eId V c ▷ (a ⟶[V] c)) ≫
          (β_ (c ⟶[V] c) (a ⟶[V] c)).hom) ≫
          eComp V a c c =
        𝟙 (a ⟶[V] c) := by
    simpa only [Category.assoc] using hBase
  rw [← comp_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [← comp_whiskerRight]
  rw [hBase']
  simp

private theorem coyonedaInsert_diagram
    (F : EnrichedFunctor V A V) (c a : A) :
    coyonedaInsert F c a ≫
        diagramAction
          (EnrichedFunctor.contravariantRepresentable V A c) F a c =
      coyonedaCocone F c a ≫ coyonedaUnit F c := by
  dsimp only [coyonedaInsert, diagramAction,
    coyonedaCocone, coyonedaUnit, rightAction]
  simp only [coendTarget, coendSource,
    EnrichedFunctor.contravariantRepresentable, id_eq]
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  rw [← Category.assoc, ← leftUnitor_inv_naturality]
  simp only [Category.assoc, tensorHom_id]

private noncomputable abbrev weightRelation
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (coendSource W F)]
    [HasCoproduct (coendTarget W F)] :
    (∐ coendSource W F) ⟶ ∐ coendTarget W F :=
  Sigma.desc fun ab ↦
    weightAction W F ab.1 ab.2 ≫
      Sigma.ι (coendTarget W F) ab.1

private noncomputable abbrev diagramRelation
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (coendSource W F)]
    [HasCoproduct (coendTarget W F)] :
    (∐ coendSource W F) ⟶ ∐ coendTarget W F :=
  Sigma.desc fun ab ↦
    diagramAction W F ab.1 ab.2 ≫
      Sigma.ι (coendTarget W F) ab.2

/-- The enriched weighted coend of a contravariant weight and a diagram. -/
public noncomputable abbrev weightedCoend
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) :
    let t : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let wa : ∀ a b, s (a, b) ⟶ t a := fun a b ↦
      (α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ
          𝟙 (F.obj a))
    let da : ∀ a b, s (a, b) ⟶ t b := fun a b ↦
      W.obj (op b) ◁
        ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))
    let l [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ wa ab.1 ab.2 ≫ Sigma.ι t ab.1
    let r [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ da ab.1 ab.2 ≫ Sigma.ι t ab.2
    ∀ [HasCoproduct s] [HasCoproduct t] [HasCoequalizer l r], V := by
  dsimp only
  intro _ _ _
  exact coequalizer
    (Sigma.desc fun ab : A × A ↦
      ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2) (F.obj ab.1)).inv ≫
          (MonoidalClosed.uncurry
            (W.map (op ab.2) (op ab.1)) ⊗ₘ 𝟙 (F.obj ab.1))) ≫
        Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.1)
    (Sigma.desc fun ab : A × A ↦
      (W.obj (op ab.2) ◁
          ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
            MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
        Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.2)

namespace weightedCoend

/-- The object-indexed coproduct diagram of a weighted coend. -/
public abbrev objects
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) : A → V :=
  fun a ↦ W.obj (op a) ⊗ F.obj a

/-- The hom-object-indexed relation diagram of a weighted coend. -/
public abbrev relations
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) : A × A → V :=
  fun ab ↦ W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)

/-- The original weighted-coend weight face on one relation summand. -/
public abbrev face0
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) (a b : A) :
    Enriched.weightedCoend.relations W F (a, b) ⟶ Enriched.weightedCoend.objects W F a :=
  (α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
    (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ 𝟙 (F.obj a))

/-- The original weighted-coend diagram-action face on one relation summand. -/
public abbrev face1
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V) (a b : A) :
    Enriched.weightedCoend.relations W F (a, b) ⟶ Enriched.weightedCoend.objects W F b :=
  W.obj (op b) ◁
    ((β_ (a ⟶[V] b) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a b))

/-- The parallel map expressing the weight action in a weighted coend. -/
public noncomputable abbrev leftMap
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (relations W F)] [HasCoproduct (objects W F)] :
    (∐ relations W F) ⟶ ∐ objects W F :=
  Sigma.desc fun ab ↦
    ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2) (F.obj ab.1)).inv ≫
        (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
          𝟙 (F.obj ab.1))) ≫ Sigma.ι (objects W F) ab.1

/-- The parallel map expressing the diagram action in a weighted coend. -/
public noncomputable abbrev rightMap
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    [HasCoproduct (relations W F)] [HasCoproduct (objects W F)] :
    (∐ relations W F) ⟶ ∐ objects W F :=
  Sigma.desc fun ab ↦
    (W.obj (op ab.2) ◁
        ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
          MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
      Sigma.ι (objects W F) ab.2

variable (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
variable [HasCoproduct (fun ab : A × A ↦
    W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1))]
  [HasCoproduct (fun a : A ↦ W.obj (op a) ⊗ F.obj a)]
  [HasCoequalizer
    (Sigma.desc fun ab : A × A ↦
      ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
            (F.obj ab.1)).inv ≫
          (MonoidalClosed.uncurry
              (W.map (op ab.2) (op ab.1)) ⊗ₘ 𝟙 (F.obj ab.1))) ≫
        Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.1)
    (Sigma.desc fun ab : A × A ↦
      (W.obj (op ab.2) ◁
          ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
            MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
        Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.2)]

/-- The characteristic map from the a-summand into a weighted coend. -/
public noncomputable def ι (a : A) :
    (W.obj (op a) ⊗ F.obj a) ⟶ weightedCoend W F :=
  Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) a ≫
    coequalizer.π
      (Sigma.desc fun ab : A × A ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2) (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry
              (W.map (op ab.2) (op ab.1)) ⊗ₘ 𝟙 (F.obj ab.1))) ≫
          Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.1)
      (Sigma.desc fun ab : A × A ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι (fun a : A ↦ W.obj (op a) ⊗ F.obj a) ab.2)

/-- The hom-object-parametrized balancing equation for the characteristic map. -/
public theorem condition (a b : A) :
    ((α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ
          𝟙 (F.obj a))) ≫
        ι W F a =
      (W.obj (op b) ◁
        ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))) ≫
        ι W F b := by
  have hWeight :
      Sigma.ι (coendSource W F) (a, b) ≫ weightRelation W F =
        weightAction W F a b ≫ Sigma.ι (coendTarget W F) a := by
    simp [weightRelation]
  have hDiagram :
      Sigma.ι (coendSource W F) (a, b) ≫ diagramRelation W F =
        diagramAction W F a b ≫ Sigma.ι (coendTarget W F) b := by
    simp [diagramRelation]
  have h := congrArg
    (fun k ↦ Sigma.ι (coendSource W F) (a, b) ≫ k)
    (coequalizer.condition (weightRelation W F)
      (diagramRelation W F))
  conv_lhs at h =>
    rw [← Category.assoc, hWeight,
      Category.assoc]
  conv_rhs at h =>
    rw [← Category.assoc, hDiagram,
      Category.assoc]
  simpa only [ι] using h

/-- Descend a balanced family from a weighted coend. -/
@[no_expose]
public noncomputable def desc {X : V}
    (k : ∀ a, (W.obj (op a) ⊗ F.obj a) ⟶ X)
    (h : ∀ a b,
      ((α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ
            𝟙 (F.obj a))) ≫ k a =
        (W.obj (op b) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ k b) :
    weightedCoend W F ⟶ X :=
  coequalizer.desc (Sigma.desc k) <| by
    apply Sigma.hom_ext
    intro ab
    have hWeight :
        Sigma.ι (coendSource W F) ab ≫ weightRelation W F =
          weightAction W F ab.1 ab.2 ≫
            Sigma.ι (coendTarget W F) ab.1 := by
      simp [weightRelation]
    have hDiagram :
        Sigma.ι (coendSource W F) ab ≫ diagramRelation W F =
          diagramAction W F ab.1 ab.2 ≫
            Sigma.ι (coendTarget W F) ab.2 := by
      simp [diagramRelation]
    conv_lhs =>
      rw [← Category.assoc, hWeight,
        Category.assoc, Sigma.ι_comp_desc]
    conv_rhs =>
      rw [← Category.assoc, hDiagram,
        Category.assoc, Sigma.ι_comp_desc]
    exact h ab.1 ab.2

/-- A descended family agrees with its components on every summand. -/
public theorem ι_desc {X : V}
    (k : ∀ a, (W.obj (op a) ⊗ F.obj a) ⟶ X)
    (h : ∀ a b,
      ((α_ (W.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
          (MonoidalClosed.uncurry (W.map (op b) (op a)) ⊗ₘ
            𝟙 (F.obj a))) ≫ k a =
        (W.obj (op b) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) ≫ k b)
    (a : A) : ι W F a ≫ desc W F k h = k a := by
  dsimp [ι, desc]
  rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

/-- Maps from a weighted coend are determined on the characteristic maps. -/
public theorem hom_ext {X : V}
    {f g : weightedCoend W F ⟶ X}
    (h : ∀ a, ι W F a ≫ f = ι W F a ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro a
  have ha := h a
  dsimp only [ι] at ha
  simpa only [Category.assoc] using ha

/-- Covariant functoriality of the weighted coend in its weight. -/
@[no_expose]
public noncomputable def mapWeightGraded
    {W W' : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W'.obj (op a) ⊗ F.obj a
    let s₂ : A × A → V := fun ab ↦
      W'.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W'.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W'.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W'.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂],
      coequalizer l₁ r₁ ⟶ coequalizer l₂ r₂ := by
  dsimp only
  intro _ _ _ _ _ _
  exact desc W F (fun a ↦
    (gradedNatApp t (op a) ⊗ₘ 𝟙 (F.obj a)) ≫
      ι W' F a) <| by
    intro a b
    have hWeight :
        weightAction W F a b ≫
            (gradedNatApp t (op a) ⊗ₘ 𝟙 (F.obj a)) =
          (gradedNatApp t (op b) ⊗ₘ
              𝟙 ((a ⟶[V] b) ⊗ F.obj a)) ≫
            weightAction W' F a b := by
      have h := t.uncurriedNaturality (op b) (op a)
      change MonoidalClosed.uncurry (W.map (op b) (op a)) ≫
          gradedNatApp t (op a) =
        (gradedNatApp t (op b) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (W'.map (op b) (op a)) at h
      dsimp only [weightAction]
      rw [Category.assoc, tensorHom_comp_tensorHom, h]
      rw [← tensorHom_comp_tensorHom]
      have hAssoc := associator_inv_naturality
        (gradedNatApp t (op b))
        (𝟙 (a ⟶[V] b)) (𝟙 (F.obj a))
      rw [← Category.assoc, ← hAssoc]
      simp only [MonoidalCategory.id_tensorHom_id]
      rw [Category.assoc]
    have hDiagram :
        diagramAction W F a b ≫
            (gradedNatApp t (op b) ⊗ₘ 𝟙 (F.obj b)) =
          (gradedNatApp t (op b) ⊗ₘ
              𝟙 ((a ⟶[V] b) ⊗ F.obj a)) ≫
            diagramAction W' F a b := by
      simpa only [diagramAction, tensorHom_id] using
        (whisker_exchange (gradedNatApp t (op b))
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b)))
    conv_lhs =>
      rw [← Category.assoc, hWeight,
        Category.assoc]
    conv_rhs =>
      rw [← Category.assoc, hDiagram,
        Category.assoc]
    rw [condition W' F a b]

/-- The value of mapWeight on a characteristic map. -/
public theorem mapWeightGraded_ι
    {W W' : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W W') :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W'.obj (op a) ⊗ F.obj a
    let s₂ : A × A → V := fun ab ↦
      W'.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W'.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W'.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W'.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂]
      (a : A),
      ι W F a ≫ mapWeightGraded F t =
        ((eHomEquiv V).symm (t.app (op a)) ⊗ₘ
          𝟙 (F.obj a)) ≫ ι W' F a := by
  dsimp only
  intro _ _ _ _ _ _ a
  simp only [mapWeightGraded, desc, ι, Category.assoc,
    coequalizer.π_desc, Sigma.ι_comp_desc, gradedNatApp, id_eq]

/-- Covariant functoriality of the weighted coend in its diagram. -/
@[no_expose]
public noncomputable def mapDiagramGraded
    (W : EnrichedFunctor V Aᵒᵖ V)
    {F F' : EnrichedFunctor V A V} (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W.obj (op a) ⊗ F'.obj a
    let s₂ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F'.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F'.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F'.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F'.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F'.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂],
      coequalizer l₁ r₁ ⟶ coequalizer l₂ r₂ := by
  dsimp only
  intro _ _ _ _ _ _
  exact desc W F (fun a ↦
    (𝟙 (W.obj (op a)) ⊗ₘ gradedNatApp t a) ≫
      ι W F' a) <| by
    intro a b
    have hWeight :
        weightAction W F a b ≫
            (𝟙 (W.obj (op a)) ⊗ₘ gradedNatApp t a) =
          (𝟙 (W.obj (op b)) ⊗ₘ
              (𝟙 (a ⟶[V] b) ⊗ₘ gradedNatApp t a)) ≫
            weightAction W F' a b := by
      dsimp only [weightAction]
      rw [Category.assoc, tensorHom_comp_tensorHom]
      have hAssoc := associator_inv_naturality
        (𝟙 (W.obj (op b))) (𝟙 (a ⟶[V] b))
        (gradedNatApp t a)
      conv_rhs =>
        rw [← Category.assoc, hAssoc, Category.assoc,
          tensorHom_comp_tensorHom]
      simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp,
        Category.comp_id]
    have hDiagram :
        diagramAction W F a b ≫
            (𝟙 (W.obj (op b)) ⊗ₘ gradedNatApp t b) =
          (𝟙 (W.obj (op b)) ⊗ₘ
              (𝟙 (a ⟶[V] b) ⊗ₘ gradedNatApp t a)) ≫
            diagramAction W F' a b := by
      dsimp only [diagramAction]
      simp only [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp]
      apply congrArg (fun q ↦ W.obj (op b) ◁ q)
      have hCore :
          (β_ (a ⟶[V] b) (F.obj a)).hom ≫
              MonoidalClosed.uncurry (F.map a b) ≫
              gradedNatApp t b =
            (𝟙 (a ⟶[V] b) ⊗ₘ gradedNatApp t a) ≫
              (β_ (a ⟶[V] b) (F'.obj a)).hom ≫
              MonoidalClosed.uncurry (F'.map a b) := by
        have hu :
            MonoidalClosed.uncurry (F.map a b) ≫ gradedNatApp t b =
              (gradedNatApp t a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
                MonoidalClosed.uncurry (F'.map a b) := by
          simpa only [gradedNatApp] using t.uncurriedNaturality a b
        rw [hu]
        rw [← Category.assoc, ← braiding_naturality]
        rw [Category.assoc]
      simpa only [id_tensorHom, Category.assoc] using hCore
    conv_lhs =>
      rw [← Category.assoc, hWeight,
        Category.assoc]
    conv_rhs =>
      rw [← Category.assoc, hDiagram, Category.assoc]
    rw [condition W F' a b]

/-- The value of mapDiagram on a characteristic map. -/
public theorem mapDiagramGraded_ι
    (W : EnrichedFunctor V Aᵒᵖ V)
    {F F' : EnrichedFunctor V A V} (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W.obj (op a) ⊗ F'.obj a
    let s₂ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F'.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F'.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F'.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F'.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F'.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂]
      (a : A),
      ι W F a ≫ mapDiagramGraded W t =
        (𝟙 (W.obj (op a)) ⊗ₘ
          (eHomEquiv V).symm (t.app a)) ≫
          ι W F' a := by
  dsimp only
  intro _ _ _ _ _ _ a
  simp only [mapDiagramGraded, desc, ι, Category.assoc,
    coequalizer.π_desc, Sigma.ι_comp_desc, gradedNatApp, id_eq]

section FunctorialityLaws

private theorem mapWeightGraded_id_of_component
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₀)
    (h : ∀ a, (eHomEquiv V).symm (t.app (op a)) = 𝟙 (W₀.obj (op a)))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapWeightGraded F₀ t = 𝟙 (weightedCoend W₀ F₀) := by
  apply hom_ext
  intro a
  rw [mapWeightGraded_ι]
  rw [h]
  simp

private theorem mapWeightGraded_comp_of_component
    {W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V} (F₀ : EnrichedFunctor V A V)
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₁ W₂)
    (t₀₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₂)
    (h : ∀ a, (eHomEquiv V).symm (t₀₂.app (op a)) =
      (eHomEquiv V).symm (t₀₁.app (op a)) ≫
        (eHomEquiv V).symm (t₁₂.app (op a)))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₁ F₀)] [HasCoproduct (objects W₁ F₀)]
    [HasCoequalizer (leftMap W₁ F₀) (rightMap W₁ F₀)]
    [HasCoproduct (relations W₂ F₀)] [HasCoproduct (objects W₂ F₀)]
    [HasCoequalizer (leftMap W₂ F₀) (rightMap W₂ F₀)] :
    mapWeightGraded F₀ t₀₂ =
      mapWeightGraded F₀ t₀₁ ≫ mapWeightGraded F₀ t₁₂ := by
  apply hom_ext
  intro a
  rw [mapWeightGraded_ι, h]
  let f := (eHomEquiv V).symm (t₀₁.app (op a))
  let g := (eHomEquiv V).symm (t₁₂.app (op a))
  change ((f ≫ g) ⊗ₘ 𝟙 (F₀.obj a)) ≫ ι W₂ F₀ a = _
  rw [show ((f ≫ g) ⊗ₘ 𝟙 (F₀.obj a)) =
      (f ⊗ₘ 𝟙 (F₀.obj a)) ≫ (g ⊗ₘ 𝟙 (F₀.obj a)) by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]]
  calc
    _ = (f ⊗ₘ 𝟙 (F₀.obj a)) ≫
        ((g ⊗ₘ 𝟙 (F₀.obj a)) ≫ ι W₂ F₀ a) := Category.assoc _ _ _
    _ = (f ⊗ₘ 𝟙 (F₀.obj a)) ≫
        (ι W₁ F₀ a ≫ mapWeightGraded F₀ t₁₂) := by
      rw [mapWeightGraded_ι]
    _ = ((f ⊗ₘ 𝟙 (F₀.obj a)) ≫ ι W₁ F₀ a) ≫
        mapWeightGraded F₀ t₁₂ := (Category.assoc _ _ _).symm
    _ = (ι W₀ F₀ a ≫ mapWeightGraded F₀ t₀₁) ≫
        mapWeightGraded F₀ t₁₂ := by
      rw [mapWeightGraded_ι]
    _ = _ := Category.assoc _ _ _

private theorem mapDiagramGraded_id_of_component
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₀)
    (h : ∀ a, (eHomEquiv V).symm (t.app a) = 𝟙 (F₀.obj a))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapDiagramGraded W₀ t = 𝟙 (weightedCoend W₀ F₀) := by
  apply hom_ext
  intro a
  rw [mapDiagramGraded_ι]
  rw [h]
  simp

private theorem mapDiagramGraded_comp_of_component
    (W₀ : EnrichedFunctor V Aᵒᵖ V)
    {F₀ F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (t₀₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₂)
    (h : ∀ a, (eHomEquiv V).symm (t₀₂.app a) =
      (eHomEquiv V).symm (t₀₁.app a) ≫
        (eHomEquiv V).symm (t₁₂.app a))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₀ F₁)] [HasCoproduct (objects W₀ F₁)]
    [HasCoequalizer (leftMap W₀ F₁) (rightMap W₀ F₁)]
    [HasCoproduct (relations W₀ F₂)] [HasCoproduct (objects W₀ F₂)]
    [HasCoequalizer (leftMap W₀ F₂) (rightMap W₀ F₂)] :
    mapDiagramGraded W₀ t₀₂ =
      mapDiagramGraded W₀ t₀₁ ≫ mapDiagramGraded W₀ t₁₂ := by
  apply hom_ext
  intro a
  rw [mapDiagramGraded_ι, h]
  let f := (eHomEquiv V).symm (t₀₁.app a)
  let g := (eHomEquiv V).symm (t₁₂.app a)
  change (𝟙 (W₀.obj (op a)) ⊗ₘ (f ≫ g)) ≫ ι W₀ F₂ a = _
  rw [show (𝟙 (W₀.obj (op a)) ⊗ₘ (f ≫ g)) =
      (𝟙 (W₀.obj (op a)) ⊗ₘ f) ≫
        (𝟙 (W₀.obj (op a)) ⊗ₘ g) by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp]]
  calc
    _ = (𝟙 (W₀.obj (op a)) ⊗ₘ f) ≫
        ((𝟙 (W₀.obj (op a)) ⊗ₘ g) ≫ ι W₀ F₂ a) := Category.assoc _ _ _
    _ = (𝟙 (W₀.obj (op a)) ⊗ₘ f) ≫
        (ι W₀ F₁ a ≫ mapDiagramGraded W₀ t₁₂) := by
      rw [mapDiagramGraded_ι]
    _ = ((𝟙 (W₀.obj (op a)) ⊗ₘ f) ≫ ι W₀ F₁ a) ≫
        mapDiagramGraded W₀ t₁₂ := (Category.assoc _ _ _).symm
    _ = (ι W₀ F₀ a ≫ mapDiagramGraded W₀ t₀₁) ≫
        mapDiagramGraded W₀ t₁₂ := by
      rw [mapDiagramGraded_ι]
    _ = _ := Category.assoc _ _ _

/-! ## Functoriality laws -/

/-- The graded weight map of the unit-graded identity is the identity. -/
public theorem mapWeightGraded_id
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapWeightGraded F₀ (GradedNatTrans.unitId W₀) =
      𝟙 (weightedCoend W₀ F₀) :=
  mapWeightGraded_id_of_component W₀ F₀ (GradedNatTrans.unitId W₀)
    (fun a => GradedNatTrans.unitId_component W₀ (op a))

/-- Graded weight maps preserve source-first composition. -/
public theorem mapWeightGraded_comp
    {W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V} (F₀ : EnrichedFunctor V A V)
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₀ W₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W₁ W₂)
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₁ F₀)] [HasCoproduct (objects W₁ F₀)]
    [HasCoequalizer (leftMap W₁ F₀) (rightMap W₁ F₀)]
    [HasCoproduct (relations W₂ F₀)] [HasCoproduct (objects W₂ F₀)]
    [HasCoequalizer (leftMap W₂ F₀) (rightMap W₂ F₀)] :
    mapWeightGraded F₀ (GradedNatTrans.unitComp t₀₁ t₁₂) =
      mapWeightGraded F₀ t₀₁ ≫ mapWeightGraded F₀ t₁₂ :=
  mapWeightGraded_comp_of_component F₀ t₀₁ t₁₂
    (GradedNatTrans.unitComp t₀₁ t₁₂)
    (fun a => GradedNatTrans.unitComp_component t₀₁ t₁₂ (op a))

/-- The graded diagram map of the unit-graded identity is the identity. -/
public theorem mapDiagramGraded_id
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapDiagramGraded W₀ (GradedNatTrans.unitId F₀) =
      𝟙 (weightedCoend W₀ F₀) :=
  mapDiagramGraded_id_of_component W₀ F₀ (GradedNatTrans.unitId F₀)
    (GradedNatTrans.unitId_component F₀)

/-- Graded diagram maps preserve source-first composition. -/
public theorem mapDiagramGraded_comp
    (W₀ : EnrichedFunctor V Aᵒᵖ V)
    {F₀ F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (t₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₀ F₁)] [HasCoproduct (objects W₀ F₁)]
    [HasCoequalizer (leftMap W₀ F₁) (rightMap W₀ F₁)]
    [HasCoproduct (relations W₀ F₂)] [HasCoproduct (objects W₀ F₂)]
    [HasCoequalizer (leftMap W₀ F₂) (rightMap W₀ F₂)] :
    mapDiagramGraded W₀ (GradedNatTrans.unitComp t₀₁ t₁₂) =
      mapDiagramGraded W₀ t₀₁ ≫ mapDiagramGraded W₀ t₁₂ :=
  mapDiagramGraded_comp_of_component W₀ t₀₁ t₁₂
    (GradedNatTrans.unitComp t₀₁ t₁₂)
    (GradedNatTrans.unitComp_component t₀₁ t₁₂)

end FunctorialityLaws

end weightedCoend

end EnrichedSource

section OrdinarySource

variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]

namespace weightedCoend

/-- Covariant functoriality of the weighted coend in its weight. -/
public noncomputable def mapWeight
    {W W' : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
    (t : W ⟶ W') (hsep : IsSeparator (𝟙_ V)) :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W'.obj (op a) ⊗ F.obj a
    let s₂ : A × A → V := fun ab ↦
      W'.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W'.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W'.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W'.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂],
      coequalizer l₁ r₁ ⟶ coequalizer l₂ r₂ := by
  dsimp only
  intro _ _ _ _ _ _
  exact mapWeightGraded F (t.toGradedNatTrans hsep)

/-- The value of mapWeight on a characteristic map. -/
public theorem mapWeight_ι
    {W W' : EnrichedFunctor V Aᵒᵖ V} (F : EnrichedFunctor V A V)
    (t : W ⟶ W') (hsep : IsSeparator (𝟙_ V)) :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W'.obj (op a) ⊗ F.obj a
    let s₂ : A × A → V := fun ab ↦
      W'.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W'.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W'.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W'.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂]
      (a : A),
      ι W F a ≫ mapWeight F t hsep =
        ((eHomEquiv V).symm
            (ForgetEnrichment.homTo V
              (t.out.app (ForgetEnrichment.of V (op a)))) ⊗ₘ
          𝟙 (F.obj a)) ≫ ι W' F a := by
  dsimp only
  intro _ _ _ _ _ _ a
  simpa only [mapWeight, EnrichedNatTrans.toGradedNatTrans, id_eq] using
    mapWeightGraded_ι F (t.toGradedNatTrans hsep) a

/-- Covariant functoriality of the weighted coend in its diagram. -/
public noncomputable def mapDiagram
    (W : EnrichedFunctor V Aᵒᵖ V)
    {F F' : EnrichedFunctor V A V} (t : F ⟶ F')
    (hsep : IsSeparator (𝟙_ V)) :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W.obj (op a) ⊗ F'.obj a
    let s₂ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F'.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F'.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F'.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F'.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F'.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂],
      coequalizer l₁ r₁ ⟶ coequalizer l₂ r₂ := by
  dsimp only
  intro _ _ _ _ _ _
  exact mapDiagramGraded W (t.toGradedNatTrans hsep)

/-- The value of mapDiagram on a characteristic map. -/
public theorem mapDiagram_ι
    (W : EnrichedFunctor V Aᵒᵖ V)
    {F F' : EnrichedFunctor V A V} (t : F ⟶ F')
    (hsep : IsSeparator (𝟙_ V)) :
    let t₁ : A → V := fun a ↦ W.obj (op a) ⊗ F.obj a
    let s₁ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let l₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F.obj ab.1))) ≫ Sigma.ι t₁ ab.1
    let r₁ [HasCoproduct s₁] [HasCoproduct t₁] :
        (∐ s₁) ⟶ ∐ t₁ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F.map ab.1 ab.2))) ≫
          Sigma.ι t₁ ab.2
    let t₂ : A → V := fun a ↦ W.obj (op a) ⊗ F'.obj a
    let s₂ : A × A → V := fun ab ↦
      W.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F'.obj ab.1)
    let l₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        ((α_ (W.obj (op ab.2)) (ab.1 ⟶[V] ab.2)
              (F'.obj ab.1)).inv ≫
            (MonoidalClosed.uncurry (W.map (op ab.2) (op ab.1)) ⊗ₘ
              𝟙 (F'.obj ab.1))) ≫ Sigma.ι t₂ ab.1
    let r₂ [HasCoproduct s₂] [HasCoproduct t₂] :
        (∐ s₂) ⟶ ∐ t₂ :=
      Sigma.desc fun ab ↦
        (W.obj (op ab.2) ◁
            ((β_ (ab.1 ⟶[V] ab.2) (F'.obj ab.1)).hom ≫
              MonoidalClosed.uncurry (F'.map ab.1 ab.2))) ≫
          Sigma.ι t₂ ab.2
    ∀ [HasCoproduct s₁] [HasCoproduct t₁] [HasCoequalizer l₁ r₁]
      [HasCoproduct s₂] [HasCoproduct t₂] [HasCoequalizer l₂ r₂]
      (a : A),
      ι W F a ≫ mapDiagram W t hsep =
        (𝟙 (W.obj (op a)) ⊗ₘ
          (eHomEquiv V).symm
            (ForgetEnrichment.homTo V
              (t.out.app (ForgetEnrichment.of V a)))) ≫
          ι W F' a := by
  dsimp only
  intro _ _ _ _ _ _ a
  simpa only [mapDiagram, EnrichedNatTrans.toGradedNatTrans, id_eq] using
    mapDiagramGraded_ι W (t.toGradedNatTrans hsep) a

section OrdinaryFunctorialityLaws

/-- The ordinary weight map of the identity is the identity. -/
public theorem mapWeight_id
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    (hsep : IsSeparator (𝟙_ V))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapWeight F₀ (𝟙 W₀) hsep = 𝟙 (weightedCoend W₀ F₀) := by
  change mapWeightGraded F₀
    ((𝟙 W₀ : W₀ ⟶ W₀).toGradedNatTrans hsep) = _
  rw [EnrichedNatTrans.toGradedNatTrans_id]
  exact mapWeightGraded_id W₀ F₀

/-- Ordinary weight maps preserve source-first composition. -/
public theorem mapWeight_comp
    {W₀ W₁ W₂ : EnrichedFunctor V Aᵒᵖ V} (F₀ : EnrichedFunctor V A V)
    (t₀₁ : W₀ ⟶ W₁) (t₁₂ : W₁ ⟶ W₂)
    (hsep : IsSeparator (𝟙_ V))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₁ F₀)] [HasCoproduct (objects W₁ F₀)]
    [HasCoequalizer (leftMap W₁ F₀) (rightMap W₁ F₀)]
    [HasCoproduct (relations W₂ F₀)] [HasCoproduct (objects W₂ F₀)]
    [HasCoequalizer (leftMap W₂ F₀) (rightMap W₂ F₀)] :
    mapWeight F₀ (t₀₁ ≫ t₁₂) hsep =
      mapWeight F₀ t₀₁ hsep ≫ mapWeight F₀ t₁₂ hsep := by
  change mapWeightGraded F₀
      ((t₀₁ ≫ t₁₂).toGradedNatTrans hsep) =
    mapWeightGraded F₀ (t₀₁.toGradedNatTrans hsep) ≫
      mapWeightGraded F₀ (t₁₂.toGradedNatTrans hsep)
  rw [EnrichedNatTrans.toGradedNatTrans_comp]
  exact mapWeightGraded_comp F₀
    (t₀₁.toGradedNatTrans hsep) (t₁₂.toGradedNatTrans hsep)

/-- The ordinary diagram map of the identity is the identity. -/
public theorem mapDiagram_id
    (W₀ : EnrichedFunctor V Aᵒᵖ V) (F₀ : EnrichedFunctor V A V)
    (hsep : IsSeparator (𝟙_ V))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)] :
    mapDiagram W₀ (𝟙 F₀) hsep = 𝟙 (weightedCoend W₀ F₀) := by
  change mapDiagramGraded W₀
    ((𝟙 F₀ : F₀ ⟶ F₀).toGradedNatTrans hsep) = _
  rw [EnrichedNatTrans.toGradedNatTrans_id]
  exact mapDiagramGraded_id W₀ F₀

/-- Ordinary diagram maps preserve source-first composition. -/
public theorem mapDiagram_comp
    (W₀ : EnrichedFunctor V Aᵒᵖ V)
    {F₀ F₁ F₂ : EnrichedFunctor V A V}
    (t₀₁ : F₀ ⟶ F₁) (t₁₂ : F₁ ⟶ F₂)
    (hsep : IsSeparator (𝟙_ V))
    [HasCoproduct (relations W₀ F₀)] [HasCoproduct (objects W₀ F₀)]
    [HasCoequalizer (leftMap W₀ F₀) (rightMap W₀ F₀)]
    [HasCoproduct (relations W₀ F₁)] [HasCoproduct (objects W₀ F₁)]
    [HasCoequalizer (leftMap W₀ F₁) (rightMap W₀ F₁)]
    [HasCoproduct (relations W₀ F₂)] [HasCoproduct (objects W₀ F₂)]
    [HasCoequalizer (leftMap W₀ F₂) (rightMap W₀ F₂)] :
    mapDiagram W₀ (t₀₁ ≫ t₁₂) hsep =
      mapDiagram W₀ t₀₁ hsep ≫ mapDiagram W₀ t₁₂ hsep := by
  change mapDiagramGraded W₀
      ((t₀₁ ≫ t₁₂).toGradedNatTrans hsep) =
    mapDiagramGraded W₀ (t₀₁.toGradedNatTrans hsep) ≫
      mapDiagramGraded W₀ (t₁₂.toGradedNatTrans hsep)
  rw [EnrichedNatTrans.toGradedNatTrans_comp]
  exact mapDiagramGraded_comp W₀
    (t₀₁.toGradedNatTrans hsep) (t₁₂.toGradedNatTrans hsep)

end OrdinaryFunctorialityLaws

end weightedCoend

end OrdinarySource

section EnrichedSource

variable {A : Type uA} [EnrichedCategory V A]

namespace weightedCoend

/-- The actual enriched co-Yoneda contraction is balanced on the entire hom object.
This characteristic needs no coproduct, coequalizer or separator. -/
public theorem coyonedaCondition (F : EnrichedFunctor V A V) (c a b : A) :
    ((α_ (b ⟶[V] c) (a ⟶[V] b) (F.obj a)).inv ≫
        (((β_ (b ⟶[V] c) (a ⟶[V] b)).hom ≫ eComp V a b c) ⊗ₘ
          𝟙 (F.obj a))) ≫
        (β_ (a ⟶[V] c) (F.obj a)).hom ≫
        MonoidalClosed.uncurry (F.map a c) =
      (b ⟶[V] c) ◁
          ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b)) ≫
        (β_ (b ⟶[V] c) (F.obj b)).hom ≫
          MonoidalClosed.uncurry (F.map b c) := by
  have h := coyoneda_balance F c a b
  dsimp only [weightAction, diagramAction, EnrichedFunctor.contravariantRepresentable,
    rightAction] at h
  rw [MonoidalClosed.uncurry_curry] at h
  exact h

/-- The enriched co-Yoneda isomorphism from the representable weighted
coend to the value of the diagram. -/
@[no_expose]
public noncomputable def coyonedaIso
    (F : EnrichedFunctor V A V) (c : A) :
    let R := EnrichedFunctor.contravariantRepresentable V A c
    let t : A → V := fun a ↦ R.obj (op a) ⊗ F.obj a
    let s : A × A → V := fun ab ↦
      R.obj (op ab.2) ⊗ ((ab.1 ⟶[V] ab.2) ⊗ F.obj ab.1)
    let wa : ∀ a b, s (a, b) ⟶ t a := fun a b ↦
      (α_ (R.obj (op b)) (a ⟶[V] b) (F.obj a)).inv ≫
        (MonoidalClosed.uncurry (R.map (op b) (op a)) ⊗ₘ
          𝟙 (F.obj a))
    let da : ∀ a b, s (a, b) ⟶ t b := fun a b ↦
      R.obj (op b) ◁
        ((β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))
    let l [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ wa ab.1 ab.2 ≫ Sigma.ι t ab.1
    let r [HasCoproduct s] [HasCoproduct t] : (∐ s) ⟶ ∐ t :=
      Sigma.desc fun ab ↦ da ab.1 ab.2 ≫ Sigma.ι t ab.2
    ∀ [HasCoproduct s] [HasCoproduct t] [HasCoequalizer l r],
      coequalizer l r ≅ F.obj c := by
  dsimp only
  intro _ _ _
  let e :
      weightedCoend
          (EnrichedFunctor.contravariantRepresentable V A c) F ≅
        F.obj c :=
    { hom :=
        desc (EnrichedFunctor.contravariantRepresentable V A c) F
          (coyonedaCocone F c) (coyoneda_balance F c)
      inv :=
        coyonedaUnit F c ≫
          ι (EnrichedFunctor.contravariantRepresentable V A c) F c
      hom_inv_id := by
        apply hom_ext
        intro a
        slice_lhs 1 2 =>
          rw [ι_desc]
        simp only [Category.comp_id]
        have h := congrArg
          (fun k ↦ coyonedaInsert F c a ≫ k)
          (condition
            (EnrichedFunctor.contravariantRepresentable V A c)
            F a c)
        conv_lhs at h =>
          rw [← Category.assoc, coyonedaInsert_weight,
            Category.id_comp]
        conv_rhs at h =>
          rw [← Category.assoc, coyonedaInsert_diagram]
        exact h.symm
      inv_hom_id := by
        slice_lhs 2 3 =>
          rw [ι_desc]
        simpa only [coyonedaUnit, coyonedaCocone, coendTarget,
          EnrichedFunctor.contravariantRepresentable,
          EnrichedFunctor.covariantRepresentable,
          Category.id_comp, Category.assoc, id_eq] using
          rightAction_id F c }
  exact e

private theorem coyonedaIso_ι_hom_private
    (F : EnrichedFunctor V A V) (c : A)
    [HasCoproduct
      (coendSource (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoproduct
      (coendTarget (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoequalizer
      (weightRelation (EnrichedFunctor.contravariantRepresentable V A c) F)
      (diagramRelation (EnrichedFunctor.contravariantRepresentable V A c) F)] (a : A) :
    ι (EnrichedFunctor.contravariantRepresentable V A c) F a ≫
        (coyonedaIso F c).hom =
      (β_ (a ⟶[V] c) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a c) := by
  change ι (EnrichedFunctor.contravariantRepresentable V A c) F a ≫
      desc (EnrichedFunctor.contravariantRepresentable V A c) F
        (coyonedaCocone F c) (coyoneda_balance F c) = coyonedaCocone F c a
  exact ι_desc (EnrichedFunctor.contravariantRepresentable V A c) F
    (coyonedaCocone F c) (coyoneda_balance F c) a

/-- The forward co-Yoneda map sends each coend generator to the enriched action.
Only the coproducts and coequalizer defining this particular coend are required. -/
@[reassoc]
public theorem coyonedaIso_ι_hom
    (F : EnrichedFunctor V A V) (c : A)
    [HasCoproduct (relations (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoproduct (objects (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoequalizer (leftMap (EnrichedFunctor.contravariantRepresentable V A c) F)
      (rightMap (EnrichedFunctor.contravariantRepresentable V A c) F)] (a : A) :
      ι (EnrichedFunctor.contravariantRepresentable V A c) F a ≫
        (coyonedaIso F c).hom =
        (β_ (a ⟶[V] c) (F.obj a)).hom ≫ MonoidalClosed.uncurry (F.map a c) := by
  exact coyonedaIso_ι_hom_private F c a

private theorem coyonedaIso_inv_private
    (F : EnrichedFunctor V A V) (c : A)
    [HasCoproduct
      (coendSource (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoproduct
      (coendTarget (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoequalizer
      (weightRelation (EnrichedFunctor.contravariantRepresentable V A c) F)
      (diagramRelation (EnrichedFunctor.contravariantRepresentable V A c) F)] :
    (coyonedaIso F c).inv =
      (λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c)) ≫
        ι (EnrichedFunctor.contravariantRepresentable V A c) F c := by
  change ((λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c))) ≫
      ι (EnrichedFunctor.contravariantRepresentable V A c) F c = _
  exact Category.assoc _ _ _

/-- The inverse co-Yoneda map inserts the enriched identity into its `c`-generator.
Only the coproducts and coequalizer defining this particular coend are required. -/
public theorem coyonedaIso_inv
    (F : EnrichedFunctor V A V) (c : A)
    [HasCoproduct (relations (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoproduct (objects (EnrichedFunctor.contravariantRepresentable V A c) F)]
    [HasCoequalizer (leftMap (EnrichedFunctor.contravariantRepresentable V A c) F)
      (rightMap (EnrichedFunctor.contravariantRepresentable V A c) F)] :
      (coyonedaIso F c).inv =
        (λ_ (F.obj c)).inv ≫ (eId V c ⊗ₘ 𝟙 (F.obj c)) ≫
          ι (EnrichedFunctor.contravariantRepresentable V A c) F c := by
  exact coyonedaIso_inv_private F c

section Fubini

variable {B : Type uB}

/-- The general Fubini isomorphism from an iterated coend presentation to
the simultaneous two-variable coend presentation. -/
@[no_expose]
public noncomputable def fubiniIso
    (T : A × B → V)
    (BT : A × (B × B) → V)
    (b₀ : ∀ p, BT p ⟶ T (p.1, p.2.1))
    (b₁ : ∀ p, BT p ⟶ T (p.1, p.2.2))
    (R : (A × A) × B → V)
    (BR : (A × A) × (B × B) → V)
    (r₀ : ∀ p, BR p ⟶ R (p.1, p.2.1))
    (r₁ : ∀ p, BR p ⟶ R (p.1, p.2.2))
    (a₀ : ∀ p, R p ⟶ T (p.1.1, p.2))
    (a₁ : ∀ p, R p ⟶ T (p.1.2, p.2)) :
    let tT : A → B → V := fun a b ↦ T (a, b)
    let sT : A → B × B → V := fun a bb ↦ BT (a, bb)
    let lT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
        (∐ sT a) ⟶ ∐ tT a :=
      Sigma.desc fun bb ↦ b₀ (a, bb) ≫ Sigma.ι (tT a) bb.1
    let rT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
        (∐ sT a) ⟶ ∐ tT a :=
      Sigma.desc fun bb ↦ b₁ (a, bb) ≫ Sigma.ι (tT a) bb.2
    let tR : A × A → B → V := fun aa b ↦ R (aa, b)
    let sR : A × A → B × B → V := fun aa bb ↦ BR (aa, bb)
    let lR (aa : A × A) [HasCoproduct (sR aa)]
        [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
      Sigma.desc fun bb ↦ r₀ (aa, bb) ≫ Sigma.ι (tR aa) bb.1
    let rR (aa : A × A) [HasCoproduct (sR aa)]
        [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
      Sigma.desc fun bb ↦ r₁ (aa, bb) ≫ Sigma.ι (tR aa) bb.2
    ∀ [∀ a, HasCoproduct (sT a)] [∀ a, HasCoproduct (tT a)]
      [∀ a, HasCoequalizer (lT a) (rT a)]
      [∀ aa, HasCoproduct (sR aa)] [∀ aa, HasCoproduct (tR aa)]
      [∀ aa, HasCoequalizer (lR aa) (rR aa)],
      let KT : A → V := fun a ↦ coequalizer (lT a) (rT a)
      let jT : ∀ a b, T (a, b) ⟶ KT a := fun a b ↦
        Sigma.ι (tT a) b ≫ coequalizer.π (lT a) (rT a)
      let KR : A × A → V := fun aa ↦ coequalizer (lR aa) (rR aa)
      ∀ (h₀ : ∀ aa bb,
          (r₀ (aa, bb) ≫ a₀ (aa, bb.1)) ≫ jT aa.1 bb.1 =
            (r₁ (aa, bb) ≫ a₀ (aa, bb.2)) ≫ jT aa.1 bb.2)
        (h₁ : ∀ aa bb,
          (r₀ (aa, bb) ≫ a₁ (aa, bb.1)) ≫ jT aa.2 bb.1 =
            (r₁ (aa, bb) ≫ a₁ (aa, bb.2)) ≫ jT aa.2 bb.2),
        let ā₀ : ∀ aa, KR aa ⟶ KT aa.1 := fun aa ↦
          coequalizer.desc
            (Sigma.desc fun b ↦ a₀ (aa, b) ≫ jT aa.1 b) (by
              apply Sigma.hom_ext
              intro bb
              simpa [lR, rR, Category.assoc] using h₀ aa bb)
        let ā₁ : ∀ aa, KR aa ⟶ KT aa.2 := fun aa ↦
          coequalizer.desc
            (Sigma.desc fun b ↦ a₁ (aa, b) ≫ jT aa.2 b) (by
              apply Sigma.hom_ext
              intro bb
              simpa [lR, rR, Category.assoc] using h₁ aa bb)
        let outerL [HasCoproduct KR] [HasCoproduct KT] :
            (∐ KR) ⟶ ∐ KT :=
          Sigma.desc fun aa ↦ ā₀ aa ≫ Sigma.ι KT aa.1
        let outerR [HasCoproduct KR] [HasCoproduct KT] :
            (∐ KR) ⟶ ∐ KT :=
          Sigma.desc fun aa ↦ ā₁ aa ≫ Sigma.ι KT aa.2
        let rel := Sum ((A × A) × B) (A × (B × B))
        let simSource : rel → V := Sum.elim R BT
        let simTarget : A × B → V := T
        let simL [HasCoproduct simSource] [HasCoproduct simTarget] :
            (∐ simSource) ⟶ ∐ simTarget :=
          Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
            (fun p => a₀ p ≫ Sigma.ι simTarget (p.1.1, p.2))
            (fun p => b₀ p ≫ Sigma.ι simTarget (p.1, p.2.1)))
        let simR [HasCoproduct simSource] [HasCoproduct simTarget] :
            (∐ simSource) ⟶ ∐ simTarget :=
          Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
            (fun p => a₁ p ≫ Sigma.ι simTarget (p.1.2, p.2))
            (fun p => b₁ p ≫ Sigma.ι simTarget (p.1, p.2.2)))
        ∀ [HasCoproduct KR] [HasCoproduct KT]
          [HasCoequalizer outerL outerR]
          [HasCoproduct simSource] [HasCoproduct simTarget]
          [HasCoequalizer simL simR],
          coequalizer outerL outerR ≅ coequalizer simL simR := by
  dsimp only
  intro _ _ _ _ _ _ h₀ h₁ _ _ _ _ _ _
  let tT : A → B → V := fun a b ↦ T (a, b)
  let sT : A → B × B → V := fun a bb ↦ BT (a, bb)
  let lT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
      (∐ sT a) ⟶ ∐ tT a :=
    Sigma.desc fun bb ↦ b₀ (a, bb) ≫ Sigma.ι (tT a) bb.1
  let rT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
      (∐ sT a) ⟶ ∐ tT a :=
    Sigma.desc fun bb ↦ b₁ (a, bb) ≫ Sigma.ι (tT a) bb.2
  let tR : A × A → B → V := fun aa b ↦ R (aa, b)
  let sR : A × A → B × B → V := fun aa bb ↦ BR (aa, bb)
  let lR (aa : A × A) [HasCoproduct (sR aa)]
      [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
    Sigma.desc fun bb ↦ r₀ (aa, bb) ≫ Sigma.ι (tR aa) bb.1
  let rR (aa : A × A) [HasCoproduct (sR aa)]
      [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
    Sigma.desc fun bb ↦ r₁ (aa, bb) ≫ Sigma.ι (tR aa) bb.2
  let KT : A → V := fun a ↦ coequalizer (lT a) (rT a)
  let jT (a : A) (b : B) : T (a, b) ⟶ KT a :=
    Sigma.ι (tT a) b ≫ coequalizer.π (lT a) (rT a)
  have conditionT (a : A) (b b' : B) :
      b₀ (a, (b, b')) ≫ jT a b = b₁ (a, (b, b')) ≫ jT a b' := by
    let bb : B × B := (b, b')
    have h := congrArg
      (fun k ↦ Sigma.ι (sT a) bb ≫ k)
      (coequalizer.condition (lT a) (rT a))
    simpa [bb, lT, rT, jT, Category.assoc] using h
  let KR : A × A → V := fun aa ↦ coequalizer (lR aa) (rR aa)
  let jR (aa : A × A) (b : B) : R (aa, b) ⟶ KR aa :=
    Sigma.ι (tR aa) b ≫ coequalizer.π (lR aa) (rR aa)
  let descT (a : A) {X : V} (k : ∀ b, T (a, b) ⟶ X)
      (h : ∀ bb, b₀ (a, bb) ≫ k bb.1 = b₁ (a, bb) ≫ k bb.2) :
      KT a ⟶ X :=
    coequalizer.desc (Sigma.desc k) (by
      apply Sigma.hom_ext
      intro bb
      simpa [lT, rT, Category.assoc] using h bb)
  have jT_desc (a : A) {X : V} (k : ∀ b, T (a, b) ⟶ X)
      (h : ∀ bb, b₀ (a, bb) ≫ k bb.1 = b₁ (a, bb) ≫ k bb.2)
      (b : B) : jT a b ≫ descT a k h = k b := by
    dsimp only [jT, descT]
    rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
  have homExtT (a : A) {X : V} {f g : KT a ⟶ X}
      (h : ∀ b, jT a b ≫ f = jT a b ≫ g) : f = g := by
    apply coequalizer.hom_ext
    apply Sigma.hom_ext
    intro b
    have hb := h b
    dsimp only [jT] at hb
    simpa only [Category.assoc] using hb
  let descR (aa : A × A) {X : V} (k : ∀ b, R (aa, b) ⟶ X)
      (h : ∀ bb, r₀ (aa, bb) ≫ k bb.1 = r₁ (aa, bb) ≫ k bb.2) :
      KR aa ⟶ X :=
    coequalizer.desc (Sigma.desc k) (by
      apply Sigma.hom_ext
      intro bb
      simpa [lR, rR, Category.assoc] using h bb)
  have jR_desc (aa : A × A) {X : V} (k : ∀ b, R (aa, b) ⟶ X)
      (h : ∀ bb, r₀ (aa, bb) ≫ k bb.1 = r₁ (aa, bb) ≫ k bb.2)
      (b : B) : jR aa b ≫ descR aa k h = k b := by
    dsimp only [jR, descR]
    rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
  have homExtR (aa : A × A) {X : V} {f g : KR aa ⟶ X}
      (h : ∀ b, jR aa b ≫ f = jR aa b ≫ g) : f = g := by
    apply coequalizer.hom_ext
    apply Sigma.hom_ext
    intro b
    have hb := h b
    dsimp only [jR] at hb
    simpa only [Category.assoc] using hb
  have h₀' (aa : A × A) (bb : B × B) :
      r₀ (aa, bb) ≫ (a₀ (aa, bb.1) ≫ jT aa.1 bb.1) =
        r₁ (aa, bb) ≫ (a₀ (aa, bb.2) ≫ jT aa.1 bb.2) := by
    simpa [tT, lT, rT, jT, Category.assoc] using h₀ aa bb
  have h₁' (aa : A × A) (bb : B × B) :
      r₀ (aa, bb) ≫ (a₁ (aa, bb.1) ≫ jT aa.2 bb.1) =
        r₁ (aa, bb) ≫ (a₁ (aa, bb.2) ≫ jT aa.2 bb.2) := by
    simpa [tT, lT, rT, jT, Category.assoc] using h₁ aa bb
  let ā₀ (aa : A × A) : KR aa ⟶ KT aa.1 :=
    descR aa (fun b ↦ a₀ (aa, b) ≫ jT aa.1 b) (h₀' aa)
  let ā₁ (aa : A × A) : KR aa ⟶ KT aa.2 :=
    descR aa (fun b ↦ a₁ (aa, b) ≫ jT aa.2 b) (h₁' aa)
  have jR_ā₀ (aa : A × A) (b : B) :
      jR aa b ≫ ā₀ aa = a₀ (aa, b) ≫ jT aa.1 b := by
    dsimp only [ā₀]
    exact jR_desc aa (fun b ↦ a₀ (aa, b) ≫ jT aa.1 b) (h₀' aa) b
  have jR_ā₁ (aa : A × A) (b : B) :
      jR aa b ≫ ā₁ aa = a₁ (aa, b) ≫ jT aa.2 b := by
    dsimp only [ā₁]
    exact jR_desc aa (fun b ↦ a₁ (aa, b) ≫ jT aa.2 b) (h₁' aa) b
  let outerL [HasCoproduct KR] [HasCoproduct KT] :
      (∐ KR) ⟶ ∐ KT :=
    Sigma.desc fun aa ↦ ā₀ aa ≫ Sigma.ι KT aa.1
  let outerR [HasCoproduct KR] [HasCoproduct KT] :
      (∐ KR) ⟶ ∐ KT :=
    Sigma.desc fun aa ↦ ā₁ aa ≫ Sigma.ι KT aa.2
  let nested : V := coequalizer outerL outerR
  let jO (a : A) : KT a ⟶ nested :=
    Sigma.ι KT a ≫ coequalizer.π outerL outerR
  have conditionO (a a' : A) :
      ā₀ (a, a') ≫ jO a = ā₁ (a, a') ≫ jO a' := by
    have h := congrArg
      (fun k ↦ Sigma.ι KR (a, a') ≫ k)
      (coequalizer.condition outerL outerR)
    simp only [outerL, outerR] at h
    conv_lhs at h =>
      rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc]
    conv_rhs at h =>
      rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc]
    simpa only [jO] using h
  let descO {X : V} (k : ∀ a, KT a ⟶ X)
      (h : ∀ aa, ā₀ aa ≫ k aa.1 = ā₁ aa ≫ k aa.2) :
      nested ⟶ X :=
    coequalizer.desc (Sigma.desc k) (by
      apply Sigma.hom_ext
      intro aa
      simpa [outerL, outerR, Category.assoc] using h aa)
  have jO_desc {X : V} (k : ∀ a, KT a ⟶ X)
      (h : ∀ aa, ā₀ aa ≫ k aa.1 = ā₁ aa ≫ k aa.2)
      (a : A) : jO a ≫ descO k h = k a := by
    dsimp only [jO, descO]
    rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
  have homExtO {X : V} {f g : nested ⟶ X}
      (h : ∀ a, jO a ≫ f = jO a ≫ g) : f = g := by
    apply coequalizer.hom_ext
    apply Sigma.hom_ext
    intro a
    have ha := h a
    dsimp only [jO] at ha
    simpa only [Category.assoc] using ha
  let rel := Sum ((A × A) × B) (A × (B × B))
  let simSource : rel → V := Sum.elim R BT
  let simTarget : A × B → V := T
  let simL [HasCoproduct simSource] [HasCoproduct simTarget] :
      (∐ simSource) ⟶ ∐ simTarget :=
    Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
      (fun p => a₀ p ≫ Sigma.ι simTarget (p.1.1, p.2))
      (fun p => b₀ p ≫ Sigma.ι simTarget (p.1, p.2.1)))
  let simR [HasCoproduct simSource] [HasCoproduct simTarget] :
      (∐ simSource) ⟶ ∐ simTarget :=
    Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
      (fun p => a₁ p ≫ Sigma.ι simTarget (p.1.2, p.2))
      (fun p => b₁ p ≫ Sigma.ι simTarget (p.1, p.2.2)))
  let simultaneous : V := coequalizer simL simR
  let jS (a : A) (b : B) : T (a, b) ⟶ simultaneous :=
    Sigma.ι simTarget (a, b) ≫ coequalizer.π simL simR
  have conditionSA (a a' : A) (b : B) :
      a₀ ((a, a'), b) ≫ jS a b =
        a₁ ((a, a'), b) ≫ jS a' b := by
    let p : rel := .inl ((a, a'), b)
    have h := congrArg
      (fun k ↦ Sigma.ι simSource p ≫ k)
      (coequalizer.condition simL simR)
    simp only [simL, simR, p, Sigma.ι_comp_desc_assoc] at h
    calc
      _ = (a₀ ((a, a'), b) ≫ Sigma.ι simTarget (a, b)) ≫
          coequalizer.π simL simR := (Category.assoc _ _ _).symm
      _ = (a₁ ((a, a'), b) ≫ Sigma.ι simTarget (a', b)) ≫
          coequalizer.π simL simR := h
      _ = _ := Category.assoc _ _ _
  have conditionSB (a : A) (b b' : B) :
      b₀ (a, (b, b')) ≫ jS a b =
        b₁ (a, (b, b')) ≫ jS a b' := by
    let p : rel := .inr (a, (b, b'))
    have h := congrArg
      (fun k ↦ Sigma.ι simSource p ≫ k)
      (coequalizer.condition simL simR)
    simp only [simL, simR, p, Sigma.ι_comp_desc_assoc] at h
    calc
      _ = (b₀ (a, (b, b')) ≫ Sigma.ι simTarget (a, b)) ≫
          coequalizer.π simL simR := (Category.assoc _ _ _).symm
      _ = (b₁ (a, (b, b')) ≫ Sigma.ι simTarget (a, b')) ≫
          coequalizer.π simL simR := h
      _ = _ := Category.assoc _ _ _
  let descS {X : V} (k : ∀ a b, T (a, b) ⟶ X)
      (hA : ∀ aa b, a₀ (aa, b) ≫ k aa.1 b =
        a₁ (aa, b) ≫ k aa.2 b)
      (hB : ∀ a bb, b₀ (a, bb) ≫ k a bb.1 =
        b₁ (a, bb) ≫ k a bb.2) : simultaneous ⟶ X :=
    coequalizer.desc (Sigma.desc fun p ↦ k p.1 p.2) (by
      apply Sigma.hom_ext
      intro p
      rcases p with p | p
      · dsimp only [simL, simR]
        rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
        dsimp only
        change (a₀ p ≫ Sigma.ι simTarget (p.1.1, p.2)) ≫
            Sigma.desc (fun q => k q.1 q.2) =
          (a₁ p ≫ Sigma.ι simTarget (p.1.2, p.2)) ≫
            Sigma.desc (fun q => k q.1 q.2)
        simp only [Category.assoc, Sigma.ι_comp_desc]
        exact hA p.1 p.2
      · dsimp only [simL, simR]
        rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
        dsimp only
        change (b₀ p ≫ Sigma.ι simTarget (p.1, p.2.1)) ≫
            Sigma.desc (fun q => k q.1 q.2) =
          (b₁ p ≫ Sigma.ι simTarget (p.1, p.2.2)) ≫
            Sigma.desc (fun q => k q.1 q.2)
        simp only [Category.assoc, Sigma.ι_comp_desc]
        exact hB p.1 p.2)
  have jS_desc {X : V} (k : ∀ a b, T (a, b) ⟶ X)
      (hA : ∀ aa b, a₀ (aa, b) ≫ k aa.1 b =
        a₁ (aa, b) ≫ k aa.2 b)
      (hB : ∀ a bb, b₀ (a, bb) ≫ k a bb.1 =
        b₁ (a, bb) ≫ k a bb.2)
      (a : A) (b : B) : jS a b ≫ descS k hA hB = k a b := by
    dsimp only [jS, descS]
    rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
  have homExtS {X : V} {f g : simultaneous ⟶ X}
      (h : ∀ a b, jS a b ≫ f = jS a b ≫ g) : f = g := by
    apply coequalizer.hom_ext
    apply Sigma.hom_ext
    intro p
    have hp := h p.1 p.2
    dsimp only [jS] at hp
    simpa only [Category.assoc] using hp
  have simBalanceA (aa : A × A) (b : B) :
      a₀ (aa, b) ≫ (jT aa.1 b ≫ jO aa.1) =
        a₁ (aa, b) ≫ (jT aa.2 b ≫ jO aa.2) := by
    rw [← Category.assoc, ← jR_ā₀, Category.assoc,
      conditionO aa.1 aa.2, ← Category.assoc, jR_ā₁,
      Category.assoc]
  have simBalanceB (a : A) (bb : B × B) :
      b₀ (a, bb) ≫ (jT a bb.1 ≫ jO a) =
        b₁ (a, bb) ≫ (jT a bb.2 ≫ jO a) := by
    rw [← Category.assoc, conditionT]
    rw [Category.assoc]
  let simToNested : simultaneous ⟶ nested :=
    descS (fun a b ↦ jT a b ≫ jO a) simBalanceA simBalanceB
  have jS_simToNested (a : A) (b : B) :
      jS a b ≫ simToNested = jT a b ≫ jO a := by
    dsimp only [simToNested]
    exact jS_desc (fun a b ↦ jT a b ≫ jO a)
      simBalanceA simBalanceB a b
  have innerBalance (a : A) (bb : B × B) :
      b₀ (a, bb) ≫ jS a bb.1 = b₁ (a, bb) ≫ jS a bb.2 :=
    conditionSB a bb.1 bb.2
  let innerToSim (a : A) : KT a ⟶ simultaneous :=
    descT a (fun b ↦ jS a b) (innerBalance a)
  have jT_innerToSim (a : A) (b : B) :
      jT a b ≫ innerToSim a = jS a b := by
    dsimp only [innerToSim]
    exact jT_desc a (fun b ↦ jS a b) (innerBalance a) b
  have outerBalance (aa : A × A) :
      ā₀ aa ≫ innerToSim aa.1 = ā₁ aa ≫ innerToSim aa.2 := by
    apply homExtR aa
    intro b
    calc
      jR aa b ≫ (ā₀ aa ≫ innerToSim aa.1) =
          (jR aa b ≫ ā₀ aa) ≫ innerToSim aa.1 :=
        (Category.assoc _ _ _).symm
      _ = (a₀ (aa, b) ≫ jT aa.1 b) ≫ innerToSim aa.1 := by
        rw [jR_ā₀]
      _ = a₀ (aa, b) ≫ (jT aa.1 b ≫ innerToSim aa.1) :=
        Category.assoc _ _ _
      _ = a₀ (aa, b) ≫ jS aa.1 b := by rw [jT_innerToSim]
      _ = a₁ (aa, b) ≫ jS aa.2 b := conditionSA aa.1 aa.2 b
      _ = a₁ (aa, b) ≫ (jT aa.2 b ≫ innerToSim aa.2) := by
        rw [jT_innerToSim]
      _ = (a₁ (aa, b) ≫ jT aa.2 b) ≫ innerToSim aa.2 :=
        (Category.assoc _ _ _).symm
      _ = (jR aa b ≫ ā₁ aa) ≫ innerToSim aa.2 := by
        rw [jR_ā₁]
      _ = jR aa b ≫ (ā₁ aa ≫ innerToSim aa.2) :=
        Category.assoc _ _ _
  let nestedToSim : nested ⟶ simultaneous :=
    descO innerToSim outerBalance
  have jO_nestedToSim (a : A) :
      jO a ≫ nestedToSim = innerToSim a := by
    dsimp only [nestedToSim]
    exact jO_desc innerToSim outerBalance a
  exact
    { hom := nestedToSim
      inv := simToNested
      hom_inv_id := by
        apply homExtO
        intro a
        rw [Category.comp_id]
        rw [← Category.assoc, jO_nestedToSim]
        apply homExtT a
        intro b
        rw [← Category.assoc, jT_innerToSim, jS_simToNested]
      inv_hom_id := by
        apply homExtS
        intro a b
        rw [Category.comp_id]
        rw [← Category.assoc, jS_simToNested, Category.assoc,
          jO_nestedToSim, jT_innerToSim] }

omit [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V] [EnrichedCategory V A] in
/-- The Fubini isomorphism and its inverse preserve the original two-variable
coend generators. The statement uses only the coproducts and coequalizers of
these particular presentations, together with the two balancing hypotheses. -/
public theorem fubiniIso_generators
    (T : A × B → V)
    (BT : A × (B × B) → V)
    (b₀ : ∀ p, BT p ⟶ T (p.1, p.2.1))
    (b₁ : ∀ p, BT p ⟶ T (p.1, p.2.2))
    (R : (A × A) × B → V)
    (BR : (A × A) × (B × B) → V)
    (r₀ : ∀ p, BR p ⟶ R (p.1, p.2.1))
    (r₁ : ∀ p, BR p ⟶ R (p.1, p.2.2))
    (a₀ : ∀ p, R p ⟶ T (p.1.1, p.2))
    (a₁ : ∀ p, R p ⟶ T (p.1.2, p.2)) :
    let tT : A → B → V := fun a b ↦ T (a, b)
    let sT : A → B × B → V := fun a bb ↦ BT (a, bb)
    let lT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
        (∐ sT a) ⟶ ∐ tT a :=
      Sigma.desc fun bb ↦ b₀ (a, bb) ≫ Sigma.ι (tT a) bb.1
    let rT (a : A) [HasCoproduct (sT a)] [HasCoproduct (tT a)] :
        (∐ sT a) ⟶ ∐ tT a :=
      Sigma.desc fun bb ↦ b₁ (a, bb) ≫ Sigma.ι (tT a) bb.2
    let tR : A × A → B → V := fun aa b ↦ R (aa, b)
    let sR : A × A → B × B → V := fun aa bb ↦ BR (aa, bb)
    let lR (aa : A × A) [HasCoproduct (sR aa)]
        [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
      Sigma.desc fun bb ↦ r₀ (aa, bb) ≫ Sigma.ι (tR aa) bb.1
    let rR (aa : A × A) [HasCoproduct (sR aa)]
        [HasCoproduct (tR aa)] : (∐ sR aa) ⟶ ∐ tR aa :=
      Sigma.desc fun bb ↦ r₁ (aa, bb) ≫ Sigma.ι (tR aa) bb.2
    ∀ [∀ a, HasCoproduct (sT a)] [∀ a, HasCoproduct (tT a)]
      [∀ a, HasCoequalizer (lT a) (rT a)]
      [∀ aa, HasCoproduct (sR aa)] [∀ aa, HasCoproduct (tR aa)]
      [∀ aa, HasCoequalizer (lR aa) (rR aa)],
      let KT : A → V := fun a ↦ coequalizer (lT a) (rT a)
      let jT : ∀ a b, T (a, b) ⟶ KT a := fun a b ↦
        Sigma.ι (tT a) b ≫ coequalizer.π (lT a) (rT a)
      let KR : A × A → V := fun aa ↦ coequalizer (lR aa) (rR aa)
      ∀ (h₀ : ∀ aa bb,
          (r₀ (aa, bb) ≫ a₀ (aa, bb.1)) ≫ jT aa.1 bb.1 =
            (r₁ (aa, bb) ≫ a₀ (aa, bb.2)) ≫ jT aa.1 bb.2)
        (h₁ : ∀ aa bb,
          (r₀ (aa, bb) ≫ a₁ (aa, bb.1)) ≫ jT aa.2 bb.1 =
            (r₁ (aa, bb) ≫ a₁ (aa, bb.2)) ≫ jT aa.2 bb.2),
        let ā₀ : ∀ aa, KR aa ⟶ KT aa.1 := fun aa ↦
          coequalizer.desc
            (Sigma.desc fun b ↦ a₀ (aa, b) ≫ jT aa.1 b) (by
              apply Sigma.hom_ext
              intro bb
              simpa [lR, rR, Category.assoc] using h₀ aa bb)
        let ā₁ : ∀ aa, KR aa ⟶ KT aa.2 := fun aa ↦
          coequalizer.desc
            (Sigma.desc fun b ↦ a₁ (aa, b) ≫ jT aa.2 b) (by
              apply Sigma.hom_ext
              intro bb
              simpa [lR, rR, Category.assoc] using h₁ aa bb)
        let outerL [HasCoproduct KR] [HasCoproduct KT] :
            (∐ KR) ⟶ ∐ KT :=
          Sigma.desc fun aa ↦ ā₀ aa ≫ Sigma.ι KT aa.1
        let outerR [HasCoproduct KR] [HasCoproduct KT] :
            (∐ KR) ⟶ ∐ KT :=
          Sigma.desc fun aa ↦ ā₁ aa ≫ Sigma.ι KT aa.2
        let rel := Sum ((A × A) × B) (A × (B × B))
        let simSource : rel → V := Sum.elim R BT
        let simTarget : A × B → V := T
        let simL [HasCoproduct simSource] [HasCoproduct simTarget] :
            (∐ simSource) ⟶ ∐ simTarget :=
          Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
            (fun p => a₀ p ≫ Sigma.ι simTarget (p.1.1, p.2))
            (fun p => b₀ p ≫ Sigma.ι simTarget (p.1, p.2.1)))
        let simR [HasCoproduct simSource] [HasCoproduct simTarget] :
            (∐ simSource) ⟶ ∐ simTarget :=
          Sigma.desc (Sum.rec (motive := fun r : rel => simSource r ⟶ ∐ simTarget)
            (fun p => a₁ p ≫ Sigma.ι simTarget (p.1.2, p.2))
            (fun p => b₁ p ≫ Sigma.ι simTarget (p.1, p.2.2)))
        ∀ [HasCoproduct KR] [HasCoproduct KT]
          [HasCoequalizer outerL outerR]
          [HasCoproduct simSource] [HasCoproduct simTarget]
          [HasCoequalizer simL simR],
          let e := fubiniIso T BT b₀ b₁ R BR r₀ r₁ a₀ a₁ h₀ h₁
          ∀ a b,
            ((jT a b ≫ (Sigma.ι KT a ≫ coequalizer.π outerL outerR)) ≫ e.hom =
                Sigma.ι simTarget (a, b) ≫ coequalizer.π simL simR) ∧
              ((Sigma.ι simTarget (a, b) ≫ coequalizer.π simL simR) ≫ e.inv =
                jT a b ≫ (Sigma.ι KT a ≫ coequalizer.π outerL outerR)) := by
  dsimp only
  intro _ _ _ _ _ _ h₀ h₁ _ _ _ _ _ _ a b
  constructor
  · dsimp only [fubiniIso, id]
    simp only [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
  · dsimp only [fubiniIso, id]
    simp only [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

end Fubini

end weightedCoend

end EnrichedSource

end CategoryTheory.Enriched
