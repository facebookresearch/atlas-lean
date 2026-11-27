/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorLeftGeneral
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorRightGeneral

/-!
# Associator Comparison Unit

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uE uK uM uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorComparisonUnit

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]

section Generic

variable {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {K : Type uK} [EnrichedCategory V K]
  {M : Type uM} [EnrichedCategory V M]

attribute [local instance] Enriched.prodCategory

section Left

variable (T : EnrichedFunctor V (C × D) K) (U : EnrichedFunctor V (K × E) M)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V)
  (X : (C × D) × E)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]
  [HasCoproduct (AssociatorLeftGeneral.objects T U F G H ((AssociatorLeftGeneral.flatIndex T U).obj
    X))]
  [HasCoproduct (AssociatorLeftGeneral.relations T U F G H ((AssociatorLeftGeneral.flatIndex T
    U).obj X))]
  [HasCoequalizer
    (AssociatorLeftGeneral.map0 T U F G H ((AssociatorLeftGeneral.flatIndex T U).obj X))
    (AssociatorLeftGeneral.map1 T U F G H ((AssociatorLeftGeneral.flatIndex T U).obj X))]
  [HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H
    ((AssociatorLeftGeneral.flatIndex T U).obj X))]
  [HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H
    ((AssociatorLeftGeneral.flatIndex T U).obj X))]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap U (Output.functor T F G) H
      ((AssociatorLeftGeneral.flatIndex T U).obj X))
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H
      ((AssociatorLeftGeneral.flatIndex T U).obj X))]

/- These three instances retain the supplied choices at the definitionally identical output. -/
local instance leftOuterObjectsAtUnit : HasCoproduct (EnrichedDayKernel.objects U
    (Output.functor T F G) H (U.obj (T.obj X.1, X.2))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.objects U (Output.functor T F G) H
    ((AssociatorLeftGeneral.flatIndex T U).obj X)))

local instance leftOuterRelationsAtUnit : HasCoproduct (EnrichedDayKernel.relations U
    (Output.functor T F G) H (U.obj (T.obj X.1, X.2))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.relations U (Output.functor T F G) H
    ((AssociatorLeftGeneral.flatIndex T U).obj X)))

local instance leftOuterCoequalizerAtUnit : HasCoequalizer
    (EnrichedDayKernel.leftMap U (Output.functor T F G) H (U.obj (T.obj X.1, X.2)))
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H (U.obj (T.obj X.1, X.2))) :=
  inferInstanceAs (HasCoequalizer
    (EnrichedDayKernel.leftMap U (Output.functor T F G) H ((AssociatorLeftGeneral.flatIndex T U).obj
      X))
    (EnrichedDayKernel.rightMap U (Output.functor T F G) H ((AssociatorLeftGeneral.flatIndex T
      U).obj X)))

/-- The actual generic LEFT comparison keeps the primitive original inner and outer unit generators.
-/
@[reassoc]
theorem left_unitGenerator_flatToNested :
    AssociatorUnit.unitGenerator (AssociatorLeftGeneral.flatIndex T U) (F.externalTensor G) H X ≫
        AssociatorLeftGeneral.flatToNested T U F G H ((AssociatorLeftGeneral.flatIndex T U).obj X) =
      (AssociatorUnit.unitGenerator T F G X.1 ⊗ₘ 𝟙 (H.obj X.2)) ≫
        AssociatorUnit.unitGenerator U (Output.functor T F G) H (T.obj X.1, X.2) := by
  let m := (AssociatorLeftGeneral.flatIndex T U).obj X
  let Q := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let Q' := (Output.functor T F G).obj (T.obj X.1) ⊗ H.obj X.2
  let u : Q ⟶ Q' := AssociatorUnit.unitGenerator T F G X.1 ⊗ₘ 𝟙 (H.obj X.2)
  let g : (m ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj U (Output.functor T F G) H m :=
    EnrichedDayKernel.gen U (Output.functor T F G) H m (T.obj X.1, X.2)
  let i : Q ⟶ AssociatorLeftGeneral.objects T U F G H m X := AssociatorUnit.identityInsert m Q
  let g₀ := AssociatorLeftGeneral.generator T U F G H m X
  let f := AssociatorLeftGeneral.flatToNested T U F G H m
  let w : AssociatorLeftGeneral.objects T U F G H m X ⟶ (m ⟶[V] m) ⊗ Q' :=
    𝟙 (m ⟶[V] m) ⊗ₘ u
  have hf : g₀ ≫ f = w ≫ g := AssociatorLeftGeneral.generator_flatToNested T U F G H m X
  have hi : i ≫ w = u ≫ AssociatorUnit.identityInsert m Q' := by
    have ht := congrArg (fun f => AssociatorUnit.identityInsert m Q ≫ f)
      (id_tensorHom (m ⟶[V] m) u)
    exact ht.trans (AssociatorUnit.identityInsert_naturality m u)
  change (i ≫ g₀) ≫ f = u ≫ (AssociatorUnit.identityInsert m Q' ≫ g)
  calc
    _ = i ≫ (g₀ ≫ f) := Category.assoc i g₀ f
    _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hf
    _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
    _ = (u ≫ AssociatorUnit.identityInsert m Q') ≫ g := congrArg (fun z => z ≫ g) hi
    _ = _ := Category.assoc u (AssociatorUnit.identityInsert m Q') g

end Left

section Right

variable (T : EnrichedFunctor V (D × E) K) (U : EnrichedFunctor V (C × K) M)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (H : EnrichedFunctor V E V)
  (X : (C × D) × E)
  [HasCoproduct (AssociatorRightGeneral.objects T U F G H ((AssociatorRightGeneral.flatIndex T
    U).obj X))]
  [HasCoproduct (AssociatorRightGeneral.relations T U F G H ((AssociatorRightGeneral.flatIndex T
    U).obj X))]
  [HasCoequalizer
    (AssociatorRightGeneral.map0 T U F G H ((AssociatorRightGeneral.flatIndex T U).obj X))
    (AssociatorRightGeneral.map1 T U F G H ((AssociatorRightGeneral.flatIndex T U).obj X))]

/-- Insert the original enriched output identity into the unchanged ordered RIGHT flat generator. -/
abbrev unitFlatR : (AssociatorRightGeneral.coefficients F G H).obj X ⟶
    AssociatorRightGeneral.point T U F G H ((AssociatorRightGeneral.flatIndex T U).obj X) :=
  AssociatorUnit.identityInsert ((AssociatorRightGeneral.flatIndex T U).obj X)
      ((AssociatorRightGeneral.coefficients F G H).obj X) ≫
    AssociatorRightGeneral.generator T U F G H ((AssociatorRightGeneral.flatIndex T U).obj X) X

variable
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T G H k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T G H k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T G H k)
    (EnrichedDayKernel.rightMap T G H k)]
  [HasCoproduct (EnrichedDayKernel.objects U F (Output.functor T G H)
    ((AssociatorRightGeneral.flatIndex T U).obj X))]
  [HasCoproduct (EnrichedDayKernel.relations U F (Output.functor T G H)
    ((AssociatorRightGeneral.flatIndex T U).obj X))]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap U F (Output.functor T G H)
      ((AssociatorRightGeneral.flatIndex T U).obj X))
    (EnrichedDayKernel.rightMap U F (Output.functor T G H)
      ((AssociatorRightGeneral.flatIndex T U).obj X))]

local instance rightOuterObjectsAtUnit : HasCoproduct (EnrichedDayKernel.objects U F
    (Output.functor T G H) (U.obj (X.1.1, T.obj (X.1.2, X.2)))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.objects U F (Output.functor T G H)
    ((AssociatorRightGeneral.flatIndex T U).obj X)))

local instance rightOuterRelationsAtUnit : HasCoproduct (EnrichedDayKernel.relations U F
    (Output.functor T G H) (U.obj (X.1.1, T.obj (X.1.2, X.2)))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.relations U F (Output.functor T G H)
    ((AssociatorRightGeneral.flatIndex T U).obj X)))

local instance rightOuterCoequalizerAtUnit : HasCoequalizer
    (EnrichedDayKernel.leftMap U F (Output.functor T G H) (U.obj (X.1.1, T.obj (X.1.2, X.2))))
    (EnrichedDayKernel.rightMap U F (Output.functor T G H) (U.obj (X.1.1, T.obj (X.1.2, X.2)))) :=
  inferInstanceAs (HasCoequalizer
    (EnrichedDayKernel.leftMap U F (Output.functor T G H) ((AssociatorRightGeneral.flatIndex T
      U).obj X))
    (EnrichedDayKernel.rightMap U F (Output.functor T G H) ((AssociatorRightGeneral.flatIndex T
      U).obj X)))

/-- The actual generic RIGHT comparison keeps the primitive original inner and outer unit
  generators. -/
@[reassoc]
theorem right_unitGenerator_flatToNested :
    unitFlatR T U F G H X ≫
        AssociatorRightGeneral.flatToNested T U F G H ((AssociatorRightGeneral.flatIndex T U).obj X)
          =
      (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator T G H (X.1.2, X.2)) ≫
        AssociatorUnit.unitGenerator U F (Output.functor T G H) (X.1.1, T.obj (X.1.2, X.2)) := by
  let m := (AssociatorRightGeneral.flatIndex T U).obj X
  let Q := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let Q' := F.obj X.1.1 ⊗ (Output.functor T G H).obj (T.obj (X.1.2, X.2))
  let u : Q ⟶ Q' := 𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator T G H (X.1.2, X.2)
  let g : (m ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj U F (Output.functor T G H) m :=
    EnrichedDayKernel.gen U F (Output.functor T G H) m (X.1.1, T.obj (X.1.2, X.2))
  let i : Q ⟶ AssociatorRightGeneral.objects T U F G H m X := AssociatorUnit.identityInsert m Q
  let g₀ := AssociatorRightGeneral.generator T U F G H m X
  let f := AssociatorRightGeneral.flatToNested T U F G H m
  let w : AssociatorRightGeneral.objects T U F G H m X ⟶ (m ⟶[V] m) ⊗ Q' :=
    𝟙 (m ⟶[V] m) ⊗ₘ u
  have hf : g₀ ≫ f = w ≫ g := AssociatorRightGeneral.generator_flatToNested T U F G H m X
  have hi : i ≫ w = u ≫ AssociatorUnit.identityInsert m Q' := by
    have ht := congrArg (fun f => AssociatorUnit.identityInsert m Q ≫ f)
      (id_tensorHom (m ⟶[V] m) u)
    exact ht.trans (AssociatorUnit.identityInsert_naturality m u)
  change (i ≫ g₀) ≫ f = u ≫ (AssociatorUnit.identityInsert m Q' ≫ g)
  calc
    _ = i ≫ (g₀ ≫ f) := Category.assoc i g₀ f
    _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hf
    _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
    _ = (u ≫ AssociatorUnit.identityInsert m Q') ≫ g := congrArg (fun z => z ≫ g) hi
    _ = _ := Category.assoc u (AssociatorUnit.identityInsert m Q') g

end Right
end Generic

section OriginalDay

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)
  (F G H : EnrichedFunctor V I V) (X : (I × I) × I)

attribute [local instance] Enriched.prodCategory

section Left

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]
  [HasCoproduct (AssociatorFlat.leftObjects d F G H ((AssociatorIndex.leftIndex d).obj X))]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H ((AssociatorIndex.leftIndex d).obj X))]
  [HasCoequalizer
    (AssociatorFlat.leftMap0 d F G H ((AssociatorIndex.leftIndex d).obj X))
    (AssociatorFlat.leftMap1 d F G H ((AssociatorIndex.leftIndex d).obj X))]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X))]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X))]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X))]

local instance dayLeftOuterObjectsAtUnit : HasCoproduct (EnrichedDayKernel.objects
  d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H (d.tensorEnrichedFunctor.obj (X.1.1 ⊗ X.1.2,
      X.2))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X)))

local instance dayLeftOuterRelationsAtUnit : HasCoproduct (EnrichedDayKernel.relations
  d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H (d.tensorEnrichedFunctor.obj (X.1.1 ⊗ X.1.2,
      X.2))) :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X)))

local instance dayLeftOuterCoequalizerAtUnit : HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H (d.tensorEnrichedFunctor.obj (X.1.1 ⊗ X.1.2,
        X.2)))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H (d.tensorEnrichedFunctor.obj (X.1.1 ⊗ X.1.2,
        X.2))) :=
  inferInstanceAs (HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H ((AssociatorIndex.leftIndex d).obj X)))

/-- The exact original LEFT Day comparison retains its two primitive nested unit generators. -/
@[reassoc]
theorem day_left_unitGenerator_flatToNested :
    AssociatorUnit.unitGenerator (AssociatorIndex.leftIndex d) (F.externalTensor G) H X ≫
        AssociatorFlattening.flatToNested d F G H ((AssociatorIndex.leftIndex d).obj X) =
      (AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2)) ≫
        AssociatorUnit.unitGenerator d.tensorEnrichedFunctor
          (Output.functor d.tensorEnrichedFunctor F G) H (X.1.1 ⊗ X.1.2, X.2) := by
  let m := (AssociatorIndex.leftIndex d).obj X
  let Q := (F.obj X.1.1 ⊗ G.obj X.1.2) ⊗ H.obj X.2
  let Q' := (Output.functor d.tensorEnrichedFunctor F G).obj (X.1.1 ⊗ X.1.2) ⊗ H.obj X.2
  let u : Q ⟶ Q' := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F G X.1 ⊗ₘ 𝟙 (H.obj X.2)
  let g : (m ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor F G) H m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor F G) H m
      (X.1.1 ⊗ X.1.2, X.2)
  let i : Q ⟶ AssociatorFlat.leftObjects d F G H m X := AssociatorUnit.identityInsert m Q
  let g₀ := AssociatorFlat.leftGenerator d F G H m X
  let f := AssociatorFlattening.flatToNested d F G H m
  let w : AssociatorFlat.leftObjects d F G H m X ⟶ (m ⟶[V] m) ⊗ Q' :=
    𝟙 (m ⟶[V] m) ⊗ₘ u
  have hf : g₀ ≫ f = w ≫ g := AssociatorFlattening.leftGenerator_flatToNested d F G H m X
  have hi : i ≫ w = u ≫ AssociatorUnit.identityInsert m Q' := by
    have ht := congrArg (fun f => AssociatorUnit.identityInsert m Q ≫ f)
      (id_tensorHom (m ⟶[V] m) u)
    exact ht.trans (AssociatorUnit.identityInsert_naturality m u)
  change (i ≫ g₀) ≫ f = u ≫ (AssociatorUnit.identityInsert m Q' ≫ g)
  calc
    _ = i ≫ (g₀ ≫ f) := Category.assoc i g₀ f
    _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hf
    _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
    _ = (u ≫ AssociatorUnit.identityInsert m Q') ≫ g := congrArg (fun z => z ≫ g) hi
    _ = _ := Category.assoc u (AssociatorUnit.identityInsert m Q') g

end Left

section Right

variable
  [HasCoproduct (AssociatorFlat.rightObjects d F G H ((AssociatorIndex.rightIndex d).obj X))]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H ((AssociatorIndex.rightIndex d).obj X))]
  [HasCoequalizer
    (AssociatorFlat.rightMap0 d F G H ((AssociatorIndex.rightIndex d).obj X))
    (AssociatorFlat.rightMap1 d F G H ((AssociatorIndex.rightIndex d).obj X))]

/-- The literal original RIGHT flat identity generator on the unchanged original coend. -/
abbrev dayUnitFlatR : (Associator.rightCoefficients F G H).obj X ⟶
    AssociatorFlat.rightPoint d F G H ((AssociatorIndex.rightIndex d).obj X) :=
  AssociatorUnit.identityInsert ((AssociatorIndex.rightIndex d).obj X)
      ((Associator.rightCoefficients F G H).obj X) ≫
    AssociatorFlat.rightGenerator d F G H ((AssociatorIndex.rightIndex d).obj X) X

variable
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor G H k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor G H k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor G H k)]
  [HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X))]
  [HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X))]
  [HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X))]

local instance dayRightOuterObjectsAtUnit : HasCoproduct (EnrichedDayKernel.objects
  d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) (d.tensorEnrichedFunctor.obj (X.1.1, X.1.2 ⊗ X.2)))
      :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X)))

local instance dayRightOuterRelationsAtUnit : HasCoproduct (EnrichedDayKernel.relations
  d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) (d.tensorEnrichedFunctor.obj (X.1.1, X.1.2 ⊗ X.2)))
      :=
  inferInstanceAs (HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F
    (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X)))

local instance dayRightOuterCoequalizerAtUnit : HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) (d.tensorEnrichedFunctor.obj (X.1.1, X.1.2 ⊗
        X.2)))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) (d.tensorEnrichedFunctor.obj (X.1.1, X.1.2 ⊗
        X.2))) :=
  inferInstanceAs (HasCoequalizer
    (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X))
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) ((AssociatorIndex.rightIndex d).obj X)))

/-- The exact original RIGHT Day comparison retains the primitive nested unit generators. -/
@[reassoc]
theorem day_right_unitGenerator_flatToNested :
    dayUnitFlatR d F G H X ≫
        AssociatorRightFlattening.flatToNested d F G H ((AssociatorIndex.rightIndex d).obj X) =
      (𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H (X.1.2, X.2)) ≫
        AssociatorUnit.unitGenerator d.tensorEnrichedFunctor F
          (Output.functor d.tensorEnrichedFunctor G H) (X.1.1, X.1.2 ⊗ X.2) := by
  let m := (AssociatorIndex.rightIndex d).obj X
  let Q := F.obj X.1.1 ⊗ (G.obj X.1.2 ⊗ H.obj X.2)
  let Q' := F.obj X.1.1 ⊗ (Output.functor d.tensorEnrichedFunctor G H).obj (X.1.2 ⊗ X.2)
  let u : Q ⟶ Q' := 𝟙 (F.obj X.1.1) ⊗ₘ AssociatorUnit.unitGenerator d.tensorEnrichedFunctor G H
    (X.1.2, X.2)
  let g : (m ⟶[V] m) ⊗ Q' ⟶ EnrichedDayKernel.obj d.tensorEnrichedFunctor F
      (Output.functor d.tensorEnrichedFunctor G H) m :=
    EnrichedDayKernel.gen d.tensorEnrichedFunctor F (Output.functor d.tensorEnrichedFunctor G H) m
      (X.1.1, X.1.2 ⊗ X.2)
  let i : Q ⟶ AssociatorFlat.rightObjects d F G H m X := AssociatorUnit.identityInsert m Q
  let g₀ := AssociatorFlat.rightGenerator d F G H m X
  let f := AssociatorRightFlattening.flatToNested d F G H m
  let w : AssociatorFlat.rightObjects d F G H m X ⟶ (m ⟶[V] m) ⊗ Q' :=
    𝟙 (m ⟶[V] m) ⊗ₘ u
  have hf : g₀ ≫ f = w ≫ g := AssociatorRightFlattening.rightGenerator_flatToNested d F G H m X
  have hi : i ≫ w = u ≫ AssociatorUnit.identityInsert m Q' := by
    have ht := congrArg (fun f => AssociatorUnit.identityInsert m Q ≫ f)
      (id_tensorHom (m ⟶[V] m) u)
    exact ht.trans (AssociatorUnit.identityInsert_naturality m u)
  change (i ≫ g₀) ≫ f = u ≫ (AssociatorUnit.identityInsert m Q' ≫ g)
  calc
    _ = i ≫ (g₀ ≫ f) := Category.assoc i g₀ f
    _ = i ≫ (w ≫ g) := congrArg (fun z => i ≫ z) hf
    _ = (i ≫ w) ≫ g := (Category.assoc i w g).symm
    _ = (u ≫ AssociatorUnit.identityInsert m Q') ≫ g := congrArg (fun z => z ≫ g) hi
    _ = _ := Category.assoc u (AssociatorUnit.identityInsert m Q') g

end Right
end OriginalDay
end CategoryTheory.EnrichedDayKernel.AssociatorComparisonUnit
