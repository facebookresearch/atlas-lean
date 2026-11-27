/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanComparison
import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ScalarComparison
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

noncomputable section

universe uV vV uC uD uK

namespace MathlibExtTest.DayKanScalarComparison

open EnrichedFunctorCat EnrichedDayKernel.LeftKanComparison

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

section DayKan

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) A.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) A.toEnrichedFunctor)]

example : (iso T F G).hom =
    EnrichedDayKernel.ActionFromTransformation.transformation T F G
      (leftKanObject T (externalObject F G)).toEnrichedFunctor
      (leftKanUnit T (externalObject F G)) := rfl

example : (iso T F G).inv =
    leftKanTransposeMap T (externalObject F G) (dayObject T F G)
      (EnrichedDayKernel.Generators.transformation T F G) := rfl

/-- The entire original forward generator family survives through the public Iso. -/
theorem whole_forward_family :
    (fun (k : K) (a : C × D) =>
      EnrichedDayKernel.gen T F G k a ≫ component (iso T F G).hom k) =
    (fun (k : K) (a : C × D) =>
      Enriched.weightedCoend.ι (leftKanWeight T k) (F.externalTensor G) a) := by
  funext k a
  exact gen_toKan T F G k a

/-- The entire original inverse generator family survives through the public Iso. -/
theorem whole_inverse_family :
    (fun (k : K) (a : C × D) =>
      Enriched.weightedCoend.ι (leftKanWeight T k) (F.externalTensor G) a ≫
        component (iso T F G).inv k) =
    (fun (k : K) (a : C × D) => EnrichedDayKernel.gen T F G k a) := by
  funext k a
  exact ι_fromKan T F G k a

example : (iso T F G).hom ≫ (iso T F G).inv = 𝟙 (dayObject T F G) :=
  toKan_fromKan T F G

example : (iso T F G).inv ≫ (iso T F G).hom =
    𝟙 (leftKanObject T (externalObject F G)) := fromKan_toKan T F G

example (k l : K) :
    MonoidalClosed.uncurry ((EnrichedDayKernel.Output.functor T F G).map k l) ≫
        component (iso T F G).hom l =
      (component (iso T F G).hom k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry
          ((leftKanObject T (externalObject F G)).toEnrichedFunctor.map k l) :=
  toKan_full_naturality T F G k l

example (k l : K) :
    MonoidalClosed.uncurry
        ((leftKanObject T (externalObject F G)).toEnrichedFunctor.map k l) ≫
        component (iso T F G).inv l =
      (component (iso T F G).inv k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry ((EnrichedDayKernel.Output.functor T F G).map k l) :=
  fromKan_full_naturality T F G k l

end DayKan

section Scalar

variable (M : V) (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

example :
    (fun a : C × D => component (externalTensorScalarIso M F G).hom a) =
      (fun a : C × D => (α_ M (F.obj a.1) (G.obj a.2)).hom) := by
  funext a
  exact externalTensorScalarIso_hom_component M F G a

example :
    (fun a : C × D => component (externalTensorScalarIso M F G).inv a) =
      (fun a : C × D => (α_ M (F.obj a.1) (G.obj a.2)).inv) := by
  funext a
  exact externalTensorScalarIso_inv_component M F G a

example (a b : C × D) :
    MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b) ≫
        (α_ M (F.obj b.1) (G.obj b.2)).hom =
      ((α_ M (F.obj a.1) (G.obj a.2)).hom ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b) :=
  externalTensorScalar_full_naturality M F G a b

example (a b : C × D) :
    MonoidalClosed.uncurry ((EnrichedFunctor.tensorLeft M (F.externalTensor G)).map a b) ≫
        (α_ M (F.obj b.1) (G.obj b.2)).inv =
      ((α_ M (F.obj a.1) (G.obj a.2)).inv ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (((EnrichedFunctor.tensorLeft M F).externalTensor G).map a b) :=
  externalTensorScalar_inv_full_naturality M F G a b

example {F' : EnrichedFunctor V C V} {G' : EnrichedFunctor V D V}
    (p : (⟨F⟩ : EnrichedFunctorCat V C) ⟶ ⟨F'⟩)
    (q : (⟨G⟩ : EnrichedFunctorCat V D) ⟶ ⟨G'⟩) :
    EnrichedFunctor.externalMap (tensorLeftMap M p) q ≫
        (externalTensorScalarIso M F' G').hom =
      (externalTensorScalarIso M F G).hom ≫
        tensorLeftMap M (F := ⟨F.externalTensor G⟩) (G := ⟨F'.externalTensor G'⟩)
          (EnrichedFunctor.externalMap p q) :=
  externalTensorScalarIso_naturality M p q

example {N : V} (h : M ⟶ N) :
    EnrichedFunctor.externalMap (scalarTensorMap h ⟨F⟩)
        (𝟙 (⟨G⟩ : EnrichedFunctorCat V D)) ≫ (externalTensorScalarIso N F G).hom =
      (externalTensorScalarIso M F G).hom ≫ scalarTensorMap h ⟨F.externalTensor G⟩ :=
  externalTensorScalarIso_scalar_naturality h F G

end Scalar

end MathlibExtTest.DayKanScalarComparison

run_cmd do
  let env ← Lean.getEnv
  for producer in #[`MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanComparison,
      `MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ScalarComparison] do
    let some idx := env.getModuleIdx? producer | throwError "producer module absent: {producer}"
    let mut count : Nat := 0
    for (name, ci) in env.constants do
      if env.getModuleIdxFor? name == some idx then
        if ci.isUnsafe then throwError "unsafe producer declaration: {name}"
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
            throwError "nonstandard axiom at {name}: {ax}"
        Lean.logInfo m!"PRODUCER_STD3 {name} {axioms}"
        count := count + 1
    unless count > 0 do throwError "zero producer declarations: {producer}"
    Lean.logInfo m!"PRODUCER_COUNT {producer} {count}"

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanComparison
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ScalarComparison
