/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence
public import Batteries.Tactic.Lint
import Lean

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uI

open CategoryTheory MonoidalCategory EnrichedFunctorCat
open scoped MonoidalClosed

namespace MathlibExtTest.EnrichedScalarCoherence

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  (X Y : EnrichedFunctorCat V I) (M N L : V)

example : tensorLeftObject (𝟙_ V) X ≅ X := scalarUnitIso X

example : (scalarUnitIso X).hom ≫ (scalarUnitIso X).inv =
    𝟙 (tensorLeftObject (𝟙_ V) X) := (scalarUnitIso X).hom_inv_id

example : (scalarUnitIso X).inv ≫ (scalarUnitIso X).hom = 𝟙 X :=
  (scalarUnitIso X).inv_hom_id

example (a : I) : component (scalarUnitIso X).hom a =
    (λ_ (X.toEnrichedFunctor.obj a)).hom := scalarUnitIso_hom_component X _

example (a : I) : component (scalarUnitIso X).inv a =
    (λ_ (X.toEnrichedFunctor.obj a)).inv := scalarUnitIso_inv_component X _

example (f : X ⟶ Y) : tensorLeftMap (𝟙_ V) f ≫ (scalarUnitIso Y).hom =
    (scalarUnitIso X).hom ≫ f := scalarUnitIso_naturality f

example : tensorLeftObject (M ⊗ N) X ≅ tensorLeftObject M (tensorLeftObject N X) :=
  scalarAssociatorIso M N X

example : (scalarAssociatorIso M N X).hom ≫ (scalarAssociatorIso M N X).inv =
    𝟙 (tensorLeftObject (M ⊗ N) X) := (scalarAssociatorIso M N X).hom_inv_id

example : (scalarAssociatorIso M N X).inv ≫ (scalarAssociatorIso M N X).hom =
    𝟙 (tensorLeftObject M (tensorLeftObject N X)) := (scalarAssociatorIso M N X).inv_hom_id

example (a : I) : component (scalarAssociatorIso M N X).hom a =
    (α_ M N (X.toEnrichedFunctor.obj a)).hom := scalarAssociatorIso_hom_component M N X _

example (a : I) : component (scalarAssociatorIso M N X).inv a =
    (α_ M N (X.toEnrichedFunctor.obj a)).inv := scalarAssociatorIso_inv_component M N X _

example (f : X ⟶ Y) : tensorLeftMap (M ⊗ N) f ≫ (scalarAssociatorIso M N Y).hom =
    (scalarAssociatorIso M N X).hom ≫ tensorLeftMap M (tensorLeftMap N f) :=
  scalarAssociatorIso_naturality M N f

example {M' : V} (h : M ⟶ M') :
    scalarTensorMap (h ▷ N) X ≫ (scalarAssociatorIso M' N X).hom =
      (scalarAssociatorIso M N X).hom ≫ scalarTensorMap h (tensorLeftObject N X) :=
  scalarAssociatorIso_scalar_left h N X

example {N' : V} (k : N ⟶ N') :
    scalarTensorMap (M ◁ k) X ≫ (scalarAssociatorIso M N' X).hom =
      (scalarAssociatorIso M N X).hom ≫ tensorLeftMap M (scalarTensorMap k X) :=
  scalarAssociatorIso_scalar_right M k X

example : (scalarAssociatorIso M (𝟙_ V) X).hom ≫
    tensorLeftMap M (scalarUnitIso X).hom = scalarTensorMap (ρ_ M).hom X :=
  scalarAssociatorIso_unit_right M X

example : (scalarAssociatorIso (𝟙_ V) M X).hom ≫
    (scalarUnitIso (tensorLeftObject M X)).hom = scalarTensorMap (λ_ M).hom X :=
  scalarAssociatorIso_unit_left M X

example : (scalarAssociatorIso (L ⊗ M) N X).hom ≫
    (scalarAssociatorIso L M (tensorLeftObject N X)).hom =
      scalarTensorMap (α_ L M N).hom X ≫ (scalarAssociatorIso L (M ⊗ N) X).hom ≫
        tensorLeftMap L (scalarAssociatorIso M N X).hom := scalarAssociatorIso_pentagon L M N X

#print axioms CategoryTheory.EnrichedFunctorCat.scalarUnitIso
#print axioms CategoryTheory.EnrichedFunctorCat.scalarUnitIso_hom_component
#print axioms CategoryTheory.EnrichedFunctorCat.scalarUnitIso_inv_component
#print axioms CategoryTheory.EnrichedFunctorCat.scalarUnitIso_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_hom_component
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_inv_component
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_scalar_left
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_scalar_right
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_unit_right
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_unit_left
#print axioms CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_pentagon

/-- The exact thirteen public roots of the genuine scalar action coherence producer. -/
def expectedProducerRoots : Array Lean.Name := #[
  `CategoryTheory.EnrichedFunctorCat.scalarUnitIso,
  `CategoryTheory.EnrichedFunctorCat.scalarUnitIso_hom_component,
  `CategoryTheory.EnrichedFunctorCat.scalarUnitIso_inv_component,
  `CategoryTheory.EnrichedFunctorCat.scalarUnitIso_naturality,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_hom_component,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_inv_component,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_naturality,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_scalar_left,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_scalar_right,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_unit_right,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_unit_left,
  `CategoryTheory.EnrichedFunctorCat.scalarAssociatorIso_pentagon
]

run_cmd do
  let env ← Lean.getEnv
  let producer := `MathlibExt.CategoryTheory.Enriched.ScalarCoherence
  let roots := expectedProducerRoots
  let some idx := env.getModuleIdx? producer | throwError "producer module absent: {producer}"
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if env.getModuleIdxFor? name == some idx then count := count + 1
  unless count > 0 do throwError "zero producer declarations: {producer}"
  for root in roots do
    unless (env.find? root).isSome do throwError "public root absent: {root}"
    unless env.getModuleIdxFor? root == some idx do
      throwError "public root has wrong defining module: {root}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {producer} {root}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {producer} {count} EXPECTED_ROOTS {roots.size}"

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.ScalarCoherence

end MathlibExtTest.EnrichedScalarCoherence
