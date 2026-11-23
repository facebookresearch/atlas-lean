/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback

/-! Tests for Kan homotopy pullbacks via mapping path spaces. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open SSet
open SSet.modelCategoryQuillen
open HomotopicalAlgebra

namespace MathlibExtTest.SSet.KanHomotopyPullback

-- Step 1: `eval₀` has boundary RLP.
example (B : SSet.{u}) [KanComplex B] : I.rlp (eval₀ (X := B)) :=
  eval₀_mem_I_rlp

-- Step 2: the mapping-path-space retract and section are weak equivalences.
example (X B : SSet.{u}) (f : X ⟶ B) [KanComplex X] [KanComplex B] :
    KanComplex.W (mappingPathRetract f) :=
  KanComplex.W.of_mappingPathRetract f

example (X B : SSet.{u}) (f : X ⟶ B) [KanComplex X] [KanComplex B] :
    KanComplex.W (mappingPathSection f) :=
  KanComplex.W.of_mappingPathSection f

-- Step 2: the mapping-path-space target is a Kan fibration.
example (X B : SSet.{u}) (f : X ⟶ B) [KanComplex X] [KanComplex B] :
    Fibration (mappingPathTarget f) := inferInstance

-- Step 2: the target factors the original map through the section.
example (X B : SSet.{u}) (f : X ⟶ B) :
    mappingPathSection f ≫ mappingPathTarget f = f :=
  mappingPathSection_comp_target f

-- Step 3: 2-of-3 transfer along a vertex weak equivalence.
example {P₁ P₂ X Y B : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B}
    {u₁ : P₁ ⟶ X} {v₁ : P₁ ⟶ Y} {u₂ : P₂ ⟶ X} {v₂ : P₂ ⟶ Y}
    (sq₁ : CommSq u₁ v₁ f g) (sq₂ : CommSq u₂ v₂ f g)
    (h : P₁ ⟶ P₂) (hu : h ≫ u₂ = u₁) (hv : h ≫ v₂ = v₁)
    (hh : KanComplex.W h) :
    IsKanHomotopyPullback sq₁ ↔ IsKanHomotopyPullback sq₂ :=
  homotopyPullback_twoOfThree sq₁ sq₂ h hu hv hh

-- Step 3: right-leg transfer of weak equivalences.
example {P X Y B : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y}
    (sq : CommSq u v f g) (hpb : IsKanHomotopyPullback sq)
    (hg : KanComplex.W g) : KanComplex.W u :=
  KanComplex.W.of_isKanHomotopyPullback_right sq hpb hg

-- Step 3: strict pullbacks along trivial Kan fibrations are homotopy pullbacks.
example {P X Y B : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex B]
    {f : X ⟶ B} {g : Y ⟶ B} {u : P ⟶ X} {v : P ⟶ Y}
    (sq : IsPullback u v f g) (hg : I.rlp g) :
    IsKanHomotopyPullback sq.toCommSq :=
  isKanHomotopyPullback_of_isPullback_of_rlp_I sq hg

end MathlibExtTest.SSet.KanHomotopyPullback
