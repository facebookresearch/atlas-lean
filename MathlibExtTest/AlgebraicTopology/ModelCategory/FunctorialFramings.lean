/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
import Batteries.Tactic.Lint

/-! # The shared framing core retains every original generated g/I/cardinal choice -/

public section
noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

example : GeneratedFramings.leftFactor g =
    ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedy
      (GeneratedFramings.leftEndpointArrow g)
      (fun {_ _} f ↦ FramingCoefficientFactory.generatedCofibrant g f) :=
  GeneratedFramings.leftFactor_original g

example : GeneratedFramings.rightFactor g =
    ReedyStructure.DegreeFactorization.classifiedFactor SimplexCategory.reedyOp
      (GeneratedFramings.rightEndpointArrow g)
      (fun {_ _} f ↦ FramingCoefficientFactory.generatedFibrant g f) :=
  GeneratedFramings.rightFactor_original g

example : GeneratedFramings.leftFrame g =
    FunctorialFramings.leftFrame (GeneratedFunctorialReplacements.fromGeneration g) :=
  GeneratedFramings.leftFrame_core g
example : GeneratedFramings.rightFrame g =
    FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration g) :=
  GeneratedFramings.rightFrame_core g

example {X Y : C} (f : X ⟶ Y) :
    (GeneratedFramings.leftFrame g).map f =
      (FunctorialFramings.leftFrame (GeneratedFunctorialReplacements.fromGeneration g)).map f := rfl
example {X Y : C} (f : X ⟶ Y) :
    (GeneratedFramings.rightFrame g).map f =
      (FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration g)).map f := rfl

example (X : C) (n : SimplexCategory) :
    ((GeneratedFramings.augmentation g).app X).app n =
      ((GeneratedFramings.leftResolution g).app X).app n ≫
        (GeneratedFunctorialReplacements.counit g).app X :=
  GeneratedFramings.augmentation_app g X n

example (X : C) (n : SimplexCategoryᵒᵖ) :
    ((GeneratedFramings.coaugmentation g).app X).app n =
      (GeneratedFunctorialReplacements.unit g).app X ≫
        ((GeneratedFramings.rightResolution g).app X).app n :=
  GeneratedFramings.coaugmentation_app g X n

example : IsIso ((GeneratedFramings.leftEndpointArrow g).app ⦋0⦌) := inferInstance
example : IsIso ((GeneratedFramings.rightEndpointArrow g).app (Opposite.op ⦋0⦌)) := inferInstance
example : IsIso ((GeneratedFramings.leftFactor g).p.app ⦋0⦌) := inferInstance
example : IsIso ((GeneratedFramings.rightFactor g).i.app (Opposite.op ⦋0⦌)) := inferInstance

variable (d : GeneratedFunctorialReplacements.Data (C := C))
example (X : C) (n : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      ((FunctorialFramings.leftFrame d).obj X) n) :=
  FunctorialFramings.leftFrame_latching_cofibration d X n
example (Y : C) (n : SimplexCategoryᵒᵖ) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp
      ((FunctorialFramings.rightFrame d).obj Y) n) :=
  FunctorialFramings.rightFrame_matching_fibration d Y n

#print axioms GeneratedFramings.leftFactor_original
#print axioms GeneratedFramings.rightFactor_original
#print axioms FunctorialFramings.leftFactor
#print axioms FunctorialFramings.rightFactor
#print axioms FunctorialFramings.augmentation_weak
#print axioms FunctorialFramings.coaugmentation_weak
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
