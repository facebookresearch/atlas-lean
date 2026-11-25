/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
import Batteries.Tactic.Lint

/-! # Original generated Quillen frame calculations use the single literal framing core -/

public section
set_option autoImplicit false
noncomputable section
universe wC wD uC uD v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

variable {C : Type uC} [Category.{v} C] [ModelCategory C]
  {D : Type uD} [Category.{v} D] [ModelCategory D]
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (gC : CofibrantGenerationData C κC) (gD : CofibrantGenerationData D κD)
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]

example :
    letI := GeneratedFramingModels.simplicialModel gC
    letI := GeneratedFramingModels.simplicialModel gD
    (a.whiskerRight SimplexCategoryᵒᵖ).IsQuillenAdjunction :=
  QuillenFrameHomComplex.simplicial_isQuillenAdjunction gC gD a

example (Y : D) (n : SimplexCategoryᵒᵖ) :
    ((QuillenFrameHomComplex.imageRightFrame gD (G := R)).obj Y).obj n =
      R.obj (((FunctorialFramings.rightFrame
        (GeneratedFunctorialReplacements.fromGeneration gD)).obj Y).obj n) := rfl

example (Y : D) (n : SimplexCategoryᵒᵖ) :
    ((QuillenFrameHomComplex.imageCoaugmentation gD (G := R)).app Y).app n =
      R.map ((GeneratedFunctorialReplacements.unit gD).app Y ≫
        ((GeneratedFramings.rightResolution gD).app Y).app n) :=
  QuillenFrameHomComplex.imageCoaugmentation_app gD Y n

example {X X' : C} (i : X ⟶ X') [Cofibration i] (Z : C) :
    Fibration (QuillenFrameHomComplex.rightPrecomp i
      ((FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration gC)).obj Z)) :=
  QuillenFrameHomComplex.rightPrecomp_originalFrame_fibration gC i Z

example {X X' : C} (i : X ⟶ X') [Cofibration i] (Z : C) :
    trivialFibrations SSet.{v} (QuillenFrameHomComplex.rightPrecomp i
        ((FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration gC)).obj Z)) ↔
      weakEquivalences SSet.{v} (QuillenFrameHomComplex.rightPrecomp i
        ((FunctorialFramings.rightFrame (GeneratedFunctorialReplacements.fromGeneration gC)).obj Z)) :=
  QuillenFrameHomComplex.rightPrecomp_originalFrame_trivialFibration_iff gC i Z

#print axioms QuillenFrameHomComplex.simplicial_isQuillenAdjunction
#print axioms QuillenFrameHomComplex.imageRightFrame_isFibrant
#print axioms QuillenFrameHomComplex.rightPrecomp_originalFrame_fibration
#print axioms QuillenFrameHomComplex.rightPrecomp_originalFrame_trivialFibration_iff
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
