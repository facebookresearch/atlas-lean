/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerve

/-!
# Single-set diagonal of the weak-stage nerve

For a Waldhausen category `C`, `stageWeakDiagonal C` is the single `SSet`
diagonal of `stageWeakNerve C`, defined canonically as
`SSet.simplicialDiagonalFunctor.obj (stageWeakNerve C)`. Degree `a`
is the `a`-simplices of the level-`a` nerve; a simplex morphism acts by inner
nerve precomposition followed by the outer weak-reindexing `nerveMap` action.
Identity and composition are inherited from functor composition.

This is a diagonal only. It provides no realization, weak-equivalence theorem,
additivity, K/G-theory, spectrum, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Single-set diagonal of the weak-stage nerve. -/
def stageWeakDiagonal : SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj (stageWeakNerve C)
/-- Object computation: degree `a` is the `a`-simplices of the level-`a` nerve. -/
@[simp]
theorem stageWeakDiagonal_obj (a : SimplexCategoryᵒᵖ) :
    (stageWeakDiagonal C).obj a = ((stageWeakNerve C).obj a).obj a :=
  rfl

/-- Map computation: inner nerve precomposition then outer weak-reindex action. -/
@[simp]
theorem stageWeakDiagonal_map {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (stageWeakDiagonal C).map f =
      ↾fun x =>
        (CategoryTheory.nerveMap (reindexStageWeak C f.unop)).app b
          ((CategoryTheory.nerve (StageWeakCategory C a.unop.len)).map f x) :=
  SSet.simplicialDiagonalFunctor_obj_map (stageWeakNerve C) f

end CategoryTheory.Waldhausen.SConstruction
