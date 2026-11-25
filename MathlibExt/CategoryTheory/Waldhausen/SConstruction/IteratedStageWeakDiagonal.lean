/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageWeakNerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal

/-!
# The original diagonal of the iterated weak S-construction

The diagonal retains every original S-stage direction and the original
nerve direction. A degree n is a chain of n composable original weak maps
in the actual r-fold S_n category. Every original simplex operator acts
on every S direction and on that same original chain. Identity and
composition are the earned multisimplicial and nerve functor laws.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

/-- The genuine diagonal indexing functor repeats the original simplex in every direction. -/
def stageTupleDiagonal (r : ℕ) : SimplexCategoryᵒᵖ ⥤ StageSimplexTuple r where
  obj a := fun _ => a
  map α := fun _ => α
  map_id _ := rfl
  map_comp _ _ := rfl

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- All original stage directions restricted to the original common simplex degree. -/
def iteratedStageWeakDiagonalNerve (r : ℕ) : SimplicialObject SSet.{max u v} :=
  stageTupleDiagonal r ⋙ iteratedStageWeakNerve C r

/-- The genuine complete diagonal also retains the original nerve direction. -/
def iteratedStageWeakDiagonal (r : ℕ) : SSet.{max u v} :=
  SSet.simplicialDiagonalFunctor.obj (iteratedStageWeakDiagonalNerve C r)

/-- Every complete diagonal simplex is an original composable chain at its actual repeated tuple. -/
theorem iteratedStageWeakDiagonal_obj (r : ℕ) (a : SimplexCategoryᵒᵖ) :
    (iteratedStageWeakDiagonal C r).obj a =
      (CategoryTheory.nerve (IteratedStageWeakAtTuple C (fun _ : Fin r => a))).obj a :=
  rfl

/-- Every complete simplex operator is the original tuple reindex map followed
by the original nerve-chain simplex operator. -/
theorem iteratedStageWeakDiagonal_map {r : ℕ} {a b : SimplexCategoryᵒᵖ} (α : a ⟶ b) :
    (iteratedStageWeakDiagonal C r).map α =
      (CategoryTheory.nerve (IteratedStageWeakAtTuple C (fun _ : Fin r => a))).map α ≫
        (CategoryTheory.nerveMap (reindexIteratedStageWeak C (fun _ : Fin r => α))).app b :=
  SSet.simplicialDiagonalFunctor_obj_map (iteratedStageWeakDiagonalNerve C r) α

end CategoryTheory.Waldhausen.SConstruction
