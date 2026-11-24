/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageWeakDiagonal

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.IteratedStageWeakDiagonal

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The genuine diagonal exists for every finite number of original stage directions. -/
def originalIteratedDiagonal (r : ℕ) : SSet.{max u v} := iteratedStageWeakDiagonal C r

/-- Every diagonal degree retains the original weak composable chains. -/
theorem originalIteratedDiagonalObjects (r : ℕ) (a : SimplexCategoryᵒᵖ) :
    (iteratedStageWeakDiagonal C r).obj a =
      (CategoryTheory.nerve (IteratedStageWeakAtTuple C (fun _ : Fin r => a))).obj a :=
  iteratedStageWeakDiagonal_obj C r a

end MathlibExtTest.IteratedStageWeakDiagonal
