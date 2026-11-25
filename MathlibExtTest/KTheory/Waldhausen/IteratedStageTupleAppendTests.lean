/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageTupleAppend

@[expose] public section
set_option autoImplicit false
open CategoryTheory Opposite
namespace MathlibExtTest.IteratedStageTupleAppend
open CategoryTheory.Waldhausen.SConstruction

/-- The original appended stage direction gives the exact original concatenated list. -/
theorem originalDegrees {r : ℕ} (a : StageSimplexTuple r) (b : SimplexCategoryᵒᵖ) :
    stageTupleDegrees (stageTupleSnoc a b) = stageTupleDegrees a ++ [b.unop.len] :=
  stageTupleDegrees_snoc a b

/-- All original repeated diagonal directions are retained, including the appended last one. -/
theorem originalDiagonal (r : ℕ) (a : SimplexCategoryᵒᵖ) :
    stageTupleSnoc (fun _ : Fin r => a) a = fun _ : Fin (r + 1) => a :=
  stageTupleSnoc_diagonal r a

end MathlibExtTest.IteratedStageTupleAppend
