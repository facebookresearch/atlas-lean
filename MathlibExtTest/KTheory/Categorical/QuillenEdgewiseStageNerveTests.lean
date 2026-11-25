/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenEdgewiseStageNerve

/-!
# Tests for the outer-edgewise weak-Stage nerve

These tests pin the carrier in outer degrees zero, one, and two; generic face
and degeneracy maps; vertex and edge computations; the simplicial diagonal;
and independent object/morphism universes.  Negative guards ensure that the
carrier module exposes none of the comparison or homotopical statements that
remain separate gates.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenEdgewiseStageNerveTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenEdgewiseStageNerveTestsWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

section Degrees

example :
    (edgewiseStageWeakNerve C).obj (op ⦋0⦌) =
      CategoryTheory.nerve (StageWeakCategory C 1) := by
  simpa using edgewiseStageWeakNerve_obj_op_mk (C := C) 0

example :
    (edgewiseStageWeakNerve C).obj (op ⦋1⦌) =
      CategoryTheory.nerve (StageWeakCategory C 3) := by
  simpa using edgewiseStageWeakNerve_obj_op_mk (C := C) 1

example :
    (edgewiseStageWeakNerve C).obj (op ⦋2⦌) =
      CategoryTheory.nerve (StageWeakCategory C 5) := by
  simpa using edgewiseStageWeakNerve_obj_op_mk (C := C) 2

example :
    (edgewiseStageWeakDiagonal C).obj (op ⦋0⦌) =
      (CategoryTheory.nerve
        (StageWeakCategory C 1)).obj (op ⦋0⦌) := by
  simpa using edgewiseStageWeakDiagonal_obj_op_mk (C := C) 0

example :
    (edgewiseStageWeakDiagonal C).obj (op ⦋1⦌) =
      (CategoryTheory.nerve
        (StageWeakCategory C 3)).obj (op ⦋1⦌) := by
  simpa using edgewiseStageWeakDiagonal_obj_op_mk (C := C) 1

example :
    (edgewiseStageWeakDiagonal C).obj (op ⦋2⦌) =
      (CategoryTheory.nerve
        (StageWeakCategory C 5)).obj (op ⦋2⦌) := by
  simpa using edgewiseStageWeakDiagonal_obj_op_mk (C := C) 2

end Degrees

section Maps

/-- The quantified index exercises every face in every outer degree. -/
example {n : ℕ} (i : Fin (n + 2)) :
    (edgewiseStageWeakNerve C).map (SimplexCategory.δ i).op =
      CategoryTheory.nerveMap
        (edgewiseStageWeakReindex (C := C) (SimplexCategory.δ i)) :=
  edgewiseStageWeakNerve_map_δ (C := C) i

/-- The quantified index exercises every degeneracy in every outer degree. -/
example {n : ℕ} (i : Fin (n + 1)) :
    (edgewiseStageWeakNerve C).map (SimplexCategory.σ i).op =
      CategoryTheory.nerveMap
        (edgewiseStageWeakReindex (C := C) (SimplexCategory.σ i)) :=
  edgewiseStageWeakNerve_map_σ (C := C) i

example {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    (X : StageWeakCategory C (edgewiseQ.obj a.unop).len) :
    ((edgewiseStageWeakNerve C).map f).app (op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀
        ((edgewiseStageWeakReindex (C := C) f.unop).obj X) :=
  edgewiseStageWeakNerve_map_app_mk₀ (C := C) f X

example {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b)
    {X Y : StageWeakCategory C (edgewiseQ.obj a.unop).len}
    (φ : X ⟶ Y) :
    ((edgewiseStageWeakNerve C).map f).app (op ⦋1⦌)
        (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁
        ((edgewiseStageWeakReindex (C := C) f.unop).map φ) :=
  edgewiseStageWeakNerve_map_app_mk₁ (C := C) f φ

example {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (edgewiseStageWeakDiagonal C).map f =
      ↾fun x =>
        (CategoryTheory.nerveMap
          (edgewiseStageWeakReindex (C := C) f.unop)).app b
            ((CategoryTheory.nerve
              (StageWeakCategory C
                (edgewiseQ.obj a.unop).len)).map f x) :=
  edgewiseStageWeakDiagonal_map (C := C) f

end Maps

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example : SimplicialObject SSet.{0} := edgewiseStageWeakNerve C₀
example : SSet.{0} := edgewiseStageWeakDiagonal C₀

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example : SimplicialObject SSet.{1} := edgewiseStageWeakNerve C₁
example : SSet.{1} := edgewiseStageWeakDiagonal C₁

end TypeOne

section MixedObjectSmallMorphLarge

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]

example : SimplicialObject SSet.{1} := edgewiseStageWeakNerve C₀₁
example : SSet.{1} := edgewiseStageWeakDiagonal C₀₁

end MixedObjectSmallMorphLarge

section MixedObjectLargeMorphSmall

variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example : SimplicialObject SSet.{1} := edgewiseStageWeakNerve C₁₀
example : SSet.{1} := edgewiseStageWeakDiagonal C₁₀

end MixedObjectLargeMorphSmall

section NegativeClaims

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridStageProjectionDiagonal

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.outerEdgewiseStageDiagonalComparison

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.edgewiseStageWeakDiagonal_mem_realizationWeakEquivalences

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.edgewiseStageWeakDiagonalBasepoint

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridQSComparison

end NegativeClaims

#print axioms AlgebraicKTheory.edgewiseStageWeakNerve
#print axioms AlgebraicKTheory.edgewiseStageWeakDiagonal

end MathlibExtTest.KTheory.Categorical.QuillenEdgewiseStageNerveTests

end
