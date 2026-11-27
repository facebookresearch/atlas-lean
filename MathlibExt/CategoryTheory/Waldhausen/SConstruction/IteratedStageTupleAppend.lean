/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex
public import Mathlib.Data.List.OfFn

/-!
# Appending the original innermost S-direction

Appending an actual simplex to a tuple places that direction at the
innermost end of the original stage-degree list. Original tuple morphisms
and the new simplex morphism give the literal pointwise appended map.
These index computations retain all original directions and support the
subsequent original interval action on the repeated diagonal.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Waldhausen.SConstruction

/-- Append the actual new innermost simplex direction to the original tuple. -/
def stageTupleSnoc {r : ℕ} (a : StageSimplexTuple r) (b : SimplexCategoryᵒᵖ) :
    StageSimplexTuple (r + 1) := Fin.snoc a b

/-- Every prior tuple coefficient is the same original simplex. -/
theorem stageTupleSnoc_castSucc {r : ℕ} (a : StageSimplexTuple r)
    (b : SimplexCategoryᵒᵖ) (i : Fin r) : stageTupleSnoc a b i.castSucc = a i := by
  simp only [stageTupleSnoc, Fin.snoc_castSucc]

/-- The appended coefficient is the actual new innermost simplex. -/
theorem stageTupleSnoc_last {r : ℕ} (a : StageSimplexTuple r) (b : SimplexCategoryᵒᵖ) :
    stageTupleSnoc a b (Fin.last r) = b := by
  simp only [stageTupleSnoc, Fin.snoc_last]

/-- Appending a tuple direction is literal concatenation of the actual stage-degree lists. -/
theorem stageTupleDegrees_snoc {r : ℕ} (a : StageSimplexTuple r) (b : SimplexCategoryᵒᵖ) :
    stageTupleDegrees (stageTupleSnoc a b) = stageTupleDegrees a ++ [b.unop.len] := by
  rw [stageTupleDegrees, List.ofFn_succ']
  simp only [stageTupleSnoc, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    stageTupleDegrees]

/-- The actual appended tuple map transports the original maps through the earned simplex-coordinate
equalities. -/
def stageTupleSnocMap {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) : stageTupleSnoc a x ⟶ stageTupleSnoc b y :=
  Fin.lastCases (motive := fun i => stageTupleSnoc a x i ⟶ stageTupleSnoc b y i)
    (eqToHom (stageTupleSnoc_last a x) ≫ f ≫ eqToHom (stageTupleSnoc_last b y).symm)
    (fun i => eqToHom (stageTupleSnoc_castSucc a x i) ≫ α i ≫
      eqToHom (stageTupleSnoc_castSucc b y i).symm)

/-- In the original prior-direction coordinates the whole appended operator is the original map. -/
theorem stageTupleSnocMap_castSucc {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (i : Fin r) :
    eqToHom (stageTupleSnoc_castSucc a x i).symm ≫ stageTupleSnocMap α f i.castSucc ≫
      eqToHom (stageTupleSnoc_castSucc b y i) = α i := by
  simp [stageTupleSnocMap, Category.assoc]

/-- In the original appended-direction coordinates the whole operator is the new simplex map. -/
theorem stageTupleSnocMap_last {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    eqToHom (stageTupleSnoc_last a x).symm ≫ stageTupleSnocMap α f (Fin.last r) ≫
      eqToHom (stageTupleSnoc_last b y) = f := by
  simp [stageTupleSnocMap, Category.assoc]

/-- Appending the same repeated simplex gives exactly the original successor diagonal tuple. -/
theorem stageTupleSnoc_diagonal (r : ℕ) (a : SimplexCategoryᵒᵖ) :
    stageTupleSnoc (fun _ : Fin r => a) a = fun _ : Fin (r + 1) => a := by
  funext i
  cases i using Fin.lastCases <;> simp [stageTupleSnoc]

end CategoryTheory.Waldhausen.SConstruction
