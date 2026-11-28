/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.GreenProblem69

open MathlibExt.Combinatorics.GreenProblem69Wanted

example : SumsetEqUniv 1 (fun _ ↦ cubeOrigin 1) :=
  conjecture_holds 1 (by decide) _ (fun _ ↦ ⟨LinearEquiv.refl _ _, by
    change cubeOrigin 1 = id '' cubeOrigin 1
    rw [Set.image_id]⟩)

private def swap : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) where
  toFun x i := x (1 - i)
  invFun x i := x (1 - i)
  left_inv x := by
    funext i
    have h : ∀ j : Fin 2, 1 - (1 - j) = j := by decide
    exact congrArg x (h i)
  right_inv x := by
    funext i
    have h : ∀ j : Fin 2, 1 - (1 - j) = j := by decide
    exact congrArg x (h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- Translation is not part of `IsCube`. Use an automorphism that actually changes the cube.
private def transform : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
  swap.trans (LinearEquiv.neg (ZMod 3) : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3))

private def labelled (i : Fin 100) : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
  if i.val % 2 = 0 then transform else LinearEquiv.refl _ _

private def cubes (i : Fin 100) : Set (Fin 2 → ZMod 3) := labelled i '' cubeOrigin 2

example : labelled (0 : Fin 100) = labelled 2 := rfl

example : labelled (0 : Fin 100) ≠ labelled 1 := by
  intro h
  have he := congrArg (fun e : (Fin 2 → ZMod 3) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) ↦
    e (fun _ ↦ 1) 0) h
  change (-(1 : ZMod 3)) = 1 at he
  exact (by decide : (-(1 : ZMod 3)) ≠ 1) he

example : SumsetEqUniv 2 cubes := conjecture_holds 2 (by decide) cubes (fun i ↦ ⟨labelled i, rfl⟩)

-- Zero is available in every summand, including those used solely for padding.
example (i : Fin 100) : (0 : Fin 2 → ZMod 3) ∈ cubes i := by
  refine ⟨0, fun j ↦ Or.inl rfl, ?_⟩
  exact map_zero (labelled i)

example : ∃ a : Fin 100 → Fin 2 → ZMod 3,
    (∀ i, a i ∈ cubes i) ∧ (∀ i, 4 ≤ i.val → a i = 0) ∧
      (0 : Fin 2 → ZMod 3) = ∑ i, a i := by
  refine ⟨0, ?_, fun _ _ ↦ rfl, by simp⟩
  intro i
  refine ⟨0, fun j ↦ Or.inl rfl, ?_⟩
  exact map_zero (labelled i)
