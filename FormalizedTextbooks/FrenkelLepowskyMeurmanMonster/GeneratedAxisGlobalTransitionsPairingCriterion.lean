/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm

/-! Whole actual axis comparisons from one complete pairing and finite sparse constituents. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem globalAxis_form_symm (x y : GriessSpace) :
    griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- One exact pairing proves equality of two actual generated translates of the same vector. -/
theorem generatedAxisGlobal_eq_of_preserved_pairing (g h : ↥G) (x : GriessSpace)
    (hc : griessForm (g.val x) (h.val x) = griessForm x x) :
    g.val x = h.val x := by
  apply sub_eq_zero.mp
  apply (griessForm_self_eq_zero_iff _).mp
  simp only [map_sub, LinearMap.sub_apply]
  rw [generated_group_preserves_griessForm, generated_group_preserves_griessForm,
    hc, globalAxis_form_symm (h.val x) (g.val x), hc]
  ring

/-- Pairing a complete sparse real packet uses only its actual finite support entries. -/
theorem generatedAxisGlobal_sparse_pairing {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (X : κ → ℝ) (c : ι → ℝ) (f : ι → κ) :
    (∑ r : κ, X r * (∑ j : ι, c j • Pi.single (f j) (1 : ℝ)) r) =
      ∑ j : ι, c j * X (f j) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (f j)]
  · simp [mul_comm]
  · intro r _ hr
    simp only [Pi.single_eq_of_ne hr, mul_zero]
  · simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
