/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQKernelUpper
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQRootFixed
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightLocalProjection

/-! The entire original root-eight extraspecial kernel has exactly two actual elements. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The identity and the genuine whole-axis root operator are distinct actual Q fixers. -/
theorem generatedFifthRootEight_axis_Q_kernel_lower_two :
    2 ≤ Nat.card generatedFifthRootEightAxisQStabilizer := by
  let f : Bool → generatedFifthRootEightAxisQStabilizer := fun b =>
    if b then ⟨generatedFifthRootEightRootQ, generatedFifthRootEight_root_Q_fixed⟩ else 1
  have hf : Function.Injective f := by
    intro b c h
    cases b <;> cases c
    · rfl
    · have he := congrArg Subtype.val h
      exact False.elim (generatedFifthRootEight_root_Q_ne_one he.symm)
    · have he := congrArg Subtype.val h
      exact False.elim (generatedFifthRootEight_root_Q_ne_one he)
    · rfl
  have h := Nat.card_le_card_of_injective f hf
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

/-- All original full-axis extraspecial fixers are accounted for by the two-element kernel. -/
theorem generatedFifthRootEight_axis_Q_stabilizer_card :
    Nat.card generatedFifthRootEightAxisQStabilizer = 2 :=
  Nat.le_antisymm generatedFifthRootEight_axis_Q_kernel_upper_two
    generatedFifthRootEight_axis_Q_kernel_lower_two

/-- The whole genuine local stabilizer is twice its actually attained Conway projection. -/
theorem generatedFifthRootEight_local_stabilizer_card_twice_range :
    Nat.card generatedFifthRootEightLocalAxisStabilizer =
      2 * Nat.card generatedFifthRootEightProjectedAxisStabilizer := by
  rw [generatedFifthRootEight_local_stabilizer_card_Q_mul_range,
    generatedFifthRootEight_axis_Q_stabilizer_card]

/-- The required full local order is exactly the required attained Conway-image order. -/
theorem generatedFifthRootEight_local_order_iff_projected_order :
    Nat.card generatedFifthRootEightLocalAxisStabilizer = 177408000 ↔
      Nat.card generatedFifthRootEightProjectedAxisStabilizer = 88704000 := by
  rw [generatedFifthRootEight_local_stabilizer_card_twice_range]
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
