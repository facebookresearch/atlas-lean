/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from `fairinternal/formal-math/MathlibExtTest/GroupTheory/Permutation/Separation.lean`
at commit `5edfb3b6f668f04b907ff6ca3a98cb0ce1c2eb64`.
Original source SHA-256: 5da7546d79cabfac765384d5a6c3f46e0adf9d257da3f8ae327f6f8410136f6d
-/

module

public import MathlibExt.GroupTheory.Permutation.Separation

@[expose] public section

example (α : Type*) [CircularOrder α] (a b c d : α) :
    MetaMathlibExt.circularSeparates a b c d ↔
      ((sbtw a c b ∧ sbtw b d a) ∨ (sbtw a d b ∧ sbtw b c a)) := by
  rfl

example (α : Type*) [CircularOrder α] (σ : Equiv.Perm α) :
    σ ∈ MetaMathlibExt.separationAutSubgroup α ↔ ∀ a b c d,
      MetaMathlibExt.circularSeparates a b c d ↔
        MetaMathlibExt.circularSeparates (σ a) (σ b) (σ c) (σ d) :=
  MetaMathlibExt.mem_separationAutSubgroup σ

example (α : Type*) [CircularOrder α] :
    (1 : Equiv.Perm α) ∈ MetaMathlibExt.separationAutSubgroup α :=
  Subgroup.one_mem _

example (α : Type*) [CircularOrder α] (σ τ : Equiv.Perm α)
    (hσ : σ ∈ MetaMathlibExt.separationAutSubgroup α)
    (hτ : τ ∈ MetaMathlibExt.separationAutSubgroup α) :
    σ * τ ∈ MetaMathlibExt.separationAutSubgroup α :=
  Subgroup.mul_mem _ hσ hτ

example (α : Type*) [CircularOrder α] (σ : Equiv.Perm α)
    (hσ : σ ∈ MetaMathlibExt.separationAutSubgroup α) :
    σ⁻¹ ∈ MetaMathlibExt.separationAutSubgroup α :=
  Subgroup.inv_mem _ hσ

example (α : Type*) [CircularOrder α] (a c d : α) :
    ¬ MetaMathlibExt.circularSeparates a a c d := by
  intro h
  unfold MetaMathlibExt.circularSeparates at h
  obtain (⟨h, -⟩ | ⟨h, -⟩) := h
  · exact sbtw_irrefl_left_right h
  · exact sbtw_irrefl_left_right h

local instance : CircularOrder ℤ := LinearOrder.toCircularOrder ℤ

example : MetaMathlibExt.circularSeparates (0 : ℤ) 2 1 3 := by
  change
    (((0 : ℤ) < 1 ∧ 1 < 2) ∨ (1 < 2 ∧ 2 < 0) ∨ (2 < 0 ∧ 0 < 1)) ∧
      (((2 : ℤ) < 3 ∧ 3 < 0) ∨ (3 < 0 ∧ 0 < 2) ∨ (0 < 2 ∧ 2 < 3)) ∨
    (((0 : ℤ) < 3 ∧ 3 < 2) ∨ (3 < 2 ∧ 2 < 0) ∨ (2 < 0 ∧ 0 < 3)) ∧
      (((2 : ℤ) < 1 ∧ 1 < 0) ∨ (1 < 0 ∧ 0 < 2) ∨ (0 < 2 ∧ 2 < 1))
  decide

example : ¬ MetaMathlibExt.circularSeparates (0 : ℤ) 1 2 3 := by
  change ¬(
    (((0 : ℤ) < 2 ∧ 2 < 1) ∨ (2 < 1 ∧ 1 < 0) ∨ (1 < 0 ∧ 0 < 2)) ∧
      (((1 : ℤ) < 3 ∧ 3 < 0) ∨ (3 < 0 ∧ 0 < 1) ∨ (0 < 1 ∧ 1 < 3)) ∨
    (((0 : ℤ) < 3 ∧ 3 < 1) ∨ (3 < 1 ∧ 1 < 0) ∨ (1 < 0 ∧ 0 < 3)) ∧
      (((1 : ℤ) < 2 ∧ 2 < 0) ∨ (2 < 0 ∧ 0 < 1) ∨ (0 < 1 ∧ 1 < 2)))
  decide
