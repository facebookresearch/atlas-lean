/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.BinaryTreeAddressLaw

/-!
# Binary tree address law tests

Root, two-address, and shifted-cylinder instances.
-/

@[expose] public section

open scoped ENNReal
open Cslib.Language.BinaryTreeAddressLaw

/-- at `p = 1/2` the root branches with mass `1/2`. -/
theorem test_law_half_root_branch :
    law (1 / 2) (by norm_num) (by norm_num) (branchAt []) = ENNReal.ofReal (1 / 2) := by
  exact law_root_branch (by norm_num) (by norm_num)

/-- root and left child both branch at `p = 1/2`. -/
theorem test_law_half_two_branch :
    law (1 / 2) (by norm_num) (by norm_num) (cylinder {[], [false]} (fun _ => true)) =
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 2) := by
  have hne : ([] : List Bool) ≠ [false] := by simp
  rw [law_cylinder (by norm_num) (by norm_num)]
  simp [cylinder_mass, Finset.prod_pair hne]

/-- root branches and right child is a leaf at general `p`. -/
theorem test_law_root_branch_right_leaf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 (cylinder {[], [true]} (fun a => a.isEmpty)) =
      ENNReal.ofReal p * ENNReal.ofReal (1 - p) := by
  have hne : ([] : List Bool) ≠ [true] := by simp
  rw [law_cylinder hp0 hp1]
  simp [cylinder_mass, Finset.prod_pair hne]

/-- the branch event below the left shift is the branch
event at the left-child address, with the root mass. -/
theorem test_law_shiftLeft_preimage_root_branch {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 (shiftLeft ⁻¹' branchAt []) = ENNReal.ofReal p := by
  have hinv := law_shift_preimage hp0 hp1 [false] (measurableSet_branchAt [])
  unfold shiftLeft
  unfold shiftLeft at hinv
  rw [hinv, branchAt_eq_cylinder, law_cylinder hp0 hp1, cylinder_mass_singleton]
  simp
