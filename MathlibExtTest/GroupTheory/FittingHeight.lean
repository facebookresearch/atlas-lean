/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.ZMod.Basic
import MathlibExt.GroupTheory.FittingHeight

open MathlibExt.GroupTheory.KourovkaNotebookShared

example : FittingHeightLE PUnit.{1} 0 := by
  exact ⟨fun _ ↦ ⊥, rfl, Subsingleton.elim _ _, fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩

example : FittingHeightLE (Multiplicative (ZMod 2)) 1 := by
  refine ⟨fun i ↦ if i = 0 then ⊥ else ⊤, rfl, rfl, ?_⟩
  intro i hi
  obtain rfl := Nat.lt_one_iff.mp hi
  obtain ⟨c, hc⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries
    (G := Multiplicative (ZMod 2))).mp inferInstance
  exact ⟨inferInstance, bot_le, c, hc.le⟩

example : ¬ FittingHeightLE (Multiplicative (ZMod 2)) 0 := by
  rintro ⟨s, hbot, htop, _⟩
  exact bot_ne_top (hbot.symm.trans htop)
