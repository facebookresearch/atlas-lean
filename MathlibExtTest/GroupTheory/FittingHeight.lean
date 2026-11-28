/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.ZGroup
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

example : FittingHeightLE (Equiv.Perm (Fin 3)) 2 := by
  let s : ℕ → Subgroup (Equiv.Perm (Fin 3))
    | 0 => ⊥
    | 1 => alternatingGroup (Fin 3)
    | _ + 2 => ⊤
  refine ⟨s, rfl, rfl, ?_⟩
  intro i hi
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · refine ⟨inferInstance, bot_le, 1, ?_⟩
    exact (Subgroup.commutator_self_eq_bot_iff.mpr
      (alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp))).le
  · exact ⟨inferInstance, le_top, 1, alternatingGroup.commutator_perm_le⟩

example : ¬ FittingHeightLE (Equiv.Perm (Fin 3)) 1 := by
  rintro ⟨s, hbot, htop, hstep⟩
  obtain ⟨c, hc⟩ := (hstep 0 Nat.zero_lt_one).2.2
  rw [Nat.zero_add, htop, hbot] at hc
  have : Group.IsNilpotent (Equiv.Perm (Fin 3)) :=
    Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c, le_bot_iff.mp hc⟩
  have : IsZGroup (Equiv.Perm (Fin 3)) := IsZGroup.of_squarefree (by
    rw [Nat.card_perm, Nat.card_fin]
    exact (Nat.squarefree_mul (m := 2) (n := 3) (by decide)).mpr
      ⟨Nat.squarefree_two, Nat.prime_three.prime.squarefree⟩)
  have hcard := (Equiv.Perm.isCyclic_iff_card_le_two (α := Fin 3)).mp inferInstance
  simp at hcard
