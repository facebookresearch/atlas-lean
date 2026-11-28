/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.FreeGroup.Reduce
import MathlibExt.GroupTheory.FinitelyGeneratedBranchGroupsKourovka15Problem14

open scoped Pointwise symmDiff
open MathlibExt.GroupTheory.FinitelyGeneratedBranchGroupsKourovka15Problem14Wanted

example : fgBranchGroupContainingFreeGroup :=
  fgBranchGroupContainingFreeGroup_holds

example : fgBranchGroupOfExponentialGrowth :=
  fgBranchGroupOfExponentialGrowth_holds

-- The witness has growth rate greater than one for an arbitrary finite generating family.
example : ∃ (G : Type) (_ : Group G), Group.FG G ∧ IsBranchGroup G ∧
    ∀ (k : ℕ) (P : Group.Generators G (Fin k)), 1 < growthRate P := by
  obtain ⟨G, hG, hfg, hbranch, _, hgrowth⟩ := fgBranchGroupOfExponentialGrowth_holds
  exact ⟨G, hG, hfg, hbranch, hgrowth⟩

example {m : ℕ → ℕ} {G : Type} [Group G] (ρ : G →* Equiv.Perm (TreeVertex m)) :
    rigidLevelStabilizer ρ 0 = ⊤ := by
  apply top_unique
  intro g _
  apply Subgroup.subset_closure
  let root : TreeVertex m := ⟨[], fun i hi => (Nat.not_lt_zero i hi).elim⟩
  apply Set.mem_iUnion.mpr
  refine ⟨root, Set.mem_iUnion.mpr ⟨rfl, ?_⟩⟩
  intro w hw
  exact (hw List.nil_prefix).elim

private def a : FreeGroup (Fin 2) := FreeGroup.of 0
private def b : FreeGroup (Fin 2) := FreeGroup.of 1

private def ballOne : Finset (FreeGroup (Fin 2)) := {1, a, a⁻¹, b, b⁻¹}

-- Check both branches of left multiplication on reduced words independently of amenability.
example : (a * (a⁻¹ * b)).toWord = [(1, true)] := by decide

example : (a * (b⁻¹ * a)).toWord = [(0, true), (1, false), (0, true)] := by decide

-- Neither generator leaves this concrete finite set almost invariant.
example : ballOne.card = 5 := by decide

example : ((a • ballOne) ∆ ballOne).card = 6 := by decide

example : ((b • ballOne) ∆ ballOne).card = 6 := by decide

example : ¬ IsAmenable (FreeGroup (Fin 2)) :=
  not_isAmenable_of_freeGroupRankTwo_embedding (MonoidHom.id _) Function.injective_id

example : fgNonamenableBranchGroup := fgNonamenableBranchGroup_holds
