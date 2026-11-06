/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleCosets

/-! The genuine second binary phase inside the actual first-axis phase kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual Ω conjugation restricted to the extraspecial elements fixing the first axis. -/
def generatedFeasibleOmegaQPhase (p : Fin 276) :
    (localAxisQPhase (Sum.inl (0, p))).ker →* Multiplicative (ZMod 2) :=
  localOmegaQPhase.comp (localAxisQPhase (Sum.inl (0, p))).ker.subtype

/-- Fixing the first short-axis sign leaves either genuine Ω sign available. -/
theorem generatedFeasibleOmegaQPhase_surjective (p : Fin 276) :
    Function.Surjective (generatedFeasibleOmegaQPhase p) := by
  have hne : localOmegaQPhase ≠ localAxisQPhase (Sum.inl (0, p)) := by
    intro h
    have hb := generatedAxis_binary_phase_injective h.symm
    exact generatedAxis_short_base_ne_omega _ (toAdd.injective hb)
  obtain ⟨q, hshort, hΩ⟩ := generatedAxis_binary_characters_kernel
    (localAxisQPhase (Sum.inl (0, p))) localOmegaQPhase
    (localAxisQPhase_surjective _) localOmegaQPhase_surjective hne
  intro a
  have hbit : toAdd a = 0 ∨ toAdd a = 1 := by
    have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact hc (toAdd a)
  rcases hbit with ha | ha
  · exact ⟨1, (generatedFeasibleOmegaQPhase p).map_one.trans (toAdd.injective ha).symm⟩
  · exact ⟨⟨q, hshort⟩, hΩ.trans (toAdd.injective ha).symm⟩

/-- The actual simultaneous short-axis and Ω phase kernel has order 2²³. -/
theorem generatedFeasibleOmegaQPhase_kernel_card (p : Fin 276) :
    Nat.card (generatedFeasibleOmegaQPhase p).ker = 2 ^ 23 := by
  have h := (generatedFeasibleOmegaQPhase p).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
    (generatedFeasibleOmegaQPhase_surjective p), Subgroup.card_top,
    localAxisQPhase_kernel_card] at h
  have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [ZMod.card]
  rw [hc] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
