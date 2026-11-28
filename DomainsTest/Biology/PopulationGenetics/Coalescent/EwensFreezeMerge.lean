/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

/-!
# Boundary checks for neutral freeze-and-merge jumps

The empty and singleton samples have unique terminal partitions. For `θ > 0` and two
labels, the terminal probabilities are computed directly from the transition law.
-/

@[expose] public section

noncomputable section

open Finset
open Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

namespace Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

/-- The empty carrier has only its native empty partition. -/
theorem empty_partition_unique (π : Finpartition (univ : Finset (Fin 0))) : π = ⊥ := by
  have hp : π.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr (by simp)
  apply Finpartition.ext
  simp [hp]

/-- The one-label carrier has only its native singleton partition. -/
theorem singleton_partition_unique (π : Finpartition (univ : Finset (Fin 1))) : π = ⊥ := by
  apply π.eq_bot_iff_card_parts_eq_card.mpr
  have hle := π.card_parts_le_card
  have hpos := π.one_le_card_parts_of_nonempty (by simp)
  simpa using Nat.le_antisymm (by simpa using hle) hpos

/-- For `θ > 0`, the empty sample starts and stops at its unique empty partition. -/
theorem terminal_zero (θ : ℝ) (hθ : 0 < θ) :
    terminalLaw θ hθ 0 = PMF.pure ⊥ := by
  simp [terminalLaw, run, PMF.pure_map, initial]

/-- For `θ > 0`, the singleton sample freezes on its first jump, retaining its unique
partition. -/
theorem terminal_one (θ : ℝ) (hθ : 0 < θ) :
    terminalLaw θ hθ 1 = PMF.pure ⊥ := by
  simpa [terminalLaw, run, PMF.pure_bind, initial] using
    step_partition_one θ hθ 1 (initial 1) (initial_active_card 1)

private lemma terminal_two_first (θ : ℝ) (hθ : 0 < θ) :
    terminalLaw θ hθ 2 = (step θ hθ 2 (initial 2)).map State.partition := by
  have hk : 0 < (initial 2).active.card := by rw [initial_active_card]; decide
  simp only [terminalLaw, run, PMF.pure_bind, PMF.map_bind]
  rw [step, dite_eq_left hk, PMF.bind_map]
  have hf : (fun e : Event 2 (initial 2) ↦
      (step θ hθ 2 (applyEvent 2 (initial 2) e)).map State.partition) =
      (fun e ↦ PMF.pure (applyEvent 2 (initial 2) e).partition) := by
    funext e
    apply step_partition_one
    have := applyEvent_active_card 2 (initial 2) e
    rw [initial_active_card] at this
    omega
  rw [Function.comp_def, hf]
  rw [PMF.map_comp]
  rfl

private lemma two_pair_partition
    (p : {p : Finset (Finset (Fin 2)) // p ∈ (initial 2).active.powersetCard 2}) :
    (applyEvent 2 (initial 2) (Sum.inr p)).partition = ⊤ := by
  have hp := (mem_powersetCard.mp p.2).1
  have hc := (mem_powersetCard.mp p.2).2
  have heq : p.1 = (initial 2).active :=
    eq_of_subset_of_card_le hp (by rw [initial_active_card, hc])
  apply (Finpartition.eq_top_iff_card_parts_eq_one _ (by simp)).mpr
  change (insert (p.1.biUnion id) ((initial 2).partition.parts \ p.1)).card = 1
  rw [heq]
  change (insert ((initial 2).active.biUnion id)
    ((initial 2).active \ (initial 2).active)).card = 1
  simp

private lemma two_top_ne_bot :
    (⊤ : Finpartition (univ : Finset (Fin 2))) ≠ ⊥ := by
  intro h
  have hc := (Finpartition.eq_top_iff_card_parts_eq_one
    (⊤ : Finpartition (univ : Finset (Fin 2))) (by simp)).mp rfl
  rw [h] at hc
  simp at hc

private lemma two_freeze_partition (B : (initial 2).active) :
    (applyEvent 2 (initial 2) (Sum.inl B)).partition = ⊥ := rfl

/-- For `θ > 0` and two labels, the merged partition has probability `1/(θ+1)`. -/
theorem terminal_two_merged (θ : ℝ) (hθ : 0 < θ) :
    terminalLaw θ hθ 2 ⊤ = ENNReal.ofReal (1 / (θ + 1)) := by
  classical
  rw [terminal_two_first, step]
  simp only [initial_active_card, Nat.ofNat_pos, dite_eq_left, PMF.map_comp,
    PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [Function.comp_apply]
  simp_rw [two_freeze_partition, two_pair_partition]
  simp only [two_top_ne_bot, ↓reduceIte, sum_const_zero, zero_add, eventLaw_apply,
    eventWeight, sum_const, card_univ, Fintype.card_coe, card_powersetCard,
    initial_active_card]
  norm_num
  congr 1
  unfold denominator
  simp only [Nat.cast_ofNat]
  have heq : θ + 2 - 1 = θ + 1 := by ring
  rw [heq]
  field_simp

/-- For `θ > 0` and two labels, the separate singleton partition has probability
`θ/(θ+1)`. -/
theorem terminal_two_separate (θ : ℝ) (hθ : 0 < θ) :
    terminalLaw θ hθ 2 ⊥ = ENNReal.ofReal (θ / (θ + 1)) := by
  classical
  rw [terminal_two_first, step]
  simp only [initial_active_card, Nat.ofNat_pos, dite_eq_left, PMF.map_comp,
    PMF.map_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [Function.comp_apply]
  simp_rw [two_freeze_partition, two_pair_partition]
  simp only [Ne.symm two_top_ne_bot, ↓reduceIte, sum_const_zero, add_zero,
    eventLaw_apply, eventWeight, sum_const, card_univ, Fintype.card_coe,
    initial_active_card, two_nsmul]
  rw [← ENNReal.ofReal_add (div_nonneg hθ.le (by
    norm_num [denominator]
    linarith)) (div_nonneg hθ.le (by
    norm_num [denominator]
    linarith))]
  congr 1
  unfold denominator
  simp only [Nat.cast_ofNat]
  have heq : θ + 2 - 1 = θ + 1 := by ring
  rw [heq]
  field_simp
  ring

/-- A concrete transition for `θ > 0`: with two active singletons, the specified singleton
freezes with probability `θ/[2(θ+1)]`. -/
theorem two_singleton_freeze (θ : ℝ) (hθ : 0 < θ) :
    step θ hθ 2 (initial 2)
      (freeze 2 (initial 2) ⟨{0}, by simp [initial, Finpartition.parts_bot]⟩) =
      ENNReal.ofReal (θ / (2 * (θ + 1))) := by
  rw [show freeze 2 (initial 2) _ = applyEvent 2 (initial 2) (Sum.inl _) from rfl,
    step_applyEvent θ hθ 2 (initial 2) (by rw [initial_active_card]; decide)]
  congr 1
  simp only [eventWeight, denominator, initial_active_card, Nat.cast_ofNat]
  congr 1
  ring

end Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge
