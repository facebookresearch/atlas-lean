/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

/-! The actual extraspecial conjugation character on the source Ω element. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual conjugation phase character at the source Ω base. -/
noncomputable def localOmegaQPhase : Q →* Multiplicative (ZMod 2) :=
  localAxisBinaryPhase (toAdd sourceOmegaQ.base)

/-- Noncentrality of the actual Ω element makes its phase character nontrivial. -/
theorem localOmegaQPhase_nontrivial : ∃ q : Q, localOmegaQPhase q ≠ 1 := by
  by_contra! h
  apply sourceOmegaQ_not_mem_center
  apply Subgroup.mem_center_iff.mpr
  intro q
  apply (q_mul_comm_iff q sourceOmegaQ).mpr
  have hz := congrArg toAdd (h q)
  change qBeta (toAdd q.base) (toAdd sourceOmegaQ.base) +
    qBeta (toAdd sourceOmegaQ.base) (toAdd q.base) = 0 at hz
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hz

/-- Either source Ω conjugation phase is realized by a genuine Q element. -/
theorem localOmegaQPhase_surjective : Function.Surjective localOmegaQPhase := by
  obtain ⟨q, hq⟩ := localOmegaQPhase_nontrivial
  have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hq1 : toAdd (localOmegaQPhase q) = 1 := by
    rcases hbit (toAdd (localOmegaQPhase q)) with h | h
    · exact False.elim (hq (toAdd.injective h))
    · exact h
  intro a
  rcases hbit (toAdd a) with ha | ha
  · exact ⟨1, by rw [map_one]; exact (toAdd.injective ha).symm⟩
  · exact ⟨q, toAdd.injective (hq1.trans ha.symm)⟩

/-- Exactly half of Q centralizes the actual source Ω element. -/
theorem localOmegaQPhase_kernel_card : Nat.card localOmegaQPhase.ker = 2 ^ 24 := by
  have h := localOmegaQPhase.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr localOmegaQPhase_surjective,
    Subgroup.card_top, q_card] at h
  have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [ZMod.card]
  rw [hc] at h
  omega

/-- The actual Ω centralizer inside Q is exactly the phase kernel. -/
theorem localOmegaQPhase_kernel_eq_centralizer :
    localOmegaQPhase.ker = Subgroup.centralizer {sourceOmegaQ} := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff, q_mul_comm_iff]
  change ofAdd (qBeta (toAdd q.base) (toAdd sourceOmegaQ.base) +
    qBeta (toAdd sourceOmegaQ.base) (toAdd q.base)) = 1 ↔ _
  rw [← ofAdd_zero, ofAdd.injective.eq_iff]
  exact ⟨fun h => by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h,
    fun h => by rw [h]; exact CharTwo.add_self_eq_zero _⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
