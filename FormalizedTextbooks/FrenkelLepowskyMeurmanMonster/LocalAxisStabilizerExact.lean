/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalOrder

/-! The actual local axis stabilizer exact sequence and its order.
No containment of any global stabilizer in the local group is asserted. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- A Q phase correction makes every lift of a short-class stabilizer fix the axis. -/
theorem localAxisStabilizerProjection_surjective (p : Fin 276) :
    Function.Surjective (localAxisStabilizerProjection p) := by
  intro c
  obtain ⟨h, hh⟩ := projH_surjective c.val
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have hfc : projH (localFiberIntoH f) = c.val := (congrArg projH hf).trans hh
  have hp : griessShortPermutation f.val.2 (Sum.inl (0, p)) = Sum.inl (0, p) := by
    have hc : co1ShortPermutation c.val (Sum.inl (0, p)) = Sum.inl (0, p) := c.property
    rw [← hfc, localAxis_projection_short_mk] at hc
    exact hc
  obtain ⟨q, hq⟩ := localAxisQPhase_surjective (Sum.inl (0, p))
    (ofAdd (localShortPhase f (Sum.inl (0, p))))
  have hphase : localShortPhase (localFiberIncl q * f) (Sum.inl (0, p)) = 0 := by
    rw [localShortPhase_mul, hp, localAxisQPhase_eq_short_phase, hq]
    exact ZModModule.add_self _
  have hperm : griessShortPermutation (localFiberIncl q * f).val.2 (Sum.inl (0, p)) =
      Sum.inl (0, p) := by
    change griessShortPermutation (1 * f.val.2) _ = _
    simpa only [one_mul] using hp
  have hmem : localFiberIntoH (localFiberIncl q * f) ∈ localAxisStabilizer p :=
    (localAxisStabilizer_mk_iff _ p).mpr ⟨hperm, hphase⟩
  refine ⟨⟨localFiberIntoH (localFiberIncl q * f), hmem⟩, Subtype.ext ?_⟩
  change projH (localFiberIntoH (localFiberIncl q * f)) = c.val
  rw [map_mul]
  change projH (inclQ q * localFiberIntoH f) = c.val
  rw [map_mul]
  have hqker : inclQ q ∈ projH.ker := by
    rw [← inclQ_range_eq_projH_ker]
    exact ⟨q, rfl⟩
  rw [show projH (inclQ q) = 1 from hqker, one_mul, hfc]

/-- The actual phase kernel embeds into the actual local axis stabilizer. -/
noncomputable def localAxisPhaseInclusion (p : Fin 276) :
    (localAxisQPhase (Sum.inl (0, p))).ker →* localAxisStabilizer p :=
  (inclQ.comp (localAxisQPhase (Sum.inl (0, p))).ker.subtype).codRestrict _ (by
    intro q
    change q.val ∈ (localAxisStabilizer p).comap inclQ
    rw [localAxisStabilizer_comap_inclQ]
    exact q.property)

/-- The phase-kernel inclusion is genuinely injective. -/
theorem localAxisPhaseInclusion_injective (p : Fin 276) :
    Function.Injective (localAxisPhaseInclusion p) := by
  intro q k h
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg Subtype.val h

/-- Exactness at the actual local axis stabilizer. -/
theorem localAxisPhaseInclusion_range (p : Fin 276) :
    (localAxisPhaseInclusion p).range = (localAxisStabilizerProjection p).ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change projH (inclQ q.val) = 1
    have hq : inclQ q.val ∈ projH.ker := by
      rw [← inclQ_range_eq_projH_ker]
      exact ⟨q.val, rfl⟩
    exact hq
  · intro hker
    have hk : h.val ∈ projH.ker := congrArg Subtype.val hker
    rw [← inclQ_range_eq_projH_ker] at hk
    obtain ⟨q, hq⟩ := hk
    have hphase : q ∈ (localAxisQPhase (Sum.inl (0, p))).ker := by
      rw [← localAxisStabilizer_comap_inclQ]
      change inclQ q ∈ localAxisStabilizer p
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The restricted projection has the actual 2^24-element extraspecial phase kernel. -/
theorem localAxisStabilizerProjection_kernel_card (p : Fin 276) :
    Nat.card (localAxisStabilizerProjection p).ker = 2 ^ 24 := by
  rw [← localAxisPhaseInclusion_range]
  have h := Nat.card_congr (MonoidHom.ofInjective (localAxisPhaseInclusion_injective p)).toEquiv
  rw [← h]
  exact localAxisQPhase_kernel_card (Sum.inl (0, p))

/-- Unconditional cardinality of the actual local axis stabilizer. -/
theorem localAxisStabilizer_card (p : Fin 276) :
    Nat.card (localAxisStabilizer p) =
      2 ^ 24 * Nat.card (co2ShortStabilizer (Sum.inl (0, p))) := by
  have h := (localAxisStabilizerProjection p).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (localAxisStabilizerProjection_surjective p),
    Subgroup.card_top, localAxisStabilizerProjection_kernel_card] at h
  exact h.symm

/-- The conventional local common-axis order, conditional only on the actual Co₁ count. -/
theorem localAxisStabilizer_card_of_co1_card (p : Fin 276)
    (hCo1 : Nat.card Co1 = 4157776806543360000) :
    Nat.card (localAxisStabilizer p) = 2 ^ 24 * 42305421312000 := by
  rw [localAxisStabilizer_card, co2Short_card_of_co1_card _ hCo1]

/-- The actual local pair-axis orbit has index 196560, without a numeric Co₁ assumption. -/
theorem localAxisStabilizer_index (p : Fin 276) :
    (localAxisStabilizer p).index = 196560 := by
  have : Finite Co1 := co1_finite
  have hc : 0 < Nat.card (co2ShortStabilizer (Sum.inl (0, p))) := Nat.card_pos
  have hp : 0 < Nat.card (localAxisStabilizer p) := by
    rw [localAxisStabilizer_card]
    exact Nat.mul_pos (by decide) hc
  have hH : Nat.card H = Nat.card (localAxisStabilizer p) * 196560 := by
    rw [h_card, localAxisStabilizer_card, ← co2Short_card_relation (Sum.inl (0, p))]
    ring
  have h := (localAxisStabilizer p).card_mul_index
  rw [hH] at h
  exact Nat.eq_of_mul_eq_mul_left hp h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
