/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalOrder

/-! Exactness and the actual octad-axis local stabilizer order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The already counted genuine Q phase stabilizer embeds into the actual H axis stabilizer. -/
def generatedOctadAxisPhaseInclusion (e : Fin 64) (c : ZMod 2) :
    generatedOctadAxisQStabilizer e c →* generatedOctadLocalAxisStabilizer e c :=
  (inclQ.comp (generatedOctadAxisQStabilizer e c).subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- The phase inclusion is genuinely injective in the original local group. -/
theorem generatedOctadAxisPhaseInclusion_injective (e : Fin 64) (c : ZMod 2) :
    Function.Injective (generatedOctadAxisPhaseInclusion e c) := by
  intro q r h
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg Subtype.val h

/-- The actual restricted projection kernel consists exactly of the actual Q phase stabilizer. -/
theorem generatedOctadAxisPhaseInclusion_range (e : Fin 64) (c : ZMod 2) :
    (generatedOctadAxisPhaseInclusion e c).range =
      (generatedOctadLocalAxisProjection e c).ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change projH (inclQ q.val) = 1
    have hq : inclQ q.val ∈ projH.ker := by
      rw [← inclQ_range_eq_projH_ker]
      exact ⟨q.val, rfl⟩
    exact hq
  · intro hk
    have hker : h.val ∈ projH.ker := congrArg Subtype.val hk
    rw [← inclQ_range_eq_projH_ker] at hker
    obtain ⟨q, hq⟩ := hker
    have hphase : q ∈ generatedOctadAxisQStabilizer e c := by
      change inclQ q ∈ generatedOctadLocalAxisStabilizer e c
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The restricted actual local projection has exactly 2^17 kernel elements. -/
theorem generatedOctadLocalAxisProjection_kernel_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadLocalAxisProjection e c).ker = 2 ^ 17 := by
  rw [← generatedOctadAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective (generatedOctadAxisPhaseInclusion_injective e c)).toEquiv
  rw [← h]
  exact generatedOctadAxisQStabilizer_card e c

/-- The octad-image axis has actual local stabilizer order 11689182992793600. -/
theorem generatedOctadLocalAxisStabilizer_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadLocalAxisStabilizer e c) = 11689182992793600 := by
  have h := (generatedOctadLocalAxisProjection e c).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (generatedOctadLocalAxisProjection_surjective e c),
    Subgroup.card_top, generatedOctadLocalAxisProjection_kernel_card,
    generatedAxisE8_co1SectionStabilizer_card] at h
  norm_num at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
