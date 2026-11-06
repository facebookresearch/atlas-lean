/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2FrameComplementCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsIncidence

/-! The intrinsic 27-point complement is a genuine carrier of actual norm-eight frame classes.
No generated-orbit or full-axis fixation assertion is assumed here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The finite label predicate is exactly the original intrinsic singularity and polar conditions. -/
theorem leechSeventhE8A2FrameComplementLabels_mem_iff (x : Fin 256) :
    x ∈ leechSeventhE8A2FrameComplementLabels ↔
      generatedAxisE8FrameLabelBits x ≠ 0 ∧
      generatedAxisE8FrameQuadratic (generatedAxisE8FrameLabelBits x) = 0 ∧
      ∀ j, leechSeventhE8A2FramePolar (generatedAxisE8FrameLabelBits x) j = 0 := by
  have hz : generatedAxisE8FrameLabelBits x = 0 ↔ x = 0 := by
    constructor
    · intro h
      apply generatedAxisE8FrameLabelEquiv.injective
      change generatedAxisE8FrameLabelBits x = generatedAxisE8FrameLabelBits 0
      have hzero : generatedAxisE8FrameLabelBits 0 = 0 := by
        ext i
        simp [generatedAxisE8FrameLabelBits]
      exact h.trans hzero.symm
    · rintro rfl
      ext i
      simp [generatedAxisE8FrameLabelBits]
  have hb (i : Fin 8) : x.val.testBit i.val = false ↔ generatedAxisE8FrameLabelBits x i = 0 := by
    cases h : x.val.testBit i.val <;> simp [generatedAxisE8FrameLabelBits, h]
  simp only [leechSeventhE8A2FrameComplementLabels, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hx, h3, h4, hq⟩
    refine ⟨fun h => hx (hz.mp h),
      (generatedAxisE8FrameSingularMask_certificate x).mp hq, ?_⟩
    exact (leechSeventhE8A2FramePolar_zero_iff _).mpr ⟨(hb 3).mp h3, (hb 4).mp h4⟩
  · rintro ⟨hx, hq, hp⟩
    obtain ⟨h3, h4⟩ := (leechSeventhE8A2FramePolar_zero_iff _).mp hp
    exact ⟨fun h => hx (hz.mpr h), (hb 3).mpr h3, (hb 4).mpr h4,
      (generatedAxisE8FrameSingularMask_certificate x).mpr hq⟩

/-- Actual selected-section norm-eight classes in the intrinsic triangle complement. -/
def leechSeventhE8A2FrameComplement : Set LeechModTwo :=
  {b | ∃ a : Fin 8 → ZMod 2, a ≠ 0 ∧ generatedAxisE8FrameQuadratic a = 0 ∧
    (∀ j, leechSeventhE8A2FramePolar a j = 0) ∧ generatedAxisE8FrameRootEmbedding a = b}

/-- Checked finite labels parameterize the entire genuine intrinsic frame-complement carrier. -/
def leechSeventhE8A2FrameComplementEquiv :
    leechSeventhE8A2FrameComplementLabels ≃ leechSeventhE8A2FrameComplement :=
  Equiv.ofBijective (fun x =>
    ⟨generatedAxisE8FrameRootEmbedding (generatedAxisE8FrameLabelBits x.val), by
      obtain ⟨ha, hq, hp⟩ := (leechSeventhE8A2FrameComplementLabels_mem_iff x.val).mp x.property
      exact ⟨generatedAxisE8FrameLabelBits x.val, ha, hq, hp, rfl⟩⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      apply generatedAxisE8FrameLabelEquiv.injective
      exact generatedAxisE8FrameRootEmbedding_injective (congrArg Subtype.val h), by
      rintro ⟨b, a, ha, hq, hp, hab⟩
      let x := generatedAxisE8FrameLabelEquiv.symm a
      have hx : generatedAxisE8FrameLabelBits x = a :=
        generatedAxisE8FrameLabelEquiv.apply_symm_apply a
      have hmem : x ∈ leechSeventhE8A2FrameComplementLabels := by
        apply (leechSeventhE8A2FrameComplementLabels_mem_iff x).mpr
        rw [hx]
        exact ⟨ha, hq, hp⟩
      exact ⟨⟨x, hmem⟩, Subtype.ext
        ((congrArg generatedAxisE8FrameRootEmbedding hx).trans hab)⟩⟩

/-- Exactly 27 genuine norm-eight frame classes have intrinsic complement coordinates. -/
theorem leechSeventhE8A2FrameComplement_card : Nat.card leechSeventhE8A2FrameComplement = 27 := by
  rw [← Nat.card_congr leechSeventhE8A2FrameComplementEquiv, Nat.card_eq_fintype_card,
    Fintype.card_coe, leechSeventhE8A2FrameComplementLabels_card]

/-- Every member is genuinely an incident norm-eight class of the actual selected E8 section. -/
theorem leechSeventhE8A2FrameComplement_subset :
    leechSeventhE8A2FrameComplement ⊆ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  rintro b ⟨a, ha, hq, _, hab⟩
  rw [← hab]
  exact generatedAxisE8Frame_singular_incident a ha hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
