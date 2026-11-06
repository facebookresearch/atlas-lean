/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMasks

/-! Exact mask recognition and distinctness of the genuine intrinsic candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual candidate vectors have exactly the labels selected by their compact span mask. -/
theorem generatedAxisE8FrameCandidateMask_mem_iff (k : Fin 270) (x : Fin 256) :
    (generatedAxisE8FrameCandidateMask k).testBit x.val = true ↔
      generatedAxisE8FrameLabelBits x ∈ generatedAxisE8FrameSystemCandidate k := by
  classical
  let T := {x : Fin 256 // (generatedAxisE8FrameCandidateMask k).testBit x.val = true}
  have hmask (v : generatedAxisE8FrameSystemCandidate k) :
      (generatedAxisE8FrameCandidateMask k).testBit
        (generatedAxisE8FrameLabel v.val).val = true := by
    obtain ⟨a, ha⟩ := v.property
    have he : generatedAxisE8FrameLabel v.val = generatedAxisE8FrameSystemCandidateLabel k a := by
      rw [← ha, generatedAxisE8FrameSystemCandidateMap_bits, generatedAxisE8FrameLabel_left]
    rw [he]
    exact generatedAxisE8FrameCandidateMask_image_certificate k a
  let f : generatedAxisE8FrameSystemCandidate k → T :=
    fun v => ⟨generatedAxisE8FrameLabel v.val, hmask v⟩
  have hinj : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    have hl : generatedAxisE8FrameLabel v.val = generatedAxisE8FrameLabel w.val :=
      congrArg Subtype.val he
    exact generatedAxisE8FrameLabel_right.injective hl
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hinj, (generatedAxisE8FrameSystemCandidate_card k).trans
      (generatedAxisE8FrameCandidateMask_card_certificate k).symm⟩
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hx⟩
    have he : generatedAxisE8FrameLabel v.val = x := congrArg Subtype.val hv
    have hve : v.val = generatedAxisE8FrameLabelBits x := by
      rw [← he, generatedAxisE8FrameLabel_right]
    exact hve ▸ v.property
  · intro hx
    have he := hmask ⟨generatedAxisE8FrameLabelBits x, hx⟩
    rwa [generatedAxisE8FrameLabel_left] at he

/-- Different displayed indices define different actual intrinsic subspaces. -/
theorem generatedAxisE8FrameSystemCandidate_injective :
    Function.Injective generatedAxisE8FrameSystemCandidate := by
  intro k l he
  apply generatedAxisE8FrameCandidateMask_injective
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 256
  · have hb : (generatedAxisE8FrameCandidateMask k).testBit i = true ↔
        (generatedAxisE8FrameCandidateMask l).testBit i = true := by
      rw [generatedAxisE8FrameCandidateMask_mem_iff k ⟨i, hi⟩,
        generatedAxisE8FrameCandidateMask_mem_iff l ⟨i, hi⟩, he]
    exact Bool.eq_iff_iff.mpr hb
  · have hp : 2 ^ 256 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((generatedAxisE8FrameCandidateMask_bound k).trans_le hp),
      Nat.testBit_lt_two_pow ((generatedAxisE8FrameCandidateMask_bound l).trans_le hp)]

/-- The270 displayed intrinsic candidates are genuinely distinct systems. -/
theorem generatedAxisE8IntrinsicFrameSystems_card_lower :
    270 ≤ Nat.card generatedAxisE8IntrinsicFrameSystems := by
  have : Finite (Submodule (ZMod 2) (Fin 8 → ZMod 2)) := inferInstance
  let f : Fin 270 → generatedAxisE8IntrinsicFrameSystems :=
    fun k => ⟨generatedAxisE8FrameSystemCandidate k, generatedAxisE8FrameSystemCandidate_mem k⟩
  have hi : Function.Injective f := by
    intro k l h
    exact generatedAxisE8FrameSystemCandidate_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
