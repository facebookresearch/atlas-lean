/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignFixing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSignCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadTransitivity

/-! Transport of the entire actual positive-on-octad Golay sign space. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All original Golay codewords zero on the actual transported E7 octad. -/
def generatedTenthE7OctadSigns : Submodule (ZMod 2) golayCode where
  carrier := {c | ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro c d hc hd i hi
    change c.val i + d.val i = 0
    rw [hc i hi, hd i hi, add_zero]
  smul_mem' := by
    intro a c hc i hi
    change a * c.val i = 0
    rw [hc i hi, mul_zero]

/-- The previously counted standard octad mask is the actual first-eight-coordinate octad. -/
theorem generatedTenth_e7_standard_mask (i : Fin 24) :
    (golayEncodedMask 2063).testBit i.val = true ↔ golayStandardOctad i = 1 := by
  revert i
  decide +kernel

/-- Genuine Golay permutations transport the whole sign space, including every original word. -/
def generatedTenthE7SignSpaceEquiv (p : golayAutomorphismSubgroup)
    (hp : golayPermute p.val generatedTenthE7OctadWord = golayStandardOctad) :
    generatedTenthE7OctadSigns ≃ generatedNinthOctadSignSpace 2063 where
  toFun c := ⟨⟨golayPermute p.val c.val.val, (p.property _).mp c.val.property⟩, by
    intro i hi
    have hstd := (generatedTenth_e7_standard_mask i).mp hi
    have hw : generatedTenthE7OctadWord (p.val.symm i) = 1 := by
      change golayPermute p.val generatedTenthE7OctadWord i = 1
      rw [hp]
      exact hstd
    have ho : p.val.symm i ∈ generatedTenthE7OctadSupport := by
      rw [generatedTenth_e7_octad_coordinates] at hw
      by_contra hn
      simp [hn] at hw
    exact c.property _ ho⟩
  invFun c := ⟨⟨golayPermute p.val⁻¹ c.val.val, ((p⁻¹).property _).mp c.val.property⟩, by
    intro i hi
    have hw : golayStandardOctad (p.val i) = 1 := by
      rw [← hp]
      change generatedTenthE7OctadWord (p.val.symm (p.val i)) = 1
      rw [p.val.symm_apply_apply, generatedTenth_e7_octad_coordinates, ite_eq_left hi]
    exact c.property _ ((generatedTenth_e7_standard_mask _).mpr hw)⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact golayPermute_inv p.val c.val.val
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    change c.val.val (p.val (p.val.symm i)) = c.val.val i
    rw [p.val.apply_symm_apply]

/-- The entire actual Golay-sign subgroup fixing E8 positively has thirty-two words. -/
theorem generatedTenth_e7_octad_sign_space_card : Nat.card generatedTenthE7OctadSigns = 32 := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard generatedTenthE7OctadWord
    generatedTenth_e7_octad_mem_code generatedTenth_e7_octad_weight
  rw [Nat.card_congr (generatedTenthE7SignSpaceEquiv p hp),
    generatedNinth_standard_octad_sign_space_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
