/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationFrameOrbit

/-! Exact original Co0 and Co1 flag stabilizers of the norm-eight frame and orthogonal root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual simultaneous stabilizer of the frame line and preferred target root. -/
def generatedFeasibleOddFrameFlagStabilizer : Subgroup leechIsomSubgroup :=
  generatedNormEightLineStabilizer ⊓ MulAction.stabilizer leechIsomSubgroup
    (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex)

/-- Both genuine central signs fix the frame line and every original preferred root. -/
theorem generatedFeasibleOddFrame_signs_le_flag :
    signsSubgroup ≤ generatedFeasibleOddFrameFlagStabilizer := by
  intro g hg
  refine ⟨generatedNormEight_signs_le_lineStabilizer hg, ?_⟩
  apply griessShortPermutation_binary_trivial
  change g ∈ leechBinaryAction.ker
  rwa [leechBinaryAction_ker]

/-- The genuine simultaneous frame-root stabilizer in the central-sign quotient. -/
def generatedFeasibleOddFrameCo1FlagStabilizer : Subgroup Co1 :=
  generatedFeasibleOddFrameFlagStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- The actual first-root stabilizer inside the original frame-line group has order 82,575,360. -/
theorem generatedFeasibleOddFrame_section_point_stabilizer_card :
    Nat.card (MulAction.stabilizer
      generatedNormEightLineStabilizer
      (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex)) = 82575360 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite
    generatedNormEightLineStabilizer
  let _ := Fintype.ofFinite (MulAction.stabilizer
    generatedNormEightLineStabilizer
    (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex))
  let _ := Fintype.ofFinite (MulAction.orbit
    generatedNormEightLineStabilizer
    (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex))
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedNormEightLineStabilizer
    (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex)
  simp only [← Nat.card_eq_fintype_card] at h
  rw [generatedFeasibleOddFrame_target_orbit, generatedFeasibleOddFrameShortLines_card,
    generatedNormEightLineStabilizer_card] at h
  omega

/-- The genuine simultaneous frame-line and preferred-root stabilizer is the nested point group. -/
def generatedFeasibleOddFrameFlagEquiv : generatedFeasibleOddFrameFlagStabilizer ≃
    MulAction.stabilizer generatedNormEightLineStabilizer
      (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex) where
  toFun g := ⟨⟨g.val, g.property.1⟩, g.property.2⟩
  invFun g := ⟨g.val.val, ⟨g.val.property, g.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full genuine Co0 frame/root flag group has order 82,575,360. -/
theorem generatedFeasibleOddFrame_flag_card :
    Nat.card (generatedFeasibleOddFrameFlagStabilizer) = 82575360 := by
  rw [Nat.card_congr generatedFeasibleOddFrameFlagEquiv,
    generatedFeasibleOddFrame_section_point_stabilizer_card]

/-- The actual central-sign quotient of the genuine outside flag group has order 41,287,680. -/
theorem generatedFeasibleOddFrame_co1_flag_card :
    Nat.card (generatedFeasibleOddFrameCo1FlagStabilizer) = 41287680 := by
  let K := generatedFeasibleOddFrameFlagStabilizer
  have h := K.card_mul_index
  have hindex : K.index = 100702602000 := by
    rw [generatedFeasibleOddFrame_flag_card, co0_card_exact] at h
    omega
  have hquotient : (generatedFeasibleOddFrameCo1FlagStabilizer).index = K.index := by
    change (K.map (QuotientGroup.mk' signsSubgroup)).index = K.index
    exact Subgroup.index_map_eq K (QuotientGroup.mk'_surjective signsSubgroup) (by
      rw [QuotientGroup.ker_mk']
      exact generatedFeasibleOddFrame_signs_le_flag)
  have hq := (generatedFeasibleOddFrameCo1FlagStabilizer).card_mul_index
  rw [hquotient, hindex, co1_card_exact] at hq
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 100702602000)
    (hq.trans (by decide : 4157776806543360000 = 41287680 * 100702602000))


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
