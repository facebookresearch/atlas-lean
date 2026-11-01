/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightPackets0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightPackets1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightPackets2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientRootEightPackets3

/-! The Root8 local family: at most one actual signed-short axis is orthogonal to the actual
Root8 prototype.

The positive final Root8 axis has matrix numerator over 256 dominating `48 I` and packed short
numerators over 256. The 96 address packets show that every signed-short axis orthogonal to it
is the single pair axis `(Sum.inl (1, 248), 0)`. A genuine local element connects this axis
with the catalogue Root8 prototype, and orthogonal axis counts are local invariants. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The orthogonality check holds at every actual short label. -/
theorem generatedFeasibleAmbient_rootEight_check (r : GriessShortIndex) :
    generatedFeasibleAmbientRootEightCheck r := by
  apply generatedFeasibleAmbient_address_join generatedFeasibleAmbientRootEightCheck _ r
  intro b u
  fin_cases b
  · exact generatedFeasibleAmbient_rootEight_packet_00 u
  · exact generatedFeasibleAmbient_rootEight_packet_01 u
  · exact generatedFeasibleAmbient_rootEight_packet_02 u
  · exact generatedFeasibleAmbient_rootEight_packet_03 u
  · exact generatedFeasibleAmbient_rootEight_packet_04 u
  · exact generatedFeasibleAmbient_rootEight_packet_05 u
  · exact generatedFeasibleAmbient_rootEight_packet_06 u
  · exact generatedFeasibleAmbient_rootEight_packet_07 u
  · exact generatedFeasibleAmbient_rootEight_packet_08 u
  · exact generatedFeasibleAmbient_rootEight_packet_09 u
  · exact generatedFeasibleAmbient_rootEight_packet_10 u
  · exact generatedFeasibleAmbient_rootEight_packet_11 u
  · exact generatedFeasibleAmbient_rootEight_packet_12 u
  · exact generatedFeasibleAmbient_rootEight_packet_13 u
  · exact generatedFeasibleAmbient_rootEight_packet_14 u
  · exact generatedFeasibleAmbient_rootEight_packet_15 u
  · exact generatedFeasibleAmbient_rootEight_packet_16 u
  · exact generatedFeasibleAmbient_rootEight_packet_17 u
  · exact generatedFeasibleAmbient_rootEight_packet_18 u
  · exact generatedFeasibleAmbient_rootEight_packet_19 u
  · exact generatedFeasibleAmbient_rootEight_packet_20 u
  · exact generatedFeasibleAmbient_rootEight_packet_21 u
  · exact generatedFeasibleAmbient_rootEight_packet_22 u
  · exact generatedFeasibleAmbient_rootEight_packet_23 u
  · exact generatedFeasibleAmbient_rootEight_packet_24 u
  · exact generatedFeasibleAmbient_rootEight_packet_25 u
  · exact generatedFeasibleAmbient_rootEight_packet_26 u
  · exact generatedFeasibleAmbient_rootEight_packet_27 u
  · exact generatedFeasibleAmbient_rootEight_packet_28 u
  · exact generatedFeasibleAmbient_rootEight_packet_29 u
  · exact generatedFeasibleAmbient_rootEight_packet_30 u
  · exact generatedFeasibleAmbient_rootEight_packet_31 u
  · exact generatedFeasibleAmbient_rootEight_packet_32 u
  · exact generatedFeasibleAmbient_rootEight_packet_33 u
  · exact generatedFeasibleAmbient_rootEight_packet_34 u
  · exact generatedFeasibleAmbient_rootEight_packet_35 u
  · exact generatedFeasibleAmbient_rootEight_packet_36 u
  · exact generatedFeasibleAmbient_rootEight_packet_37 u
  · exact generatedFeasibleAmbient_rootEight_packet_38 u
  · exact generatedFeasibleAmbient_rootEight_packet_39 u
  · exact generatedFeasibleAmbient_rootEight_packet_40 u
  · exact generatedFeasibleAmbient_rootEight_packet_41 u
  · exact generatedFeasibleAmbient_rootEight_packet_42 u
  · exact generatedFeasibleAmbient_rootEight_packet_43 u
  · exact generatedFeasibleAmbient_rootEight_packet_44 u
  · exact generatedFeasibleAmbient_rootEight_packet_45 u
  · exact generatedFeasibleAmbient_rootEight_packet_46 u
  · exact generatedFeasibleAmbient_rootEight_packet_47 u
  · exact generatedFeasibleAmbient_rootEight_packet_48 u
  · exact generatedFeasibleAmbient_rootEight_packet_49 u
  · exact generatedFeasibleAmbient_rootEight_packet_50 u
  · exact generatedFeasibleAmbient_rootEight_packet_51 u
  · exact generatedFeasibleAmbient_rootEight_packet_52 u
  · exact generatedFeasibleAmbient_rootEight_packet_53 u
  · exact generatedFeasibleAmbient_rootEight_packet_54 u
  · exact generatedFeasibleAmbient_rootEight_packet_55 u
  · exact generatedFeasibleAmbient_rootEight_packet_56 u
  · exact generatedFeasibleAmbient_rootEight_packet_57 u
  · exact generatedFeasibleAmbient_rootEight_packet_58 u
  · exact generatedFeasibleAmbient_rootEight_packet_59 u
  · exact generatedFeasibleAmbient_rootEight_packet_60 u
  · exact generatedFeasibleAmbient_rootEight_packet_61 u
  · exact generatedFeasibleAmbient_rootEight_packet_62 u
  · exact generatedFeasibleAmbient_rootEight_packet_63 u
  · exact generatedFeasibleAmbient_rootEight_packet_64 u
  · exact generatedFeasibleAmbient_rootEight_packet_65 u
  · exact generatedFeasibleAmbient_rootEight_packet_66 u
  · exact generatedFeasibleAmbient_rootEight_packet_67 u
  · exact generatedFeasibleAmbient_rootEight_packet_68 u
  · exact generatedFeasibleAmbient_rootEight_packet_69 u
  · exact generatedFeasibleAmbient_rootEight_packet_70 u
  · exact generatedFeasibleAmbient_rootEight_packet_71 u
  · exact generatedFeasibleAmbient_rootEight_packet_72 u
  · exact generatedFeasibleAmbient_rootEight_packet_73 u
  · exact generatedFeasibleAmbient_rootEight_packet_74 u
  · exact generatedFeasibleAmbient_rootEight_packet_75 u
  · exact generatedFeasibleAmbient_rootEight_packet_76 u
  · exact generatedFeasibleAmbient_rootEight_packet_77 u
  · exact generatedFeasibleAmbient_rootEight_packet_78 u
  · exact generatedFeasibleAmbient_rootEight_packet_79 u
  · exact generatedFeasibleAmbient_rootEight_packet_80 u
  · exact generatedFeasibleAmbient_rootEight_packet_81 u
  · exact generatedFeasibleAmbient_rootEight_packet_82 u
  · exact generatedFeasibleAmbient_rootEight_packet_83 u
  · exact generatedFeasibleAmbient_rootEight_packet_84 u
  · exact generatedFeasibleAmbient_rootEight_packet_85 u
  · exact generatedFeasibleAmbient_rootEight_packet_86 u
  · exact generatedFeasibleAmbient_rootEight_packet_87 u
  · exact generatedFeasibleAmbient_rootEight_packet_88 u
  · exact generatedFeasibleAmbient_rootEight_packet_89 u
  · exact generatedFeasibleAmbient_rootEight_packet_90 u
  · exact generatedFeasibleAmbient_rootEight_packet_91 u
  · exact generatedFeasibleAmbient_rootEight_packet_92 u
  · exact generatedFeasibleAmbient_rootEight_packet_93 u
  · exact generatedFeasibleAmbient_rootEight_packet_94 u
  · exact generatedFeasibleAmbient_rootEight_packet_95 u

private theorem check_forall (r : GriessShortIndex) :
    |generatedRootEightPositiveFinalShortCachedNumerator r| < 48 ∨ ∀ c : ZMod 2,
      ((256 : ℕ) : ℤ) * generatedFeasibleAmbientQuad generatedFeasibleAmbientRootEightN
          (generatedAxisGlobalShortIntegral r) =
        32 * ((256 : ℕ) : ℤ) * generatedFeasibleAmbientSign c *
          generatedRootEightPositiveFinalShortCachedNumerator r →
        (r, c) ∈ generatedFeasibleAmbientRootEightZeroSet := by
  rcases generatedFeasibleAmbient_rootEight_check r with h | ⟨h₀, h₁⟩
  · exact Or.inl h
  · right
    intro c
    fin_cases c
    · exact h₀
    · exact h₁

/-- At most one actual signed-short axis is orthogonal to the positive final Root8 axis. -/
theorem generatedFeasibleAmbientAxisZeroCount_rootEightDestination_le :
    generatedFeasibleAmbientAxisZeroCount
      generatedRootEightIncomingPositiveTrialityDestination ≤ 1 := by
  have h := generatedFeasibleAmbientAxisZeroCount_le_of_subset
    generatedRootEightIncomingPositiveTrialityDestination generatedFeasibleAmbientRootEightZeroSet
    (generatedFeasibleAmbient_zero_mem_of_check _ generatedFeasibleAmbientRootEightN
      generatedRootEightPositiveFinalShortCachedNumerator 256 256 (by norm_num) (by norm_num)
      generatedFeasibleAmbient_rootEight_matrix generatedFeasibleAmbient_rootEight_short 48 48
      generatedFeasibleAmbient_rootEight_quad_ge (by norm_num)
      generatedFeasibleAmbientRootEightZeroSet check_forall)
  simpa [generatedFeasibleAmbientRootEightZeroSet] using h

/-- At most one actual signed-short axis is orthogonal to the catalogue Root8 prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_rootEight_le :
    generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1 := by
  obtain ⟨u, -, hu⟩ := generatedRootEight_incoming_positive_projection_orbit
  rw [hu]
  change generatedFeasibleAmbientAxisZeroCount
    (u • generatedRootEightIncomingPositiveTrialityDestination) ≤ 1
  rw [generatedFeasibleAmbientAxisZeroCount_smul]
  exact generatedFeasibleAmbientAxisZeroCount_rootEightDestination_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
