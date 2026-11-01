/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCachePacket07

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem all_labels : ∀ d : Fin 2048,
    generatedTwelfthGolayMaskCache d = golayEncodedMask d.val ∧
      generatedTwelfthGolayPhaseCache d =
        nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  have h : ∀ (b : Fin 8) (u : Fin 256),
      let d : Fin 2048 := ⟨b.val * 256 + u.val, by omega⟩
      generatedTwelfthGolayMaskCache d = golayEncodedMask d.val ∧
        generatedTwelfthGolayPhaseCache d =
          nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
    intro b u
    fin_cases b
    · exact generatedTwelfth_golay_mask_cache_packet_00 u
    · exact generatedTwelfth_golay_mask_cache_packet_01 u
    · exact generatedTwelfth_golay_mask_cache_packet_02 u
    · exact generatedTwelfth_golay_mask_cache_packet_03 u
    · exact generatedTwelfth_golay_mask_cache_packet_04 u
    · exact generatedTwelfth_golay_mask_cache_packet_05 u
    · exact generatedTwelfth_golay_mask_cache_packet_06 u
    · exact generatedTwelfth_golay_mask_cache_packet_07 u
  intro d
  let b : Fin 8 := ⟨d.val / 256, by omega⟩
  let u : Fin 256 := ⟨d.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 2048) = d := by
    apply Fin.ext
    dsimp [b, u]
    omega
  exact Eq.mp (congrArg (fun q : Fin 2048 =>
    generatedTwelfthGolayMaskCache q = golayEncodedMask q.val ∧
      generatedTwelfthGolayPhaseCache q =
        nortonUIntegerSign (golayMaskWeight (golayEncodedMask q.val) / 4 : ℕ)) he) (h b u)

/-- Every original odd-label codeword agrees in all twenty-four bits. -/
theorem generatedTwelfth_golay_mask_cache_actual (d : Fin 2048) :
    generatedTwelfthGolayMaskCache d = golayEncodedMask d.val := (all_labels d).1

/-- Every original odd-label Parker weight sign agrees exactly. -/
theorem generatedTwelfth_golay_phase_cache_actual (d : Fin 2048) :
    generatedTwelfthGolayPhaseCache d =
      nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := (all_labels d).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
