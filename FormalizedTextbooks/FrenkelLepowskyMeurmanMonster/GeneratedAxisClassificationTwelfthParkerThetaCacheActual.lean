/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCachePacket15

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every original twelve-bit label retains the full original Parker cocode natural mask. -/
theorem generatedTwelfth_parker_theta_cache_actual (d : Fin 4096) :
    generatedTwelfthParkerThetaCache d = parkerThetaMask d.val := by
  have h : ∀ (b : Fin 16) (u : Fin 256),
      let d : Fin 4096 := ⟨b.val * 256 + u.val, by omega⟩
      generatedTwelfthParkerThetaCache d = parkerThetaMask d.val := by
    intro b u
    fin_cases b
    · exact generatedTwelfth_parker_theta_cache_packet_00 u
    · exact generatedTwelfth_parker_theta_cache_packet_01 u
    · exact generatedTwelfth_parker_theta_cache_packet_02 u
    · exact generatedTwelfth_parker_theta_cache_packet_03 u
    · exact generatedTwelfth_parker_theta_cache_packet_04 u
    · exact generatedTwelfth_parker_theta_cache_packet_05 u
    · exact generatedTwelfth_parker_theta_cache_packet_06 u
    · exact generatedTwelfth_parker_theta_cache_packet_07 u
    · exact generatedTwelfth_parker_theta_cache_packet_08 u
    · exact generatedTwelfth_parker_theta_cache_packet_09 u
    · exact generatedTwelfth_parker_theta_cache_packet_10 u
    · exact generatedTwelfth_parker_theta_cache_packet_11 u
    · exact generatedTwelfth_parker_theta_cache_packet_12 u
    · exact generatedTwelfth_parker_theta_cache_packet_13 u
    · exact generatedTwelfth_parker_theta_cache_packet_14 u
    · exact generatedTwelfth_parker_theta_cache_packet_15 u
  let b : Fin 16 := ⟨d.val / 256, by omega⟩
  let u : Fin 256 := ⟨d.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 4096) = d := by
    apply Fin.ext
    dsimp [b, u]
    omega
  exact Eq.mp (congrArg (fun q : Fin 4096 =>
    generatedTwelfthParkerThetaCache q = parkerThetaMask q.val) he) (h b u)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
