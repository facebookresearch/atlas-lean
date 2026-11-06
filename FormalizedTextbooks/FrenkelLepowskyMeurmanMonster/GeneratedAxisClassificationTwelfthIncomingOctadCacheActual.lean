/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingOctadCachePacket11

/-! The complete packed source cache equals every actual original incoming octad lookup. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

private theorem all_packets (k : Fin 12) (u : Fin 4096) :
    if h : k.val * 4096 + u.val < 48576 then
      generatedTwelfthIncomingOctadCache
        ⟨(k.val * 4096 + u.val) / 64, by omega⟩
        ⟨(k.val * 4096 + u.val) % 64, Nat.mod_lt _ (by decide)⟩ =
      generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inl
        (⟨(k.val * 4096 + u.val) / 64, by omega⟩,
          ⟨(k.val * 4096 + u.val) % 64, Nat.mod_lt _ (by decide)⟩))) else True := by
  fin_cases k
  · exact generatedTwelfth_incoming_octad_cache_packet_00 u
  · exact generatedTwelfth_incoming_octad_cache_packet_01 u
  · exact generatedTwelfth_incoming_octad_cache_packet_02 u
  · exact generatedTwelfth_incoming_octad_cache_packet_03 u
  · exact generatedTwelfth_incoming_octad_cache_packet_04 u
  · exact generatedTwelfth_incoming_octad_cache_packet_05 u
  · exact generatedTwelfth_incoming_octad_cache_packet_06 u
  · exact generatedTwelfth_incoming_octad_cache_packet_07 u
  · exact generatedTwelfth_incoming_octad_cache_packet_08 u
  · exact generatedTwelfth_incoming_octad_cache_packet_09 u
  · exact generatedTwelfth_incoming_octad_cache_packet_10 u
  · exact generatedTwelfth_incoming_octad_cache_packet_11 u

/-- Every original signed octad coordinate has its exact incoming source value. -/
theorem generatedTwelfth_incoming_octad_cache_actual (o : Fin 759) (e : Fin 64) :
    generatedTwelfthIncomingOctadCache o e =
      generatedTwelfthIncomingShortCoefficient (Sum.inr (Sum.inl (o, e))) := by
  let x := 64 * o.val + e.val
  have hx : x < 48576 := by dsimp only [x]; omega
  let k : Fin 12 := ⟨x / 4096, by omega⟩
  let u : Fin 4096 := ⟨x % 4096, Nat.mod_lt _ (by decide)⟩
  have hh := all_packets k u
  have hr : k.val * 4096 + u.val = x := by dsimp only [k, u]; omega
  have hb : k.val * 4096 + u.val < 48576 := by omega
  rw [dite_eq_left hb] at hh
  have ho : (⟨(k.val * 4096 + u.val) / 64, by omega⟩ : Fin 759) = o := by
    apply Fin.ext
    change (k.val * 4096 + u.val) / 64 = o.val
    dsimp only [x] at hr
    omega
  have he : (⟨(k.val * 4096 + u.val) % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) = e := by
    apply Fin.ext
    change (k.val * 4096 + u.val) % 64 = e.val
    dsimp only [x] at hr
    omega
  simpa only [ho, he] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
