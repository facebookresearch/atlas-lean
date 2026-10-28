/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesPacket07

/-! All original incoming root-orbit edges, with no coverage premise. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All sixty-two noninitial original root addresses satisfy their entire integer edge. -/
theorem generatedTenth_e7_orbit_edges_actual : ∀ n : Fin 63, n ≠ 0 →
    generatedTenthE7OrbitEdgeCondition n := by
  have hb : ∀ b : Fin 8, ∀ u : Fin 8,
      if hn : b.val * 8 + u.val < 63 then
        if _hi : (⟨b.val * 8 + u.val, hn⟩ : Fin 63) ≠ 0 then
          generatedTenthE7OrbitEdgeCondition ⟨b.val * 8 + u.val, hn⟩
        else True else True := by
    intro b
    fin_cases b
    · exact generatedTenth_e7_orbit_edges_packet_00
    · exact generatedTenth_e7_orbit_edges_packet_01
    · exact generatedTenth_e7_orbit_edges_packet_02
    · exact generatedTenth_e7_orbit_edges_packet_03
    · exact generatedTenth_e7_orbit_edges_packet_04
    · exact generatedTenth_e7_orbit_edges_packet_05
    · exact generatedTenth_e7_orbit_edges_packet_06
    · exact generatedTenth_e7_orbit_edges_packet_07
  intro n hn
  have hc := hb ⟨n.val / 8, by omega⟩ ⟨n.val % 8, Nat.mod_lt _ (by decide)⟩
  have he : n.val / 8 * 8 + n.val % 8 = n.val := by omega
  simpa only [he, dite_eq_left n.isLt, dite_eq_left hn] using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
