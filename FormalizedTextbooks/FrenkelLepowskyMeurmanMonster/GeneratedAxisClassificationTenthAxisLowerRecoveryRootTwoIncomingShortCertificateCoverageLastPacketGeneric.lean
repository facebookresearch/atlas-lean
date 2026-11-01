/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Exact final packet coverage, with no omitted or padded source rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Two Fin 16 blocks and one Fin 8 block cover every original Fin 40 address. -/
theorem generatedTenth_root_two_coverage_last_packet_cover (p : Fin 40 → Prop)
    (h0 : ∀ u : Fin 16, p ⟨u.val, by omega⟩)
    (h1 : ∀ u : Fin 16, p ⟨16 + u.val, by omega⟩)
    (h2 : ∀ u : Fin 8, p ⟨32 + u.val, by omega⟩)
    (n : Fin 40) : p n := by
  by_cases hn0 : n.val < 16
  · let u : Fin 16 := ⟨n.val, hn0⟩
    have hn : (⟨u.val, by omega⟩ : Fin 40) = n := by
      apply Fin.ext
      rfl
    simpa only [hn] using h0 u
  · by_cases hn1 : n.val < 32
    · let u : Fin 16 := ⟨n.val - 16, by omega⟩
      have hn : (⟨16 + u.val, by omega⟩ : Fin 40) = n := by
        apply Fin.ext
        dsimp only [u]
        omega
      simpa only [hn] using h1 u
    · let u : Fin 8 := ⟨n.val - 32, by omega⟩
      have hn : (⟨32 + u.val, by omega⟩ : Fin 40) = n := by
        apply Fin.ext
        dsimp only [u]
        omega
      simpa only [hn] using h2 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
