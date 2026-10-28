/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificateGenericPackets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortPacketRewriteGeneric

/-! Exact finite coverage split. All new proof bodies are uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Four exact Fin 16 blocks cover every original Fin 64 row address. -/
theorem generatedTenth_root_two_coverage_quarter_cover (p : Fin 64 → Prop)
    (h : ∀ b : Fin 4, ∀ u : Fin 16, p ⟨16 * b.val + u.val, by omega⟩)
    (n : Fin 64) : p n := by
  let b : Fin 4 := ⟨n.val / 16, by omega⟩
  let u : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨16 * b.val + u.val, by omega⟩ : Fin 64) = n := by
    apply Fin.ext
    dsimp only [b, u]
    omega
  simpa only [hn] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
