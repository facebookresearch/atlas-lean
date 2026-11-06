/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorCertificatesGeneric

/-! Exact four-part coverage of the original Fin 256 domain.
All proof bodies remain uncompiled drafts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Four exact Fin 64 quarters cover every original Fin 256 coordinate. -/
theorem generatedTenth_source_delta_spin_quarter_cover (p : Fin 256 → Prop)
    (h : ∀ s : Fin 4, ∀ u : Fin 64, p ⟨64 * s.val + u.val, by omega⟩)
    (n : Fin 256) : p n := by
  let s : Fin 4 := ⟨n.val / 64, by omega⟩
  let u : Fin 64 := ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨64 * s.val + u.val, by omega⟩ : Fin 256) = n := by
    apply Fin.ext
    dsimp only [s, u]
    omega
  simpa only [hn] using h s u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
