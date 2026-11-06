/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryPacketGeneric

/-! Exact complete whole-word boundary partition into sixteen-prefix blocks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Four exact sixteen-prefix blocks cover every original sixty-four-prefix packet. -/
theorem generatedTenth_packed_boundary_quarter_cover (p : Fin 64 → Prop)
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
