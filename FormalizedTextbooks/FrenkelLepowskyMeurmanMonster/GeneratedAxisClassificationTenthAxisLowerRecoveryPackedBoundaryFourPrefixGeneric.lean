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

/-- Four exact four-prefix blocks cover every original sixteen-prefix block. -/
theorem generatedTenth_packed_boundary_four_prefix_cover (p : Fin 16 → Prop)
    (h : ∀ b : Fin 4, ∀ u : Fin 4, p ⟨4 * b.val + u.val, by omega⟩)
    (n : Fin 16) : p n := by
  let b : Fin 4 := ⟨n.val / 4, by omega⟩
  let u : Fin 4 := ⟨n.val % 4, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨4 * b.val + u.val, by omega⟩ : Fin 16) = n := by
    apply Fin.ext
    dsimp only [b, u]
    omega
  simpa only [hn] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
