/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitData

/-! A generic complete coordinate cover assembles bounded incoming tensor certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Sixteen complete blocks cover all original 4096 source coordinates. -/
theorem generatedRootEight_incoming_tensor_coordinate_cover (P : Fin 4096 → Prop)
    (h : ∀ b : Fin 16, ∀ u : Fin 256, P ⟨b.val * 256 + u.val, by omega⟩) :
    ∀ n, P n := by
  intro n
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    change n.val / 256 * 256 + n.val % 256 = n.val
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
