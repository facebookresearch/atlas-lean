/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Bounded finite quantifiers cover every original spin coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Sixteen complete256-coordinate blocks cover all4096 original source coordinates. -/
theorem generatedNinth_lower_spin_tensor_predicate4096_of_blocks (p : Fin 4096 → Prop)
    (h : ∀ b : Fin 16, ∀ u : Fin 256, p ⟨b.val * 256 + u.val, by omega⟩) :
    ∀ n : Fin 4096, p n := by
  intro n
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, u]
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
