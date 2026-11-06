/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedData

/-! Bounded finite quantifiers retain every coordinate in each original short packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Four complete 256-coordinate blocks cover every coordinate in a 1,024-coordinate packet. -/
theorem generatedNinth_lower_spin_short_predicate1024_of_blocks (p : Fin 1024 → Prop)
    (h : ∀ b : Fin 4, ∀ u : Fin 256, p ⟨b.val * 256 + u.val, by omega⟩) :
    ∀ n : Fin 1024, p n := by
  intro n
  let b : Fin 4 := ⟨n.val / 256, by omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [b, u]
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
