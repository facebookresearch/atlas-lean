/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedActual

/-! Exact original sixteen-slot source-word domains and complete prefix coverage. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Four independent leaves cover every original complete source-word prefix. -/
def generatedTenthIncomingBSourceWordCachePrefix (b : Fin 4) (u : Fin 64) : Fin 256 :=
  ⟨64 * b.val + u.val, by omega⟩

/-- Division and remainder retain all 256 original word prefixes without omitting zero slots. -/
theorem generatedTenth_incoming_B_source_word_cache_of_four (p : Fin 256 → Prop)
    (h : ∀ b u, p (generatedTenthIncomingBSourceWordCachePrefix b u)) : ∀ a, p a := by
  intro a
  let b : Fin 4 := ⟨a.val / 64, by omega⟩
  let u : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthIncomingBSourceWordCachePrefix b u = a := by
    apply Fin.ext
    dsimp [generatedTenthIncomingBSourceWordCachePrefix, b, u]
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
