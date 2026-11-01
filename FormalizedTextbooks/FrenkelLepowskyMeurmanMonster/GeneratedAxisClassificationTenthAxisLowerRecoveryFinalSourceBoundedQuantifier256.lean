/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic

/-! Exact smaller closed quantifiers preserve all original final-source packet addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Four full 64-address blocks cover every original 256-address packet coordinate. -/
theorem generatedTenth_final_source_predicate256_of_blocks (p : Fin 256 → Prop)
    (h : ∀ b : Fin 4, ∀ u : Fin 64, p ⟨64 * b.val + u.val, by omega⟩) :
    ∀ n : Fin 256, p n := by
  intro n
  let b : Fin 4 := ⟨n.val / 64, by omega⟩
  let u : Fin 64 := ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : (⟨64 * b.val + u.val, by omega⟩ : Fin 256) = n := by
    apply Fin.ext
    dsimp [b, u]
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
