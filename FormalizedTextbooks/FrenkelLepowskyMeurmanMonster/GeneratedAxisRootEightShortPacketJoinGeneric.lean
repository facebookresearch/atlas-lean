/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

/-! Abstract joins of complete original short-address predicates. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete bounded packets cover each original address exactly. -/
theorem generatedRootEight_short_packet_join (P : Fin 98280 → Prop)
    (h : ∀ b : Fin 96, ∀ u : Fin 1024,
      if hb : b.val * 1024 + u.val < 98280 then P ⟨b.val * 1024 + u.val, hb⟩ else True) :
    ∀ a : Fin 98280, P a := by
  intro a
  let b : Fin 96 := ⟨a.val / 1024, by have ha := a.isLt; omega⟩
  let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hn : b.val * 1024 + u.val = a.val := by dsimp [b, u]; omega
  have hb : b.val * 1024 + u.val < 98280 := by have ha := a.isLt; omega
  have hh := h b u
  rw [dite_eq_left hb] at hh
  have he : (⟨b.val * 1024 + u.val, hb⟩ : Fin 98280) = a := Fin.ext hn
  simpa only [he] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
