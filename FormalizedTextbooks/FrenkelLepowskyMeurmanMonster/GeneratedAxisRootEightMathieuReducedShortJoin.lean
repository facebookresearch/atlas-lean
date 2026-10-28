/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.FinCases

/-! Bounded address assembly is independent of every concrete short-coordinate decoder. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Twenty-three full intervals and the final partial interval cover all original addresses. -/
theorem generatedRootEight_mathieu_reduced_short_join
    (P : Fin 4 → Fin 98280 → Prop)
    (hfull : ∀ k : Fin 23, ∀ g : Fin 4, ∀ u : Fin 4096,
      P g ⟨4096 * k.val + u.val, by omega⟩)
    (hlast : ∀ g : Fin 4, ∀ u : Fin 4072, P g ⟨94208 + u.val, by omega⟩)
    (g : Fin 4) (n : Fin 98280) : P g n := by
  by_cases h : n.val < 94208
  · let k : Fin 23 := ⟨n.val / 4096, by omega⟩
    let u : Fin 4096 := ⟨n.val % 4096, by omega⟩
    have he : (⟨4096 * k.val + u.val, by omega⟩ : Fin 98280) = n := by
      apply Fin.ext
      dsimp [k, u]
      omega
    have hp := hfull k g u
    rw [he] at hp
    exact hp
  · let u : Fin 4072 := ⟨n.val - 94208, by omega⟩
    have he : (⟨94208 + u.val, by omega⟩ : Fin 98280) = n := by
      apply Fin.ext
      dsimp [u]
      omega
    have hp := hlast g u
    rw [he] at hp
    exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
