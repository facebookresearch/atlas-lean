/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBoundedQuantifier

/-! The exact final bounded interval retains every original address. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Four complete blocks cover every one of the1,024 original addresses. -/
theorem generatedRootEight_short_predicate1024_of_four_blocks (p : Fin 1024 → Prop)
    (h0 : ∀ u : Fin 256, p ⟨u.val, by omega⟩)
    (h1 : ∀ u : Fin 256, p ⟨256 + u.val, by omega⟩)
    (h2 : ∀ u : Fin 256, p ⟨512 + u.val, by omega⟩)
    (h3 : ∀ u : Fin 256, p ⟨768 + u.val, by omega⟩) :
    ∀ n : Fin 1024, p n := by
  intro n
  by_cases a : n.val < 256
  · exact h0 ⟨n.val, a⟩
  · by_cases b : n.val < 512
    · let u : Fin 256 := ⟨n.val - 256, by omega⟩
      have hi : (⟨256 + u.val, by omega⟩ : Fin 1024) = n := by apply Fin.ext; dsimp [u]; omega
      simpa only [hi] using h1 u
    · by_cases c : n.val < 768
      · let u : Fin 256 := ⟨n.val - 512, by omega⟩
        have hi : (⟨512 + u.val, by omega⟩ : Fin 1024) = n := by apply Fin.ext; dsimp [u]; omega
        simpa only [hi] using h2 u
      · let u : Fin 256 := ⟨n.val - 768, by have hn := n.isLt; omega⟩
        have hi : (⟨768 + u.val, by omega⟩ : Fin 1024) = n := by apply Fin.ext; dsimp [u]; omega
        simpa only [hi] using h3 u


/-- Three full blocks and the final232 coordinates cover every one of the1,000 addresses. -/
theorem generatedRootEight_short_predicate1000_of_blocks (p : Fin 1000 → Prop)
    (h0 : ∀ u : Fin 256, p ⟨u.val, by omega⟩)
    (h1 : ∀ u : Fin 256, p ⟨256 + u.val, by omega⟩)
    (h2 : ∀ u : Fin 256, p ⟨512 + u.val, by omega⟩)
    (h3 : ∀ u : Fin 232, p ⟨768 + u.val, by omega⟩) :
    ∀ n : Fin 1000, p n := by
  intro n
  by_cases a : n.val < 256
  · exact h0 ⟨n.val, a⟩
  · by_cases b : n.val < 512
    · let u : Fin 256 := ⟨n.val - 256, by omega⟩
      have hi : (⟨256 + u.val, by omega⟩ : Fin 1000) = n := by apply Fin.ext; dsimp [u]; omega
      simpa only [hi] using h1 u
    · by_cases c : n.val < 768
      · let u : Fin 256 := ⟨n.val - 512, by omega⟩
        have hi : (⟨512 + u.val, by omega⟩ : Fin 1000) = n := by apply Fin.ext; dsimp [u]; omega
        simpa only [hi] using h2 u
      · let u : Fin 232 := ⟨n.val - 768, by have hn := n.isLt; omega⟩
        have hi : (⟨768 + u.val, by omega⟩ : Fin 1000) = n := by apply Fin.ext; dsimp [u]; omega
        simpa only [hi] using h3 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
