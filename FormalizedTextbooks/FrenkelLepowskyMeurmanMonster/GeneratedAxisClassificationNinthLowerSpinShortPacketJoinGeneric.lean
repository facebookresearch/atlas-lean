/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBoundedQuantifier

/-! Abstract exact joins keep literal source predicates out of arithmetic proof elaboration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Twelve complete bounded predicates cover every one of the original 98,280 addresses. -/
theorem generatedNinth_lower_spin_short_packet_join (P : Fin 98280 → Prop)
    (h00 : ∀ u : Fin 8192, if h : 0 * 8192 + u.val < 98280 then
      P ⟨0 * 8192 + u.val, h⟩ else True)
    (h01 : ∀ u : Fin 8192, if h : 1 * 8192 + u.val < 98280 then
      P ⟨1 * 8192 + u.val, h⟩ else True)
    (h02 : ∀ u : Fin 8192, if h : 2 * 8192 + u.val < 98280 then
      P ⟨2 * 8192 + u.val, h⟩ else True)
    (h03 : ∀ u : Fin 8192, if h : 3 * 8192 + u.val < 98280 then
      P ⟨3 * 8192 + u.val, h⟩ else True)
    (h04 : ∀ u : Fin 8192, if h : 4 * 8192 + u.val < 98280 then
      P ⟨4 * 8192 + u.val, h⟩ else True)
    (h05 : ∀ u : Fin 8192, if h : 5 * 8192 + u.val < 98280 then
      P ⟨5 * 8192 + u.val, h⟩ else True)
    (h06 : ∀ u : Fin 8192, if h : 6 * 8192 + u.val < 98280 then
      P ⟨6 * 8192 + u.val, h⟩ else True)
    (h07 : ∀ u : Fin 8192, if h : 7 * 8192 + u.val < 98280 then
      P ⟨7 * 8192 + u.val, h⟩ else True)
    (h08 : ∀ u : Fin 8192, if h : 8 * 8192 + u.val < 98280 then
      P ⟨8 * 8192 + u.val, h⟩ else True)
    (h09 : ∀ u : Fin 8192, if h : 9 * 8192 + u.val < 98280 then
      P ⟨9 * 8192 + u.val, h⟩ else True)
    (h10 : ∀ u : Fin 8192, if h : 10 * 8192 + u.val < 98280 then
      P ⟨10 * 8192 + u.val, h⟩ else True)
    (h11 : ∀ u : Fin 8192, if h : 11 * 8192 + u.val < 98280 then
      P ⟨11 * 8192 + u.val, h⟩ else True)
    : ∀ a : Fin 98280, P a := by
  have hp : ∀ b : Fin 12, ∀ u : Fin 8192,
      if h : b.val * 8192 + u.val < 98280 then
        P ⟨b.val * 8192 + u.val, h⟩ else True := by
    intro b u
    fin_cases b
    · exact h00 u
    · exact h01 u
    · exact h02 u
    · exact h03 u
    · exact h04 u
    · exact h05 u
    · exact h06 u
    · exact h07 u
    · exact h08 u
    · exact h09 u
    · exact h10 u
    · exact h11 u
  intro a
  let b : Fin 12 := ⟨a.val / 8192, by omega⟩
  let u : Fin 8192 := ⟨a.val % 8192, Nat.mod_lt _ (by decide)⟩
  have hn : b.val * 8192 + u.val = a.val := by
    dsimp [b, u]
    omega
  have hlt : b.val * 8192 + u.val < 98280 := by omega
  have hh := hp b u
  rw [dite_eq_left hlt] at hh
  have he : (⟨b.val * 8192 + u.val, hlt⟩ : Fin 98280) = a := Fin.ext hn
  simpa only [he] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
