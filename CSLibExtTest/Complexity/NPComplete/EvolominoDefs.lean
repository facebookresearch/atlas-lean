/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EvolominoDefs

namespace MetaMathlibExt.Complexity.NPComplete.Evolomino

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open BkVPGRecognition (GridAdj IsGridPath)

private theorem accepts_encoding (i : EvolominoInstance) :
    evolominoDec (bitEncode i) = true ↔ WellFormed i ∧ EvolominoFeasible i := by
  simp [evolominoDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : evolominoDec [true] = false := by
  have h : bitDecode (α := EvolominoInstance) [true] = none := rfl
  simp [evolominoDec, h]

private instance (p q : ℕ × ℕ) : Decidable (GridAdj p q) := by
  unfold GridAdj; infer_instance

/-- Squares linked to a square of a set `C` closed under adjacency within `S` stay in `C`. -/
private theorem linked_closed {S C : Finset (ℕ × ℕ)} {p q : ℕ × ℕ} (hp : p ∈ C)
    (hC : ∀ a ∈ C, ∀ b ∈ S, GridAdj a b → b ∈ C) (h : Linked S p q) : q ∈ C := by
  induction h with
  | refl => exact hp
  | tail _ hab ih => exact hC _ ih _ hab.2.1 hab.2.2

/-- The block of `p` is `C` when `C ⊆ S` is closed under adjacency within `S` and every member of
`C` is linked to `p`. -/
private theorem block_eq {S C : Finset (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ C) (hCS : C ⊆ S)
    (hC : ∀ a ∈ C, ∀ b ∈ S, GridAdj a b → b ∈ C) (hl : ∀ q ∈ C, Linked S p q) :
    block S p = C := by
  classical
  ext q
  simp only [block, Finset.mem_filter]
  exact ⟨fun h => linked_closed hp hC h.2, fun h => ⟨hCS h, hl q h⟩⟩

/-- A two-by-three white board with one arrow along the top row. -/
private abbrev board : EvolominoInstance := ([[0, 0, 0], [0, 0, 0]], [[(0, 0), (0, 1), (0, 2)]])

/-- The squares: a monomino at the start of the arrow and a vertical domino at its end. -/
private abbrev S₀ : Finset (ℕ × ℕ) := {(0, 0), (0, 2), (1, 2)}

private theorem block_left : block S₀ (0, 0) = {(0, 0)} :=
  block_eq (by decide) (by decide) (by decide) fun q hq => by
    rw [Finset.mem_singleton.1 hq]; exact .refl

private theorem block_right (p : ℕ × ℕ) (hp : p = (0, 2) ∨ p = (1, 2)) :
    block S₀ p = {(0, 2), (1, 2)} := by
  have step : Linked S₀ (0, 2) (1, 2) := .single ⟨by decide, by decide, by decide⟩
  have back : Linked S₀ (1, 2) (0, 2) := .single ⟨by decide, by decide, by decide⟩
  rcases hp with rfl | rfl
  · refine block_eq (by decide) (by decide) (by decide) fun q hq => ?_
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact .refl
    · rw [Finset.mem_singleton.1 hq]; exact step
  · refine block_eq (by decide) (by decide) (by decide) fun q hq => ?_
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact back
    · rw [Finset.mem_singleton.1 hq]; exact .refl

/-- The monomino at the arrow's start evolves into the domino at its end by adding one square;
each block holds exactly one arrow square. -/
example : evolominoDec (bitEncode board) = true := by
  refine (accepts_encoding _).2 ⟨?_, S₀, by decide, ?_, ?_, by decide, ?_⟩
  · unfold WellFormed IsGridPath
    decide
  · rintro ⟨a, b⟩ hp
    exfalso
    rcases a with _ | _ | a <;> rcases b with _ | _ | _ | b <;> simp [kind] at hp
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | hp
    · rw [block_left]; decide
    · rw [block_right p hp]; decide
  · intro A hA
    obtain rfl := List.mem_singleton.1 hA
    rw [show ([(0, 0), (0, 1), (0, 2)].filter (· ∈ S₀)) = [(0, 0), (0, 2)] by decide]
    simp only [List.map_cons, List.map_nil, block_left, block_right (0, 2) (Or.inl rfl)]
    exact List.isChain_pair.2 ⟨by decide, 0, 2, by decide⟩

/-- A one-by-two board whose two cells form an arrow: the arrow needs both cells as squares, but
adjacent squares share a block, which then holds two arrow squares. -/
example : evolominoDec (bitEncode (([[0, 0]], [[(0, 0), (0, 1)]]) : EvolominoInstance)) =
    false := by
  cases h : evolominoDec (bitEncode (([[0, 0]], [[(0, 0), (0, 1)]]) : EvolominoInstance)) with
  | false => rfl
  | true =>
    classical
    obtain ⟨-, S, -, -, hone, htwo, -⟩ := (accepts_encoding _).1 h
    have hlen := htwo _ (List.mem_singleton_self _)
    have h0 : (0, 0) ∈ S := by
      by_contra hn
      by_cases h1 : (0, 1) ∈ S <;> simp [hn, h1] at hlen
    have h1 : (0, 1) ∈ S := by
      by_contra hn
      simp [h0, hn] at hlen
    have hsub : ({(0, 0), (0, 1)} : Finset (ℕ × ℕ)) ⊆
        (block S (0, 0)).filter fun q => ∃ A ∈ ([[(0, 0), (0, 1)]] : List (List (ℕ × ℕ))),
          q ∈ A := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      simp only [Finset.mem_filter, block]
      rcases hq with rfl | rfl
      · exact ⟨⟨h0, .refl⟩, by decide⟩
      · exact ⟨⟨h1, .single ⟨h0, h1, by decide⟩⟩, by decide⟩
    have := Finset.card_le_card hsub
    rw [hone _ h0] at this
    exact absurd this (by decide)

end MetaMathlibExt.Complexity.NPComplete.Evolomino
