/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SideChainPositioningDefs

namespace MetaMathlibExt.Complexity.NPComplete.SideChainPositioning

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SideChainPositioningInstance) :
    sideChainPositioningDec (bitEncode i) = true ↔
      WellFormed i ∧ SideChainPositioningFeasible i := by
  simp [sideChainPositioningDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : sideChainPositioningDec [true] = false := by
  have h : bitDecode (α := SideChainPositioningInstance) [true] = none := rfl
  simp [sideChainPositioningDec, h]

/-- Two positions; rotamer `0` sits at position `0` with energy `0`, rotamers `1` and `2` sit at
position `1` with energies `5` and `1`; the pair energy between rotamers `0` and `2` is `2`, the
other pair energies are `0`. -/
private abbrev inst (K : ℕ × ℕ) : SideChainPositioningInstance :=
  (2, [0, 1, 1], [(0, 0), (5, 0), (1, 0)],
    [[(0, 0), (0, 0), (0, 0)], [(0, 0), (0, 0), (0, 0)], [(2, 0), (0, 0), (0, 0)]], K)

private theorem wellFormed_inst (K : ℕ × ℕ) : WellFormed (inst K) := by
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · show ∀ j ∈ [0, 1, 1], j < 2
    decide
  · show ∀ j < 2, j ∈ [0, 1, 1]
    decide
  · show ∀ row ∈ [[((0 : ℕ), (0 : ℕ)), (0, 0), (0, 0)], [(0, 0), (0, 0), (0, 0)],
      [(2, 0), (0, 0), (0, 0)]], row.length = 3
    decide

/-- The total energy of a choice depends only on the two chosen rotamers. -/
private theorem totalEnergy_inst (K : ℕ × ℕ) (c : Fin 2 → ℕ) :
    totalEnergy (inst K) c = selfEnergy (inst K) (c 0) + selfEnergy (inst K) (c 1) +
      pairEnergy (inst K) (c 1) (c 0) := by
  have h0 : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 2) = {0} := by decide
  change ∑ a : Fin 2, _ + ∑ a : Fin 2, ∑ b ∈ Finset.Iio a, _ = _
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [hu, Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide), h0, h1, Finset.sum_empty,
    Finset.sum_singleton]
  omega

/-- Choosing rotamers `0` and `2` costs `0 + 1 + 2 = 3`, within the bound `3`. -/
example : sideChainPositioningDec (bitEncode (inst (3, 0))) = true := by
  refine (accepts_encoding _).2 ⟨wellFormed_inst _, fun a => if (a : ℕ) = 0 then 0 else 2,
    by decide, ?_⟩
  rw [totalEnergy_inst]
  decide

/-- Bound `2`: rotamer `0` is forced at position `0`; then rotamer `1` costs `0 + 5 + 0 = 5`
and rotamer `2` costs `0 + 1 + 2 = 3`, so no choice reaches `2`, though the self energies alone
would allow `1`. -/
example : sideChainPositioningDec (bitEncode (inst (2, 0))) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, c, hc, hE⟩ := (accepts_encoding _).1 h
  rw [totalEnergy_inst] at hE
  obtain ⟨hc0, hp0⟩ := hc 0
  obtain ⟨hc1, hp1⟩ := hc 1
  simp only [inst, List.length_cons, List.length_nil] at hc0 hc1 hp0 hp1
  generalize c 0 = x at hc0 hp0 hE
  generalize c 1 = y at hc1 hp1 hE
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1 ∨ y = 2) with rfl | rfl | rfl <;>
    simp at hp0 hp1 <;> revert hE <;> decide

/-- A rotamer at position `2` is outside the `2` positions, so the instance is malformed. -/
example : sideChainPositioningDec
    (bitEncode ((2, [0, 1, 2], [(0, 0), (0, 0), (0, 0)],
      [[(0, 0), (0, 0), (0, 0)], [(0, 0), (0, 0), (0, 0)], [(0, 0), (0, 0), (0, 0)]],
      (5, 0)) : SideChainPositioningInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.1 2 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.SideChainPositioning
