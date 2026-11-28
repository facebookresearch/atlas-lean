/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HedonicCoreStablePartitionDefs

namespace MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HedonicCoreStablePartitionInstance) :
    hedonicCoreStablePartitionDec (bitEncode i) = true ↔
      WellFormed i ∧ HedonicCoreStablePartitionFeasible i := by
  simp [hedonicCoreStablePartitionDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HedonicCoreStablePartitionInstance) bits = none) :
    hedonicCoreStablePartitionDec bits = false := by
  simp [hedonicCoreStablePartitionDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hedonicCoreStablePartitionDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Two players who both rank the pair `{0, 1}` first (rank `0`) and their singleton second. -/
private abbrev pairInst : HedonicCoreStablePartitionInstance :=
  (2, [[([0, 1], 0), ([0], 1)], [([0, 1], 0), ([1], 1)]])

/-- Three players with cyclic preferences over pairs: player `0` ranks `{0, 1}`, `{0, 2}`, `{0}`;
player `1` ranks `{1, 2}`, `{0, 1}`, `{1}`; player `2` ranks `{0, 2}`, `{1, 2}`, `{2}`. -/
private abbrev cyclicInst : HedonicCoreStablePartitionInstance :=
  (3, [[([0, 1], 0), ([0, 2], 1), ([0], 2)], [([1, 2], 0), ([0, 1], 1), ([1], 2)],
    [([0, 2], 0), ([1, 2], 1), ([2], 2)]])

/-- The grand coalition is core stable: every player ranks it first, so no coalition is strictly
preferred by any member. -/
example : hedonicCoreStablePartitionDec (bitEncode pairInst) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed listing; decide,
    Finpartition.indiscrete (Finset.univ_nonempty.ne_empty), ?_⟩
  intro S hS
  obtain ⟨p, hp⟩ := hS
  refine ⟨p, hp, ?_⟩
  have hpart : (Finpartition.indiscrete (Finset.univ_nonempty.ne_empty)).part p =
      (Finset.univ : Finset (Fin pairInst.1)) :=
    Finpartition.part_eq_of_mem _ (by simp) (Finset.mem_univ p)
  rw [hpart]
  rintro ⟨c, -, -, hall⟩
  have hgrand : ([0, 1] : List ℕ).toFinset =
      (Finset.univ : Finset (Fin pairInst.1)).image Fin.val := by decide
  rcases p with ⟨_ | _ | n, hn⟩
  · exact absurd (hall ([0, 1], 0) (by simp [listing]) hgrand) (by simp)
  · exact absurd (hall ([0, 1], 0) (by simp [listing]) hgrand) (by simp)
  · exact absurd hn (by simp)

-- The cyclic game is checked over all `8 ^ 3` choices of the players' parts, which exceeds the
-- default instance size bound for `decide`.
set_option synthInstance.maxSize 1024 in
/-- Whatever parts the three players occupy, consistently with a partition, some nonempty
coalition is strictly preferred by each of its members. -/
private theorem cyclic_blocked : ∀ a b c : Finset (Fin 3), 0 ∈ a → 1 ∈ b → 2 ∈ c →
    (1 ∈ a → b = a) → (2 ∈ a → c = a) → (0 ∈ b → a = b) → (2 ∈ b → c = b) →
    (0 ∈ c → a = c) → (1 ∈ c → b = c) →
    ∃ S : Finset (Fin 3), S.Nonempty ∧ ∀ p ∈ S,
      Prefers cyclicInst p S (if p = 0 then a else if p = 1 then b else c) := by
  unfold Prefers listing
  decide

/-- The cyclic game is well formed. -/
example : WellFormed cyclicInst := by
  unfold WellFormed listing
  decide

/-- The cyclic game has no core stable partition. -/
example : hedonicCoreStablePartitionDec (bitEncode cyclicInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, P, hP⟩
  have hmem : ∀ p : Fin 3, p ∈ P.part p := fun p => P.mem_part (Finset.mem_univ p)
  have hsame : ∀ p q : Fin 3, q ∈ P.part p → P.part q = P.part p := fun p q =>
    (P.mem_part_iff_part_eq_part (Finset.mem_univ q) (Finset.mem_univ p)).1
  obtain ⟨S, hS, hpref⟩ := cyclic_blocked (P.part 0) (P.part 1) (P.part 2)
    (hmem 0) (hmem 1) (hmem 2) (hsame 0 1) (hsame 0 2) (hsame 1 0) (hsame 1 2)
    (hsame 2 0) (hsame 2 1)
  obtain ⟨p, hp, hnot⟩ := hP S hS
  apply hnot
  have := hpref p hp
  rcases p with ⟨_ | _ | _ | n, hn⟩
  · exact this
  · exact this
  · exact this
  · exact absurd hn (by simp)

/-- A player who does not list their own singleton is malformed. -/
example :
    hedonicCoreStablePartitionDec (bitEncode
      ((1, [[]]) : HedonicCoreStablePartitionInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h⟩, -⟩
  obtain ⟨-, -, c, hc, -⟩ := h 0 (by decide)
  simp [listing] at hc

end MetaMathlibExt.Complexity.NPComplete.HedonicCoreStablePartition
