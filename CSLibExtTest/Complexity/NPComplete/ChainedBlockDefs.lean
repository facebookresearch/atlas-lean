/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ChainedBlockDefs

namespace MetaMathlibExt.Complexity.NPComplete.ChainedBlock

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ChainedBlockInstance) :
    chainedBlockDec (bitEncode i) = true ↔
      WellFormed i ∧ ChainedBlockFeasible i := by
  simp [chainedBlockDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : chainedBlockDec [true] = false := by
  have h : bitDecode (α := ChainedBlockInstance) [true] = none := rfl
  simp [chainedBlockDec, h]

open SimpleGraph

/-- A `2 × 3` grid with the clue `1` at `(0, 0)` and the clue `2` at `(1, 1)`. -/
private abbrev inst : ChainedBlockInstance :=
  [[(true, 1), (false, 0), (false, 0)], [(false, 0), (true, 2), (false, 0)]]

/-- The cell in row `r` and column `k`. -/
private abbrev cell (r k : ℕ) (hr : r < 2 := by decide) (hk : k < 3 := by decide) : Cell inst :=
  (⟨r, hr⟩, ⟨k, hk⟩)

/-- The black cells of the solution: the block `{(0, 0)}` and the domino `{(1, 1), (1, 2)}`. -/
private def B : Set (Cell inst) := {p | p = cell 0 0 ∨ p = cell 1 1 ∨ p = cell 1 2}

private theorem reach_const {V α : Type} {G : SimpleGraph V} (f : V → α)
    (hf : ∀ u v, G.Adj u v → f u = f v) {u v : V} (h : G.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons ha _ ih => exact (hf _ _ ha).trans ih

private theorem induce_adj (p q : B) :
    ((gridGraph inst).induce B).Adj p q ↔
      ((p.1.1.val + 1 = q.1.1.val ∨ q.1.1.val + 1 = p.1.1.val) ∧ p.1.2 = q.1.2) ∨
        ((p.1.2.val + 1 = q.1.2.val ∨ q.1.2.val + 1 = p.1.2.val) ∧ p.1.1 = q.1.1) := by
  simp [boxProd_adj, pathGraph_adj]

private def v₀ : B := ⟨cell 0 0, Or.inl rfl⟩
private def v₁ : B := ⟨cell 1 1, Or.inr (Or.inl rfl)⟩
private def v₂ : B := ⟨cell 1 2, Or.inr (Or.inr rfl)⟩

/-- The block of the clue `1`. -/
private def c₀ : Block inst B := ((gridGraph inst).induce B).connectedComponentMk v₀
/-- The block of the clue `2`. -/
private def c₁ : Block inst B := ((gridGraph inst).induce B).connectedComponentMk v₁

private theorem c₁_eq : ((gridGraph inst).induce B).connectedComponentMk v₂ = c₁ :=
  ConnectedComponent.eq.2 (Adj.reachable ((induce_adj _ _).2 (Or.inr ⟨Or.inr rfl, rfl⟩)))

/-- No black cell other than `(0, 0)` is grid-adjacent to `(0, 0)`. -/
private theorem isolated (u v : B) (h : ((gridGraph inst).induce B).Adj u v) :
    decide (u.1 = cell 0 0) = decide (v.1 = cell 0 0) := by
  obtain ⟨p, hp⟩ := u
  obtain ⟨q, hq⟩ := v
  rw [induce_adj] at h
  simp only [B, Set.mem_ofPred_eq] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all [Fin.ext_iff]

private theorem c₀_ne_c₁ : c₀ ≠ c₁ := by
  intro h
  have := reach_const (fun u : B => decide (u.1 = cell 0 0)) isolated (ConnectedComponent.eq.1 h)
  simp [v₀, v₁] at this

private theorem block_cases (c : Block inst B) : c = c₀ ∨ c = c₁ := by
  induction c using ConnectedComponent.ind with
  | h v =>
    obtain ⟨p, hp⟩ := v
    simp only [B, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr c₁_eq

private theorem mem_blockCells (c : Block inst B) (p : Cell inst) :
    p ∈ blockCells c ↔
      ∃ h : p ∈ B, ((gridGraph inst).induce B).connectedComponentMk ⟨p, h⟩ = c := by
  simp [blockCells, ConnectedComponent.mem_supp_iff]

private theorem cells_c₀ : blockCells c₀ = {cell 0 0} := by
  ext p
  rw [mem_blockCells, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h⟩
    simp only [B, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact absurd h.symm c₀_ne_c₁
    · exact absurd (h.symm.trans c₁_eq) c₀_ne_c₁
  · rintro rfl
    exact ⟨Or.inl rfl, rfl⟩

private theorem cells_c₁ : blockCells c₁ = {cell 1 1, cell 1 2} := by
  ext p
  rw [mem_blockCells, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h⟩
    simp only [B, Set.mem_ofPred_eq] at hp
    rcases hp with rfl | rfl | rfl
    · exact absurd h c₀_ne_c₁
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨Or.inr (Or.inr rfl), c₁_eq⟩

private theorem latticeSymm_injective (s : Bool × Bool × Bool) :
    Function.Injective (latticeSymm s) := by
  obtain ⟨_ | _, _ | _, _ | _⟩ := s <;> intro p q h <;>
    simp [latticeSymm, Prod.ext_iff] at h ⊢ <;> omega

private theorem ncard_coords (S : Set (Cell inst)) : (coords S).ncard = S.ncard :=
  Set.ncard_image_of_injective _ fun p q h => by
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

private theorem not_sameShape (S T : Set (Cell inst)) (h : S.ncard ≠ T.ncard) :
    ¬ SameShape (coords S) (coords T) := by
  rintro ⟨s, t, hT⟩
  apply h
  have inj : Function.Injective fun p => latticeSymm s p + t :=
    fun p q hpq => latticeSymm_injective s (add_right_cancel hpq)
  rw [← ncard_coords S, ← ncard_coords T, hT, Set.ncard_image_of_injective _ inj]

private theorem ncard_c₀ : (blockCells c₀).ncard = 1 := by
  rw [cells_c₀, Set.ncard_singleton]

private theorem ncard_c₁ : (blockCells c₁).ncard = 2 := by
  rw [cells_c₁, Set.ncard_pair (by decide)]

private theorem touch₀₁ : Touch c₀ c₁ :=
  ⟨c₀_ne_c₁, cell 0 0, by simp [cells_c₀], cell 1 1, by simp [cells_c₁],
    by unfold CornerAdj; decide⟩

/-- The clue `1` keeps the single cell `(0, 0)`, and the clue `2` grows into the domino
`(1, 1), (1, 2)`; the two blocks touch at a corner and have different shapes, so they form a
valid chain. -/
example : chainedBlockDec (bitEncode inst) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, B, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨r, hr⟩, ⟨k, hk⟩⟩ h
    simp only [IsClue, entry] at h
    simp only [B, Set.mem_ofPred_eq]
    revert r k
    decide
  · intro c
    rcases block_cases c with rfl | rfl
    · refine ⟨cell 0 0, ⟨by simp [cells_c₀], by unfold IsClue; decide⟩, fun q ⟨hq, _⟩ => ?_⟩
      simpa [cells_c₀] using hq
    · refine ⟨cell 1 1, ⟨by simp [cells_c₁], by unfold IsClue; decide⟩, fun q ⟨hq, hc⟩ => ?_⟩
      rw [cells_c₁, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · rfl
      · exact absurd hc (by unfold IsClue; decide)
  · intro c p hp hc _
    rcases block_cases c with rfl | rfl
    · rw [cells_c₀, Set.mem_singleton_iff] at hp
      subst hp
      rw [ncard_c₀]
      rfl
    · rw [cells_c₁, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · rw [ncard_c₁]
        rfl
      · exact absurd hc (by unfold IsClue; decide)
  · intro c
    rcases block_cases c with rfl | rfl
    · exact ⟨c₁, touch₀₁⟩
    · obtain ⟨hne, p, hp, q, hq, hpq⟩ := touch₀₁
      exact ⟨c₀, hne.symm, q, hq, p, hp, ⟨hpq.1.symm, hpq.2.symm⟩⟩
  · intro c d hcd _
    rcases block_cases c with rfl | rfl <;> rcases block_cases d with rfl | rfl
    · exact absurd rfl hcd
    · exact not_sameShape _ _ (by rw [ncard_c₀, ncard_c₁]; decide)
    · exact not_sameShape _ _ (by rw [ncard_c₀, ncard_c₁]; decide)
    · exact absurd rfl hcd

/-- A lone clue on a `1 × 1` grid cannot be part of a chain: no two cells of the grid are
diagonal neighbours, so its block touches no other block. -/
example : chainedBlockDec (bitEncode ([[(true, 1)]] : ChainedBlockInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, B', hclue, -, -, hchain, -⟩
  let p : Cell [[(true, 1)]] := (⟨0, by decide⟩, ⟨0, by decide⟩)
  have hp : p ∈ B' := hclue p (by unfold IsClue; decide)
  obtain ⟨d, -, q, -, r, -, hqr⟩ := hchain (((gridGraph _).induce B').connectedComponentMk ⟨p, hp⟩)
  obtain ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ := q
  obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := r
  simp only [CornerAdj] at hqr
  simp only [rows, cols, List.length_cons, List.length_nil, List.headD_cons] at hq₁ hq₂ hr₁ hr₂
  omega

/-- Malformed: a ragged grid (rows of lengths `2` and `1`) is not well formed. -/
example : chainedBlockDec (bitEncode
    ([[(true, 1), (false, 0)], [(false, 0)]] : ChainedBlockInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨hw, -⟩
  exact absurd hw (by unfold WellFormed; decide)

end MetaMathlibExt.Complexity.NPComplete.ChainedBlock
