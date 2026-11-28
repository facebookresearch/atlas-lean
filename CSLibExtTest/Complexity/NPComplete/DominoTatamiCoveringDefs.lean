/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DominoTatamiCoveringDefs

namespace MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Side adjacency of two cells, as a decidable formula. -/
private def SideAdj (p q : ℕ × ℕ) : Prop :=
  (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1) ∧ p.2 = q.2 ∨ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2) ∧ p.1 = q.1

private instance (p q : ℕ × ℕ) : Decidable (SideAdj p q) := by unfold SideAdj; infer_instance

private theorem latticeGraph_adj (p q : ℕ × ℕ) : latticeGraph.Adj p q ↔ SideAdj p q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp [SideAdj, SimpleGraph.boxProd_adj, SimpleGraph.hasse_adj, Nat.covBy_iff_add_one_eq]

/-- A listed region is connected when every cell after the first is side-adjacent to an earlier
cell. -/
private theorem connected_of_parents (l : List (ℕ × ℕ)) (hne : 0 < l.length)
    (h : ∀ k < l.length, 0 < k → ∃ j < k, SideAdj (l.getD j (0, 0)) (l.getD k (0, 0))) :
    (latticeGraph.comap l.get).Connected := by
  have adj : ∀ u v : Fin l.length, SideAdj (l.getD u (0, 0)) (l.getD v (0, 0)) →
      (latticeGraph.comap l.get).Adj u v := by
    intro u v huv
    rw [SimpleGraph.comap_adj, latticeGraph_adj]
    simpa [List.getD_eq_getElem] using huv
  have reach : ∀ k (hk : k < l.length),
      (latticeGraph.comap l.get).Reachable ⟨0, hne⟩ ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rfl
      · obtain ⟨j, hj, hadj⟩ := h k hk hpos
        exact (ih j hj (by omega)).trans (adj ⟨j, by omega⟩ ⟨k, hk⟩ hadj).reachable
  have : Nonempty (Fin l.length) := ⟨⟨0, hne⟩⟩
  exact ⟨fun u v => (reach u u.2).symm.trans (reach v v.2)⟩

/-- Every block lying in the region has its lower left cell in the region. -/
private theorem block_iff (i : DominoTatamiCoveringInstance) (Q : ℕ × ℕ → Prop) :
    (∀ p : ℕ × ℕ, (∀ c ∈ blockCells p, c ∈ i) → Q p) ↔
      ∀ p ∈ i, (∀ c ∈ blockCells p, c ∈ i) → Q p :=
  ⟨fun h p _ => h p, fun h p hp => h p (hp p (by simp [blockCells])) hp⟩

/-- Every domino covers one cell of each checkerboard color. -/
private theorem countP_even (d : (ℕ × ℕ) × Bool) :
    (dominoCells d).countP (fun c => (c.1 + c.2) % 2 == 0) = 1 := by
  obtain ⟨⟨x, y⟩, b⟩ := d
  cases b <;> simp [dominoCells, List.countP_cons] <;> split_ifs <;> omega

private theorem countP_odd (d : (ℕ × ℕ) × Bool) :
    (dominoCells d).countP (fun c => (c.1 + c.2) % 2 == 1) = 1 := by
  obtain ⟨⟨x, y⟩, b⟩ := d
  cases b <;> simp [dominoCells, List.countP_cons] <;> split_ifs <;> omega

/-- The `4 × 2` rectangle, listed column by column. -/
private abbrev yes : DominoTatamiCoveringInstance :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]

/-- Four vertical dominoes, one per column. -/
private abbrev vertical : List ((ℕ × ℕ) × Bool) :=
  [((0, 0), false), ((1, 0), false), ((2, 0), false), ((3, 0), false)]

/-- Four horizontal dominoes: a domino tiling in which four dominoes meet at `(2, 1)`. -/
private abbrev horizontal : List ((ℕ × ℕ) × Bool) :=
  [((0, 0), true), ((0, 1), true), ((2, 0), true), ((2, 1), true)]

/-- The T-tetromino: three cells of one checkerboard color and one of the other. -/
private abbrev tee : DominoTatamiCoveringInstance := [(0, 0), (1, 0), (2, 0), (1, 1)]

private theorem yes_wellFormed : WellFormed yes :=
  ⟨by decide, connected_of_parents yes (by decide) (by decide)⟩

private theorem tee_wellFormed : WellFormed tee :=
  ⟨by decide, connected_of_parents tee (by decide) (by decide)⟩

/-- The decision problem accepts the rectangle, with the vertical tiling as witness. -/
example : dominoTatamiCoveringDec (bitEncode yes) = true := by
  have hf : DominoTatamiCoveringFeasible yes := by
    refine ⟨vertical, by decide, ?_⟩
    rw [block_iff]
    decide
  simp [dominoTatamiCoveringDec, bitDecode_bitEncode, yes_wellFormed, hf]

/-- The block condition is not vacuous: the horizontal tiling covers the rectangle exactly, but
the block with lower left cell `(1, 0)` contains none of its dominoes. -/
example : (horizontal.flatMap dominoCells).Perm yes ∧
    ¬ ∀ p : ℕ × ℕ, (∀ c ∈ blockCells p, c ∈ yes) →
      ∃ d ∈ horizontal, ∀ c ∈ dominoCells d, c ∈ blockCells p := by
  rw [block_iff]
  decide

/-- The decision problem rejects the well-formed T-tetromino: by the checkerboard coloring a
domino covering would use as many cells of each color. -/
example : WellFormed tee ∧ dominoTatamiCoveringDec (bitEncode tee) = false := by
  have hf : ¬ DominoTatamiCoveringFeasible tee := by
    rintro ⟨ds, hperm, -⟩
    have he := hperm.countP_eq (fun c => (c.1 + c.2) % 2 == 0)
    have ho := hperm.countP_eq (fun c => (c.1 + c.2) % 2 == 1)
    rw [List.countP_flatMap] at he ho
    simp only [Function.comp_def, countP_even, countP_odd, List.map_const', List.sum_replicate,
      smul_eq_mul, mul_one] at he ho
    have h3 : List.countP (fun c : ℕ × ℕ => (c.1 + c.2) % 2 == 0) tee = 3 := by decide
    have h1 : List.countP (fun c : ℕ × ℕ => (c.1 + c.2) % 2 == 1) tee = 1 := by decide
    omega
  exact ⟨tee_wellFormed, by simp [dominoTatamiCoveringDec, bitDecode_bitEncode, hf]⟩

/-- The empty region is malformed (not a polyomino), although the empty covering is feasible. -/
example : DominoTatamiCoveringFeasible [] ∧
    dominoTatamiCoveringDec (bitEncode ([] : DominoTatamiCoveringInstance)) = false := by
  have hw : ¬ WellFormed [] := fun h => h.2.nonempty.some.elim0
  refine ⟨⟨[], List.Perm.nil, fun p hp => absurd (hp p (by simp [blockCells])) (by simp)⟩, ?_⟩
  simp [dominoTatamiCoveringDec, bitDecode_bitEncode, hw]

/-- A lone continuation bit is a truncated instance encoding. -/
example : dominoTatamiCoveringDec [true] = false := by
  have h : bitDecode (α := DominoTatamiCoveringInstance) [true] = none := rfl
  simp [dominoTatamiCoveringDec, h]

end MetaMathlibExt.Complexity.NPComplete.DominoTatamiCovering
