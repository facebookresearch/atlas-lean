/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SatogaeriDefs

namespace MetaMathlibExt.Complexity.NPComplete.Satogaeri

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SatogaeriInstance) :
    satogaeriDec (bitEncode i) = true ↔ WellFormed i ∧ SatogaeriFeasible i := by
  simp [satogaeriDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : satogaeriDec [true] = false := by
  have h : bitDecode (α := SatogaeriInstance) [true] = none := rfl
  simp [satogaeriDec, h]

/-- A set of cells any two of which are equal or adjacent induces a preconnected graph. -/
private theorem preconnected_of_pairwise {V : Type} (G : SimpleGraph V) (S : Set V)
    (h : ∀ u ∈ S, ∀ v ∈ S, u = v ∨ G.Adj u v) : (G.induce S).Preconnected := by
  intro u v
  rcases h u.1 u.2 v.1 v.2 with e | a
  · rw [Subtype.ext e]
  · exact SimpleGraph.Adj.reachable (by simpa using a)

/-- Adjacency in the grid graph, as a decidable condition on coordinates. -/
private theorem grid_adj (i : SatogaeriInstance) (u v : Cell i) : (Grid i).Adj u v ↔
    (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)) ∨
      (u.2 = v.2 ∧ ((u.1 : ℕ) + 1 = v.1 ∨ (v.1 : ℕ) + 1 = u.1)) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
  tauto

/-- A `1 × 3` grid in two regions, `{(0, 0)}` and `{(0, 1), (0, 2)}`, with an unnumbered circle
at `(0, 0)` and a circle numbered `1` at `(0, 1)`. -/
private abbrev grid13 : SatogaeriInstance := (2, [[(0, 1), (1, 3), (1, 0)]])

/-- Destinations: cells of column `0` stay, the others go to `(0, 2)`. -/
private def dest (x : Cell grid13) : Cell grid13 :=
  if (x.2 : ℕ) = 0 then x else (x.1, ⟨2, by decide⟩)

/-- The circle at `(0, 0)` stays and the circle at `(0, 1)` moves one cell right: each region
receives one circle and the tracks are disjoint. -/
example : satogaeriDec (bitEncode grid13) = true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, by decide, by decide, by decide, fun k hk => ?_⟩,
    dest, ?_⟩
  · rcases (by have : k < 2 := hk; omega : k = 0 ∨ k = 1) with rfl | rfl
    · refine (SimpleGraph.connected_iff _).2 ⟨preconnected_of_pairwise _ _ ?_,
        ⟨⟨(⟨0, by decide⟩, ⟨0, by decide⟩), rfl⟩⟩⟩
      simp only [grid_adj, Set.mem_ofPred_eq]
      decide
    · refine (SimpleGraph.connected_iff _).2 ⟨preconnected_of_pairwise _ _ ?_,
        ⟨⟨(⟨0, by decide⟩, ⟨1, by decide⟩), rfl⟩⟩⟩
      simp only [grid_adj, Set.mem_ofPred_eq]
      decide
  · refine ⟨by decide, by decide, ?_, fun k hk => ?_⟩
    · intro x y hx hy hne z ⟨hzx, hzy⟩
      unfold OnTrack at hzx hzy
      rcases hzx with hzx | hzx <;> rcases hzy with hzy | hzy <;> revert x y z <;> decide
    · rcases (by have : k < 2 := hk; omega : k = 0 ∨ k = 1) with rfl | rfl
      · refine ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by decide, fun y hy => ?_⟩
        revert y
        decide
      · refine ⟨(⟨0, by decide⟩, ⟨1, by decide⟩), by decide, fun y hy => ?_⟩
        revert y
        decide

/-- A `1 × 2` grid in two regions with one circle numbered `1` at `(0, 0)`: the circle must
move into the second region, leaving the first region without a circle. -/
example : satogaeriDec (bitEncode ((2, [[(0, 3), (1, 0)]]) : SatogaeriInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, D, -, hmove, -, hregion⟩ := (accepts_encoding _).1 h
  obtain ⟨x, ⟨hx, hk⟩, -⟩ := hregion 0 (by decide)
  have key : ∀ x d : Cell ((2, [[(0, 3), (1, 0)]]) : SatogaeriInstance),
      (cell (2, [[(0, 3), (1, 0)]]) x).2 ≠ 0 → (cell (2, [[(0, 3), (1, 0)]]) d).1 = 0 →
      (2 ≤ (cell (2, [[(0, 3), (1, 0)]]) x).2 →
        Nat.dist x.1 d.1 + Nat.dist x.2 d.2 = (cell (2, [[(0, 3), (1, 0)]]) x).2 - 2) → False := by
    decide
  exact key x (D x) hx hk (hmove x)

/-- A region index not below the number of regions makes the instance malformed. -/
example : satogaeriDec (bitEncode ((1, [[(1, 1)]]) : SatogaeriInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.2.2.1 [(1, 1)] (by simp) (1, 1) (by simp))
    (by decide)

end MetaMathlibExt.Complexity.NPComplete.Satogaeri
