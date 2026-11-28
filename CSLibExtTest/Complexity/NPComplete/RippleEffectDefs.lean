/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RippleEffectDefs

namespace MetaMathlibExt.Complexity.NPComplete.RippleEffect

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : RippleEffectInstance) :
    rippleEffectDec (bitEncode i) = true ↔ WellFormed i ∧ RippleEffectFeasible i := by
  simp [rippleEffectDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : rippleEffectDec [true] = false := by
  have h : bitDecode (α := RippleEffectInstance) [true] = none := rfl
  simp [rippleEffectDec, h]

/-- Adjacency in the grid graph, as a decidable condition on coordinates. -/
private theorem grid_adj (i : RippleEffectInstance) (u v : Fin (rows i) × Fin (cols i)) :
    (Grid i).Adj u v ↔
      (u.1 = v.1 ∧ ((u.2 : ℕ) + 1 = v.2 ∨ (v.2 : ℕ) + 1 = u.2)) ∨
        (u.2 = v.2 ∧ ((u.1 : ℕ) + 1 = v.1 ∨ (v.1 : ℕ) + 1 = u.1)) := by
  simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
  tauto

/-- A set of cells any two of which are equal or adjacent induces a preconnected graph. -/
private theorem preconnected_of_pairwise {V : Type} (G : SimpleGraph V) (S : Set V)
    (h : ∀ u ∈ S, ∀ v ∈ S, u = v ∨ G.Adj u v) : (G.induce S).Preconnected := by
  intro u v
  rcases h u.1 u.2 v.1 v.2 with e | a
  · rw [Subtype.ext e]
  · exact SimpleGraph.Adj.reachable (by simpa using a)

/-- A `1 × 3` row in two rooms, `{(0, 0)}` and `{(0, 1), (0, 2)}`, with the given number `g` in
cell `(0, 1)` (`0` for none). -/
private abbrev row (g : ℕ) : RippleEffectInstance := [[(0, 0), (1, g), (1, 0)]]

private theorem wellFormed_row (g : ℕ) (hg : g = 0 ∨ g = 1) : WellFormed (row g) := by
  rcases hg with rfl | rfl <;>
  · refine ⟨by decide, by decide, by simp [cols], fun k => preconnected_of_pairwise _ _ ?_⟩
    intro u hu v hv
    have huv : room _ u = room _ v := hu.trans hv.symm
    clear hu hv
    revert u v
    simp only [grid_adj]
    unfold room
    decide

/-- With no given number, the row is filled `1 2 1`: the two `1`s are two cells apart, more than
the required one. -/
example : rippleEffectDec (bitEncode (row 0)) = true := by
  refine (accepts_encoding _).2
    ⟨wellFormed_row 0 (Or.inl rfl), fun _ c => if c = 1 then 2 else 1, ?_⟩
  unfold roomSize room given
  decide

/-- A given `1` in cell `(0, 1)` is unsolvable: the one-cell room forces a `1` in cell `(0, 0)`,
right next to it. -/
example : rippleEffectDec (bitEncode (row 1)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, f, hgiven, hrange, -, hrow, -⟩ := (accepts_encoding _).1 h
  have h1 := hgiven (⟨0, by decide⟩, ⟨1, by decide⟩) (by decide)
  have h0 := hrange (⟨0, by decide⟩, ⟨0, by decide⟩)
  have hsize : roomSize (row 1) (⟨0, by decide⟩, ⟨0, by decide⟩) = 1 := by decide
  have hgiven1 : given (row 1) (⟨0, by decide⟩, ⟨1, by decide⟩) = 1 := rfl
  simp only [hsize, hgiven1] at h0 h1
  have := hrow (⟨0, by decide⟩, ⟨0, by decide⟩) (⟨0, by decide⟩, ⟨1, by decide⟩) rfl
    (by decide) (by simp only at h0 h1 ⊢; omega)
  simp only at this h0
  omega

/-- A room split into two parts (cells `(0, 0)` and `(0, 2)` with a different room between them)
is not connected, so the grid is malformed. -/
example : rippleEffectDec (bitEncode ([[(0, 0), (1, 0), (0, 0)]] : RippleEffectInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro h
  have hpc := ((accepts_encoding _).1 h).1.2.2.2 0
  let S := {x : Fin (rows [[(0, 0), (1, 0), (0, 0)]]) × Fin (cols [[(0, 0), (1, 0), (0, 0)]]) |
    room [[(0, 0), (1, 0), (0, 0)]] x = 0}
  let a : S := ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), rfl⟩
  let b : S := ⟨(⟨0, by decide⟩, ⟨2, by decide⟩), rfl⟩
  have hbot : (Grid [[(0, 0), (1, 0), (0, 0)]]).induce S = ⊥ := by
    ext u v
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, SimpleGraph.bot_adj,
      iff_false]
    obtain ⟨u, hu⟩ := u
    obtain ⟨v, hv⟩ := v
    change room _ u = 0 at hu
    change room _ v = 0 at hv
    simp only [grid_adj]
    revert u v
    unfold room
    decide
  have hab := hpc a b
  rw [hbot, SimpleGraph.reachable_bot] at hab
  exact absurd (congrArg (fun x : S => (x.1.2 : ℕ)) hab) (by decide)

end MetaMathlibExt.Complexity.NPComplete.RippleEffect
