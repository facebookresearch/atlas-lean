/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCrossing

/-!
# Ray-crossing parity for closed lattice walks

The unit cell `(a, b)` of `ℤ²` is the square `[a, a + 1] × [b, b + 1]`. The vertical ray going up
from its center crosses the horizontal steps of the walk lying on the column `[a, a + 1]` above
height `b`; `rayParity d a b` is the parity of their number. A cell is inside the walk when this
parity is `1` (the even-odd rule of the Jordan curve theorem). This file shows that the parity
does not change between adjacent cells unless the walk separates them, and vanishes above the
walk.

## Main definitions

* `StatMech.Onsager.JordanParity.upCross`: the number of horizontal steps above cell `(a, b)`.
* `StatMech.Onsager.JordanParity.rayParity`: its parity in `ZMod 2`.

## Main results

* `StatMech.Onsager.JordanParity.rayParity_vstep`: moving one cell up does not change the parity
  if no horizontal step separates the two cells.
* `StatMech.Onsager.JordanParity.rayParity_hstep`: moving one cell right does not change the
  parity if no vertical step separates the two cells.
* `StatMech.Onsager.JordanParity.rayParity_topOutside`: cells above the walk have parity `0`.
-/

@[expose] public section

namespace StatMech.Onsager.JordanParity
open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
variable {n : ℕ} [NeZero n]

/-- The number of horizontal steps of the walk on the column `[a, a + 1]` strictly above the cell
  `(a, b)`: the crossings of the upward vertical ray from the center of that cell. -/
def upCross (d : Fin n → Fin 4) (a b : ℤ) : ℕ :=
  (Finset.univ.filter
    (fun k : Fin n =>
      isHorizEdge (d k) ∧
      min ((pos d k).1) ((pos d (k+1)).1) = a ∧
      b < (pos d k).2)).card

/-- The parity of the number of crossings of the upward ray from the center of cell `(a, b)` with
  the walk; cells with parity `1` are inside the walk. -/
def rayParity (d : Fin n → Fin 4) (a b : ℤ) : ZMod 2 := (upCross d a b : ZMod 2)

/-- The upward crossing count is the same for cells `(a, b)` and `(a, b + 1)` when no horizontal
  step lies between them. -/
lemma upCross_vstep (d : Fin n → Fin 4) (a b : ℤ)
    (h : ∀ k : Fin n, isHorizEdge (d k) →
      min ((pos d k).1) ((pos d (k+1)).1) = a → (pos d k).2 ≠ b + 1) :
    upCross d a b = upCross d a (b + 1) := by
  unfold upCross
  congr 1
  apply Finset.filter_congr
  intro k _
  by_cases hh : isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k+1)).1) = a
  · obtain ⟨h1, h2⟩ := hh
    have hne := h k h1 h2
    constructor
    · rintro ⟨_, _, hlt⟩; exact ⟨h1, h2, by omega⟩
    · rintro ⟨_, _, hlt⟩; exact ⟨h1, h2, by omega⟩
  · constructor
    · rintro ⟨a1, a2, _⟩; exact absurd ⟨a1, a2⟩ hh
    · rintro ⟨a1, a2, _⟩; exact absurd ⟨a1, a2⟩ hh

/-- The ray parity is the same for cells `(a, b)` and `(a, b + 1)` when no horizontal step lies
  between them. -/
lemma rayParity_vstep (d : Fin n → Fin 4) (a b : ℤ)
    (h : ∀ k : Fin n, isHorizEdge (d k) →
      min ((pos d k).1) ((pos d (k+1)).1) = a → (pos d k).2 ≠ b + 1) :
    rayParity d a b = rayParity d a (b + 1) := by
  unfold rayParity
  rw [upCross_vstep d a b h]

/-- Cells at or above the top height of the walk have no upward crossings. -/
lemma upCross_topOutside (d : Fin n → Fin 4) (a b T : ℤ)
    (hT : ∀ j : Fin n, (pos d j).2 ≤ T) (hb : T ≤ b) :
    upCross d a b = 0 := by
  unfold upCross
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _
  rintro ⟨_, _, hlt⟩
  have := hT k
  omega

/-- Cells at or above the top height of the walk are outside. -/
lemma rayParity_topOutside (d : Fin n → Fin 4) (a b T : ℤ)
    (hT : ∀ j : Fin n, (pos d j).2 ≤ T) (hb : T ≤ b) :
    rayParity d a b = 0 := by
  unfold rayParity
  rw [upCross_topOutside d a b T hT hb]
  simp

/-- When no vertical step separates the cells `(a, b)` and `(a + 1, b)`, their upward crossing
  counts add up to an even number. -/
lemma upCross_hstep (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 →
      ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
         b < max ((pos d k).2) ((pos d (k + 1)).2))) :
    upCross d a b + upCross d (a + 1) b
      = 2 * (Finset.univ.filter (fun k : Fin n =>
          ¬ ((pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2) ∧
            ((pos d (k + 1)).1 = a + 1 ∧ b + 1 ≤ (pos d (k + 1)).2))).card := by
  classical
  set Pin : Fin n → Prop := fun k => (pos d k).1 = a + 1 ∧ b + 1 ≤ (pos d k).2 with hPin
  set g : Fin n → ℤ := fun k => if Pin k then (1 : ℤ) else 0 with hg
  have hshift : (∑ k : Fin n, g (k + 1)) = ∑ k, g k :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin n)) g
  have htel : (∑ k : Fin n, (g (k + 1) - g k)) = 0 := by
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hper : ∀ k : Fin n, g (k + 1) - g k
      = (if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
        - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0) := by
    intro k
    simp only [hg]
    by_cases h1 : Pin k <;> by_cases h2 : Pin (k + 1) <;> simp [h1, h2]
  have hentexit :
      (Finset.univ.filter (fun k : Fin n => ¬ Pin k ∧ Pin (k + 1))).card
        = (Finset.univ.filter (fun k : Fin n => Pin k ∧ ¬ Pin (k + 1))).card := by
    have hcong : (∑ k : Fin n,
          ((if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
            - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0)))
        = ∑ k : Fin n, (g (k + 1) - g k) :=
      Finset.sum_congr rfl (fun k _ => (hper k).symm)
    have hsum : (∑ k : Fin n,
          ((if (¬ Pin k ∧ Pin (k + 1)) then (1 : ℤ) else 0)
            - (if (Pin k ∧ ¬ Pin (k + 1)) then (1 : ℤ) else 0))) = 0 := by
      rw [hcong]; exact htel
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at hsum
    exact_mod_cast hsum
  have hdisjLR : Disjoint
      (Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
        min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ b < (pos d k).2))
      (Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
        min ((pos d k).1) ((pos d (k + 1)).1) = a + 1 ∧ b < (pos d k).2)) := by
    rw [Finset.disjoint_filter]
    intro k _ hl hr
    obtain ⟨_, hla, _⟩ := hl
    obtain ⟨_, hra, _⟩ := hr
    omega
  have hdisjEE : Disjoint
      (Finset.univ.filter (fun k : Fin n => ¬ Pin k ∧ Pin (k + 1)))
      (Finset.univ.filter (fun k : Fin n => Pin k ∧ ¬ Pin (k + 1))) := by
    rw [Finset.disjoint_filter]
    intro k _ he hx
    exact absurd hx.1 he.1
  have hunion :
      (Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
          min ((pos d k).1) ((pos d (k + 1)).1) = a ∧ b < (pos d k).2))
        ∪ (Finset.univ.filter (fun k : Fin n => isHorizEdge (d k) ∧
          min ((pos d k).1) ((pos d (k + 1)).1) = a + 1 ∧ b < (pos d k).2))
      = Finset.univ.filter (fun k : Fin n =>
          (¬ Pin k ∧ Pin (k + 1)) ∨ (Pin k ∧ ¬ Pin (k + 1))) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hPin]
    have hx := fst_step d hclosed k
    have hy := snd_step d hclosed k
    rcases stepOf_coords (d k) with ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨hd, hs⟩ | ⟨hd, hs⟩
    · have hsx : (stepOf (d k)).1 = 1 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 0 := by rw [hs]
      have hH : isHorizEdge (d k) := Or.inl hd
      simp only [hH, true_and]
      omega
    · have hsx : (stepOf (d k)).1 = 0 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 1 := by rw [hs]
      have hnH : ¬ isHorizEdge (d k) := by rw [hd]; decide
      have hV : isVertEdge (d k) := Or.inl hd
      have hns := hstr k hV
      simp only [hnH, false_and, or_self, false_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hns (by omega) (by omega)
      · exact hns (by omega) (by omega)
    · have hsx : (stepOf (d k)).1 = -1 := by rw [hs]
      have hsy : (stepOf (d k)).2 = 0 := by rw [hs]
      have hH : isHorizEdge (d k) := Or.inr hd
      simp only [hH, true_and]
      omega
    · have hsx : (stepOf (d k)).1 = 0 := by rw [hs]
      have hsy : (stepOf (d k)).2 = -1 := by rw [hs]
      have hnH : ¬ isHorizEdge (d k) := by rw [hd]; decide
      have hV : isVertEdge (d k) := Or.inr hd
      have hns := hstr k hV
      simp only [hnH, false_and, or_self, false_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hns (by omega) (by omega)
      · exact hns (by omega) (by omega)
  unfold upCross
  rw [← Finset.card_union_of_disjoint hdisjLR, hunion, Finset.filter_or,
    Finset.card_union_of_disjoint hdisjEE, hentexit]
  ring

/-- The ray parity is the same for cells `(a, b)` and `(a + 1, b)` when no vertical step lies
  between them. -/
lemma rayParity_hstep (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 →
      ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
         b < max ((pos d k).2) ((pos d (k + 1)).2))) :
    rayParity d a b = rayParity d (a + 1) b := by
  have hsum := upCross_hstep d hclosed a b hstr
  have hy2 : ∀ z : ZMod 2, z + z = 0 := by decide
  have hcast : (upCross d a b : ZMod 2) + (upCross d (a + 1) b : ZMod 2) = 0 := by
    have := congrArg (fun m : ℕ => (m : ZMod 2)) hsum
    push_cast at this
    rw [this]
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]; ring
  rw [rayParity, rayParity]
  calc (upCross d a b : ZMod 2)
      = (upCross d a b : ZMod 2)
          + ((upCross d (a + 1) b : ZMod 2) + (upCross d (a + 1) b : ZMod 2)) := by
        rw [hy2]; ring
    _ = ((upCross d a b : ZMod 2) + (upCross d (a + 1) b : ZMod 2))
          + (upCross d (a + 1) b : ZMod 2) := by ring
    _ = (upCross d (a + 1) b : ZMod 2) := by rw [hcast]; ring

end StatMech.Onsager.JordanParity
