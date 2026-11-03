/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkVertices
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting the turns of a walk without right turns

For a cyclic direction sequence `d : Fin n → Fin 4` in which every turn is straight or left, the
number of left turns out of direction `c` does not depend on `c`. Hence the total number of left
turns is `cc d = 4 * tcount d 1`, and eight or more left turns force two distinct
north-then-west corners. The file also records which steps can leave or enter an extreme vertex.

## Main definitions

* `StatMech.Onsager.NoDoubleWind2.tcount`: the number of left turns from direction `c` to `c + 1`.
* `StatMech.Onsager.NoDoubleWind2.scount`: the number of straight continuations in direction `c`.

## Main results

* `StatMech.Onsager.NoDoubleWind2.tcount_shift`: `tcount d c = tcount d (c + 1)`.
* `StatMech.Onsager.NoDoubleWind2.cc_eq_four_mul_tcount`: `cc d = 4 * tcount d 1`.
* `StatMech.Onsager.NoDoubleWind2.cc_lt_eight_of_uniqueTopCorner`: a unique north-then-west
  corner forces fewer than eight left turns.
-/

@[expose] public section

namespace StatMech.Onsager.NoDoubleWind2

open Finset
open StatMech.Onsager.BaseCase
open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]

/-- The `x`-coordinate recursion of a closed walk. See also
  `StatMech.Onsager.WalkCrossing.fst_step`. -/
theorem xco_succ (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
  rw [pos_succ d hclosed k]; rfl

/-- The `y`-coordinate recursion of a closed walk. See also
  `StatMech.Onsager.WalkCrossing.snd_step`. -/
theorem yco_succ (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
  rw [pos_succ d hclosed k]; rfl

theorem xstep_cases (w : Fin 4) :
    (w = 0 ∧ (stepOf w).1 = 1) ∨ (w = 2 ∧ (stepOf w).1 = -1) ∨
    ((w = 1 ∨ w = 3) ∧ (stepOf w).1 = 0) := by
  fin_cases w <;> simp [stepOf]

theorem ystep_cases (w : Fin 4) :
    (w = 1 ∧ (stepOf w).2 = 1) ∨ (w = 3 ∧ (stepOf w).2 = -1) ∨
    ((w = 0 ∨ w = 2) ∧ (stepOf w).2 = 0) := by
  fin_cases w <;> simp [stepOf]

/-- No east step leaves a vertex of maximal `x`-coordinate. -/
theorem maxx_no_E_out (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) : d k ≠ 0 := by
  intro hE
  have hs := xco_succ d hclosed k
  have hx1 : (stepOf (d k)).1 = 1 := by rw [hE]; rfl
  rw [hx1] at hs
  have := hmax (k + 1)
  omega

/-- No west step arrives at a vertex of maximal `x`-coordinate. -/
theorem maxx_no_W_in (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) : d (k - 1) ≠ 2 := by
  intro hW
  have hs := xco_succ d hclosed (k - 1)
  rw [sub_add_cancel] at hs
  have hx1 : (stepOf (d (k - 1))).1 = -1 := by rw [hW]; rfl
  rw [hx1] at hs
  have := hmax (k - 1)
  omega

/-- No south step leaves a vertex of minimal `y`-coordinate. -/
theorem miny_no_S_out (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) : d k ≠ 3 := by
  intro hS
  have hs := yco_succ d hclosed k
  have hy1 : (stepOf (d k)).2 = -1 := by rw [hS]; rfl
  rw [hy1] at hs
  have := hmin (k + 1)
  omega

/-- No north step arrives at a vertex of minimal `y`-coordinate. -/
theorem miny_no_N_in (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n)
    (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) : d (k - 1) ≠ 1 := by
  intro hN
  have hs := yco_succ d hclosed (k - 1)
  rw [sub_add_cancel] at hs
  have hy1 : (stepOf (d (k - 1))).2 = 1 := by rw [hN]; rfl
  rw [hy1] at hs
  have := hmin (k - 1)
  omega

/-- The number of left turns of `d` from direction `c` to direction `c + 1`. -/
def tcount (d : Fin n → Fin 4) (c : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1)).card

/-- The number of straight continuations of `d` in direction `c`. -/
def scount (d : Fin n → Fin 4) (c : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c)).card

theorem card_filter_shift (d : Fin n → Fin 4) (P : Fin 4 → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : Fin n => P (d (i + 1)))).card
    = (Finset.univ.filter (fun i : Fin n => P (d i))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n)) (fun i => if P (d i) then 1 else 0)

theorem dcount_out (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (c : Fin 4) :
    (Finset.univ.filter (fun i : Fin n => d i = c)).card = tcount d c + scount d c := by
  have hunion : Finset.univ.filter (fun i : Fin n => d i = c)
      = Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1)
        ∪ Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hc
      rcases hreflexfree i with h | h
      · exact Or.inr ⟨hc, by rw [sub_eq_zero] at h; rw [h, hc]⟩
      · refine Or.inl ⟨hc, ?_⟩
        rw [sub_eq_iff_eq_add] at h; rw [h, hc, add_comm]
    · rintro (⟨hc, _⟩ | ⟨hc, _⟩) <;> exact hc
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1))
      (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact add_ne_left.mpr one_ne_zero (h1.2.symm.trans h2.2)
  rw [hunion, Finset.card_union_of_disjoint hdisj, tcount, scount]

theorem dcount_in (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (c : Fin 4) :
    (Finset.univ.filter (fun i : Fin n => d (i + 1) = c + 1)).card
      = tcount d c + scount d (c + 1) := by
  have hunion : Finset.univ.filter (fun i : Fin n => d (i + 1) = c + 1)
      = Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1)
        ∪ Finset.univ.filter (fun i : Fin n => d i = c + 1 ∧ d (i + 1) = c + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hc
      rcases hreflexfree i with h | h
      · refine Or.inr ⟨?_, hc⟩; rw [sub_eq_zero] at h; exact h.symm.trans hc
      · refine Or.inl ⟨?_, hc⟩
        rw [sub_eq_iff_eq_add] at h
        have : d i + 1 = c + 1 := by rw [← hc, h, add_comm]
        exact add_right_cancel this
    · rintro (⟨_, hc⟩ | ⟨_, hc⟩) <;> exact hc
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => d i = c ∧ d (i + 1) = c + 1))
      (Finset.univ.filter (fun i : Fin n => d i = c + 1 ∧ d (i + 1) = c + 1)) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact add_ne_left.mpr one_ne_zero (h2.1.symm.trans h1.1)
  rw [hunion, Finset.card_union_of_disjoint hdisj, tcount, scount]

/-- In a direction sequence without right turns, every direction is left by the same number of left
  turns. -/
theorem tcount_shift (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (c : Fin 4) :
    tcount d c = tcount d (c + 1) := by
  have hin := dcount_in d hreflexfree c
  have hshift := card_filter_shift d (fun x => x = c + 1)
  have hout := dcount_out d hreflexfree (c + 1)
  rw [hshift, hout] at hin
  omega

theorem cc_eq_sum_tcount (d : Fin n → Fin 4) :
    cc d = ∑ c : Fin 4, tcount d c := by
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun i : Fin n => d (i + 1) - d i = 1))
    (t := (Finset.univ : Finset (Fin 4))) (f := fun i => d i)
    (fun x _ => Finset.mem_univ _)
  rw [cc]
  rw [hfib]
  apply Finset.sum_congr rfl
  intro c _
  rw [tcount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hturn, hc⟩
    refine ⟨hc, ?_⟩
    rw [sub_eq_iff_eq_add] at hturn
    rw [hturn, hc, add_comm]
  · rintro ⟨hc, hnext⟩
    refine ⟨?_, hc⟩
    rw [hnext, hc, add_sub_cancel_left]

/-- In a direction sequence without right turns, the number of left turns is four times the number
  of north-to-west turns. -/
theorem cc_eq_four_mul_tcount (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 * tcount d 1 := by
  have h01 : tcount d 0 = tcount d 1 := tcount_shift d hreflexfree 0
  have h12 : tcount d 1 = tcount d 2 := tcount_shift d hreflexfree 1
  have h23 : tcount d 2 = tcount d 3 := tcount_shift d hreflexfree 2
  rw [cc_eq_sum_tcount d, Fin.sum_univ_four]
  omega

theorem two_le_tcount_one (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (h8 : 8 ≤ cc d) : 2 ≤ tcount d 1 := by
  have := cc_eq_four_mul_tcount d hreflexfree
  omega

/-- Eight or more left turns, without right turns, give two distinct north-then-west corners. -/
theorem exists_two_top_corners (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (h8 : 8 ≤ cc d) :
    ∃ i j : Fin n, i ≠ j ∧ d i = 1 ∧ d (i + 1) = 2 ∧ d j = 1 ∧ d (j + 1) = 2 := by
  have h2 : 1 < (Finset.univ.filter (fun i : Fin n => d i = 1 ∧ d (i + 1) = 1 + 1)).card := by
    have := two_le_tcount_one d hreflexfree h8; rw [tcount] at this; omega
  rw [Finset.one_lt_card_iff] at h2
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  rw [Finset.mem_filter] at ha hb
  have e2 : (1 + 1 : Fin 4) = 2 := by decide
  exact ⟨a, b, hab, ha.2.1, by rw [ha.2.2, e2], hb.2.1, by rw [hb.2.2, e2]⟩

/-- If the north-then-west corner is unique, a direction sequence without right turns has fewer than
  eight left turns. -/
theorem cc_lt_eight_of_uniqueTopCorner (d : Fin n → Fin 4)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (huniq : ∀ i j : Fin n, d i = 1 → d (i + 1) = 2 → d j = 1 → d (j + 1) = 2 → i = j) :
    cc d < 8 := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨i, j, hij, hi1, hi2, hj1, hj2⟩ := exists_two_top_corners d hreflexfree hcon
  exact hij (huniq i j hi1 hi2 hj1 hj2)

end StatMech.Onsager.NoDoubleWind2
