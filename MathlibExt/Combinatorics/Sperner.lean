/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sperner's lemma in dimensions one and two

Sperner's lemma is the combinatorial core of Brouwer's fixed-point theorem and the prototype of
the parity ("END-OF-THE-LINE") arguments that define the complexity class PPAD
(Papadimitriou 1994; Daskalakis, Goldberg and Papadimitriou 2009, Section 3.3).

* Dimension one: a `{0, 1}`-colouring of the points `0, 1, …, n` with `c 0 = 0` and `c n = 1`
  has an odd number of bichromatic unit segments.
* Dimension two: subdivide the triangle with corners `(0, 0)`, `(n, 0)` and `(0, n)` into the
  `n²` unit triangles of the grid: the "up" cells `{(i, j), (i + 1, j), (i, j + 1)}` with
  `i + j < n` and the "down" cells `{(i + 1, j), (i, j + 1), (i + 1, j + 1)}` with
  `i + j + 2 ≤ n`. Colour the grid points with `0, 1, 2` so that points on the side opposite
  corner `k` never get colour `k` (Sperner's boundary condition). Then the number of
  trichromatic (rainbow) cells is odd; in particular one exists.

The proof is the door-counting argument: in `ZMod 2`, the rainbow indicator of a cell equals
the number of its `{0, 1}`-coloured edges; interior edges are shared by two cells and cancel, the
edges on the two sides not joining corners `0` and `1` carry no door, and the bottom side carries
an odd number of doors by the one-dimensional lemma.

The general `n`-dimensional lemma, on iterated barycentric subdivisions of a simplex, is proved
privately inside `MathlibExt.Analysis.Convex.KKM` and used there for the
Knaster–Kuratowski–Mazurkiewicz lemma; this module records the low-dimensional cases on the
standard grid triangulation as public, reusable statements.

## References

* E. Sperner, "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes",
  Abh. Math. Sem. Univ. Hamburg 6 (1928), 265–272.
* C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, "The complexity of computing a Nash
  equilibrium", SIAM J. Comput. 39(1) (2009), 195–259, Section 3.3 (Sperner's lemma as the
  existence argument behind the problem BROUWER).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Sperner

open Finset

/-! ### Dimension one -/

/-- Indicator of colour `1` in `ZMod 2`. -/
private def ind (a : Fin 2) : ZMod 2 := if a = 1 then 1 else 0

private lemma ne_ind (a b : Fin 2) :
    (if a ≠ b then (1 : ZMod 2) else 0) = ind a + ind b := by
  revert a b; decide

private lemma sum_ne_ind (c : ℕ → Fin 2) (n : ℕ) :
    ∑ i ∈ range n, (if c i ≠ c (i + 1) then (1 : ZMod 2) else 0) = ind (c 0) + ind (c n) := by
  induction n with
  | zero =>
    have h : ∀ x : ZMod 2, x + x = 0 := by decide
    simp [h]
  | succ k ih =>
    rw [sum_range_succ, ih, ne_ind]
    have h : ∀ x : ZMod 2, x + x = 0 := by decide
    linear_combination h (ind (c k))

/-- **Sperner's lemma in dimension one.** Colour the points `0, 1, …, n` with two colours so that
`c 0 = 0` and `c n = 1`. Then the number of indices `i < n` with `c i ≠ c (i + 1)` (bichromatic
unit segments) is odd; in particular there is at least one.

Source: E. Sperner, "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes",
Abh. Math. Sem. Univ. Hamburg 6 (1928), 265–272 (the one-dimensional case of his lemma). -/
theorem odd_card_bichromatic (c : ℕ → Fin 2) (n : ℕ) (h0 : c 0 = 0) (hn : c n = 1) :
    Odd ((range n).filter (fun i => c i ≠ c (i + 1))).card := by
  rw [← ZMod.natCast_eq_one_iff_odd, card_filter, Nat.cast_sum]
  have := sum_ne_ind c n
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at this ⊢
  rw [this, h0, hn]
  decide

/-! ### Dimension two -/

/-- **Rainbow triple of colours.** Three colours in `{0, 1, 2}` are pairwise distinct, so that a
cell with these vertex colours is fully labelled. -/
def IsRainbow (a b c : Fin 3) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

instance (a b c : Fin 3) : Decidable (IsRainbow a b c) := by
  unfold IsRainbow; infer_instance

/-- **Up cells of the grid triangulation.** The index pairs `(i, j)` with `i + j < n`; the pair
stands for the unit triangle with vertices `(i, j)`, `(i + 1, j)` and `(i, j + 1)`. -/
def upCells (n : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun p => p.1 + p.2 < n)

/-- **Down cells of the grid triangulation.** The index pairs `(i, j)` with `i + j + 2 ≤ n`; the
pair stands for the unit triangle with vertices `(i + 1, j)`, `(i, j + 1)` and
`(i + 1, j + 1)`. Together with the up cells they triangulate the triangle with corners
`(0, 0)`, `(n, 0)` and `(0, n)` into `n²` unit triangles. -/
def downCells (n : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun p => p.1 + p.2 + 2 ≤ n)

/-- **Sperner colouring of the grid triangle.** A colouring `c i j ∈ {0, 1, 2}` of the grid
points of the triangle with corners `(0, 0)`, `(n, 0)` and `(0, n)` such that points on the
bottom side (`j = 0`) avoid colour `2`, points on the left side (`i = 0`) avoid colour `1`, and
points on the hypotenuse (`i + j = n`) avoid colour `0`. The corners are then forced to have
colours `0`, `1` and `2` (for `n ≥ 1`; for `n = 0` no colouring qualifies). -/
structure IsSpernerColouring (n : ℕ) (c : ℕ → ℕ → Fin 3) : Prop where
  bottom : ∀ i ≤ n, c i 0 ≠ 2
  left : ∀ j ≤ n, c 0 j ≠ 1
  hypotenuse : ∀ i ≤ n, c i (n - i) ≠ 0

/-- Door indicator in `ZMod 2`: the edge with end colours `a`, `b` has colours exactly `{0, 1}`. -/
private def door (a b : Fin 3) : ZMod 2 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0

private def rb (a b c : Fin 3) : ZMod 2 := if IsRainbow a b c then 1 else 0

private lemma rb_eq (a b c : Fin 3) : rb a b c = door a b + door b c + door a c := by
  revert a b c; decide

private def ind3 (a : Fin 3) : ZMod 2 := if a = 1 then 1 else 0

private lemma door_eq_ind (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) :
    door a b = ind3 a + ind3 b := by
  revert a b; decide

private lemma door_of_ne_one (a b : Fin 3) (ha : a ≠ 1) (hb : b ≠ 1) : door a b = 0 := by
  revert a b; decide

private lemma door_of_ne_zero (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0) : door a b = 0 := by
  revert a b; decide

private lemma sum_upCells {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ × ℕ → M) :
    ∑ p ∈ upCells n, g p = ∑ j ∈ range n, ∑ i ∈ range (n - j), g (i, j) := by
  rw [upCells, sum_filter, sum_product_right]
  refine sum_congr rfl (fun j hj => ?_)
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range] at hj ⊢
  omega

private lemma sum_downCells {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ × ℕ → M) :
    ∑ p ∈ downCells (m + 1), g p = ∑ j ∈ range (m + 1), ∑ i ∈ range (m - j), g (i, j) := by
  rw [downCells, sum_filter, sum_product_right]
  refine sum_congr rfl (fun j hj => ?_)
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range] at hj ⊢
  omega

private lemma bottom_doors (c : ℕ → ℕ → Fin 3) (n : ℕ) (hb : ∀ i ≤ n, c i 0 ≠ 2) :
    ∀ k ≤ n, ∑ i ∈ range k, door (c i 0) (c (i + 1) 0) = ind3 (c 0 0) + ind3 (c k 0) := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  intro k
  induction k with
  | zero => intro _; simp [h2]
  | succ k ih =>
    intro hk
    rw [sum_range_succ, ih (by omega), door_eq_ind _ _ (hb k (by omega)) (hb (k + 1) hk)]
    linear_combination h2 (ind3 (c k 0))

/-- **Sperner's lemma in dimension two (parity form).** For every Sperner colouring `c` of the
grid triangle with corners `(0, 0)`, `(n, 0)` and `(0, n)` (`IsSpernerColouring`), the number of
rainbow cells of the grid triangulation, up cells plus down cells, is odd.

This is the two-dimensional case of E. Sperner, "Neuer Beweis für die Invarianz der
Dimensionszahl und des Gebietes", Abh. Math. Sem. Univ. Hamburg 6 (1928), 265–272, for the
particular triangulation by the unit grid; Sperner proves it for arbitrary triangulations of a
simplex, which this statement does not cover. The proof counts `{0, 1}`-doors modulo 2. -/
theorem odd_card_rainbow {n : ℕ} {c : ℕ → ℕ → Fin 3} (hc : IsSpernerColouring n c) :
    Odd (((upCells n).filter
        (fun p => IsRainbow (c p.1 p.2) (c (p.1 + 1) p.2) (c p.1 (p.2 + 1)))).card +
      ((downCells n).filter
        (fun p => IsRainbow (c (p.1 + 1) p.2) (c p.1 (p.2 + 1))
          (c (p.1 + 1) (p.2 + 1)))).card) := by
  obtain ⟨hb, hl, hh⟩ := hc
  have hh' : ∀ i j, i + j = n → c i j ≠ 0 := by
    intro i j hij
    have := hh i (by omega)
    rwa [show n - i = j by omega] at this
  -- For `n = 0` no colouring is a Sperner colouring.
  obtain _ | m := n
  · exact absurd (hh' 0 0 rfl) (by
      have h1 := hb 0 le_rfl
      have h2 := hl 0 le_rfl
      revert h1 h2
      generalize c 0 0 = a
      revert a
      decide)
  rw [← ZMod.natCast_eq_one_iff_odd, Nat.cast_add, card_filter, card_filter, Nat.cast_sum,
    Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  change ∑ p ∈ upCells (m + 1), rb (c p.1 p.2) (c (p.1 + 1) p.2) (c p.1 (p.2 + 1)) +
      ∑ p ∈ downCells (m + 1),
        rb (c (p.1 + 1) p.2) (c p.1 (p.2 + 1)) (c (p.1 + 1) (p.2 + 1)) = 1
  rw [sum_upCells, sum_downCells, ← sum_add_distrib]
  -- Edge indicators.
  set h : ℕ → ℕ → ZMod 2 := fun i j => door (c i j) (c (i + 1) j) with hh_def
  set v : ℕ → ℕ → ZMod 2 := fun i j => door (c i j) (c i (j + 1)) with hv_def
  set d : ℕ → ℕ → ZMod 2 := fun i j => door (c (i + 1) j) (c i (j + 1)) with hd_def
  set H : ℕ → ZMod 2 := fun j => ∑ i ∈ range (m + 1 - j), h i j with hH_def
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hrow : ∀ j ∈ range (m + 1),
      ∑ i ∈ range (m + 1 - j), rb (c i j) (c (i + 1) j) (c i (j + 1)) +
        ∑ i ∈ range (m - j), rb (c (i + 1) j) (c i (j + 1)) (c (i + 1) (j + 1)) =
      (H (j + 1) - H j) + v 0 j + d (m - j) j := by
    intro j hj
    have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
    have hsucc : m + 1 - j = (m - j) + 1 := by omega
    have hH1 : H (j + 1) = ∑ i ∈ range (m - j), h i (j + 1) := by
      simp only [hH_def]
      rw [show m + 1 - (j + 1) = m - j by omega]
    simp only [rb_eq]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have eU_d : ∑ i ∈ range (m + 1 - j), door (c (i + 1) j) (c i (j + 1)) =
        ∑ i ∈ range (m - j), d i j + d (m - j) j := by
      rw [hsucc, sum_range_succ]
    have eU_v : ∑ i ∈ range (m + 1 - j), door (c i j) (c i (j + 1)) =
        ∑ i ∈ range (m - j), v (i + 1) j + v 0 j := by
      rw [hsucc, sum_range_succ']
    have eU_h : ∑ i ∈ range (m + 1 - j), door (c i j) (c (i + 1) j) = H j := rfl
    have eD_h : ∑ i ∈ range (m - j), door (c i (j + 1)) (c (i + 1) (j + 1)) = H (j + 1) := by
      rw [hH1]
    rw [eU_d, eU_v, eU_h, eD_h]
    change H j + (∑ i ∈ range (m - j), d i j + d (m - j) j) +
        (∑ i ∈ range (m - j), v (i + 1) j + v 0 j) +
        (∑ i ∈ range (m - j), d i j + H (j + 1) + ∑ i ∈ range (m - j), v (i + 1) j) =
      H (j + 1) - H j + v 0 j + d (m - j) j
    linear_combination h2 (∑ i ∈ range (m - j), d i j) +
      h2 (∑ i ∈ range (m - j), v (i + 1) j) + h2 (H j)
  rw [sum_congr rfl hrow, sum_add_distrib, sum_add_distrib, sum_range_sub]
  have hv0 : ∑ j ∈ range (m + 1), v 0 j = 0 := by
    refine sum_eq_zero (fun j hj => ?_)
    have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
    exact door_of_ne_one _ _ (hl j (by omega)) (hl (j + 1) (by omega))
  have hd0 : ∑ j ∈ range (m + 1), d (m - j) j = 0 := by
    refine sum_eq_zero (fun j hj => ?_)
    have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
    exact door_of_ne_zero _ _ (hh' _ _ (by omega)) (hh' _ _ (by omega))
  have hHtop : H (m + 1) = 0 := by simp [hH_def]
  have hH0 : H 0 = 1 := by
    simp only [hH_def, Nat.sub_zero, hh_def]
    rw [bottom_doors c (m + 1) hb (m + 1) le_rfl]
    have c00 : c 0 0 = 0 := by
      have h1 := hb 0 (by omega)
      have h3 := hl 0 (by omega)
      revert h1 h3
      generalize c 0 0 = a
      revert a
      decide
    have cm0 : c (m + 1) 0 = 1 := by
      have h1 := hb (m + 1) le_rfl
      have h3 := hh' (m + 1) 0 rfl
      revert h1 h3
      generalize c (m + 1) 0 = a
      revert a
      decide
    rw [c00, cm0]
    decide
  rw [hv0, hd0, hHtop, hH0]
  decide

/-- **Sperner's lemma in dimension two.** Every Sperner colouring of the grid triangle with
corners `(0, 0)`, `(n, 0)` and `(0, n)` has a rainbow cell: an up cell
`{(i, j), (i + 1, j), (i, j + 1)}` or a down cell `{(i + 1, j), (i, j + 1), (i + 1, j + 1)}`
whose three vertices carry the three colours. Immediate from the parity form
`odd_card_rainbow` (Sperner 1928, two-dimensional case, for the grid triangulation). -/
theorem exists_rainbow {n : ℕ} {c : ℕ → ℕ → Fin 3} (hc : IsSpernerColouring n c) :
    (∃ p ∈ upCells n, IsRainbow (c p.1 p.2) (c (p.1 + 1) p.2) (c p.1 (p.2 + 1))) ∨
      ∃ p ∈ downCells n, IsRainbow (c (p.1 + 1) p.2) (c p.1 (p.2 + 1)) (c (p.1 + 1) (p.2 + 1)) := by
  have hodd := odd_card_rainbow hc
  by_contra hno
  push Not at hno
  obtain ⟨hU, hD⟩ := hno
  rw [filter_false_of_mem hU, filter_false_of_mem hD] at hodd
  simp at hodd

end MathlibExt.Combinatorics.Sperner
