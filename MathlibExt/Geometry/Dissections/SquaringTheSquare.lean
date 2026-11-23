/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.NormNum

/-!
# Squaring the square with distinct squares

Duijvestijn's order-21 dissection gives integer coordinates in a square of side 112.
The vertical and horizontal lines through the tile edges form a grid. Checking that every
closed grid cell lies in a tile proves coverage, including on the edges of the square.
-/

namespace MathlibExt.Geometry.ScottishBook59Wanted

open Set

private structure Tile where
  x : ℕ
  y : ℕ
  side : ℕ

-- Lower left corner and side length, ordered by row and then by column.
private def tiles : Fin 21 → Tile :=
  (#v[⟨0, 0, 50⟩, ⟨50, 0, 35⟩, ⟨85, 0, 27⟩, ⟨85, 27, 8⟩, ⟨93, 27, 19⟩,
      ⟨50, 35, 15⟩, ⟨65, 35, 17⟩, ⟨82, 35, 11⟩, ⟨82, 46, 6⟩, ⟨88, 46, 24⟩,
      ⟨0, 50, 29⟩, ⟨29, 50, 25⟩, ⟨54, 50, 9⟩, ⟨63, 50, 2⟩, ⟨63, 52, 7⟩,
      ⟨70, 52, 18⟩, ⟨54, 59, 16⟩, ⟨70, 70, 42⟩, ⟨29, 75, 4⟩, ⟨33, 75, 37⟩,
      ⟨0, 79, 33⟩] : Vector Tile 21).get

private def xCuts : Fin 13 → ℕ := #v[0, 29, 33, 50, 54, 63, 65, 70, 82, 85, 88, 93, 112].get
private def yCuts : Fin 11 → ℕ := #v[0, 27, 35, 46, 50, 52, 59, 70, 75, 79, 112].get

private theorem grid_covered : ∀ (a : Fin 12) (b : Fin 10), ∃ i : Fin 21,
    (tiles i).x ≤ xCuts a.castSucc ∧ xCuts a.succ ≤ (tiles i).x + (tiles i).side ∧
    (tiles i).y ≤ yCuts b.castSucc ∧ yCuts b.succ ≤ (tiles i).y + (tiles i).side := by
  decide

private theorem tiles_separated : ∀ i j : Fin 21, i ≠ j →
    (tiles i).x + (tiles i).side ≤ (tiles j).x ∨ (tiles j).x + (tiles j).side ≤ (tiles i).x ∨
    (tiles i).y + (tiles i).side ≤ (tiles j).y ∨ (tiles j).y + (tiles j).side ≤ (tiles i).y := by
  decide

-- A point between the first and last cut belongs to a closed strip between successive cuts.
private theorem exists_strip {n : ℕ} (cut : Fin (n + 2) → ℝ) {p : ℝ}
    (h₀ : cut 0 ≤ p) (h₁ : p ≤ cut (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), cut i.castSucc ≤ p ∧ p ≤ cut i.succ := by
  induction n with
  | zero => exact ⟨0, h₀, h₁⟩
  | succ n ih =>
    by_cases h : p ≤ cut (Fin.last (n + 1)).castSucc
    · obtain ⟨i, hi⟩ := ih (fun j => cut j.castSucc) h₀ h
      exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last _, le_of_not_ge h, h₁⟩

private noncomputable def scale (k : ℕ) : ℝ := k / 112

private theorem scale_strictMono : StrictMono scale := fun _ _ h =>
  div_lt_div_of_pos_right (Nat.cast_lt.mpr h) (by norm_num)

private theorem scale_add (m n : ℕ) : scale (m + n) = scale m + scale n := by
  simp [scale, add_div]

private noncomputable def Tile.square (t : Tile) : Set (ℝ × ℝ) :=
  Icc (scale t.x, scale t.y) (scale (t.x + t.side), scale (t.y + t.side))

private theorem tiles_cover : (⋃ i, (tiles i).square) = Icc (0, 0) (1, 1) := by
  have h₀ : scale 0 = 0 := by norm_num [scale]
  have h₁ : scale 112 = 1 := by norm_num [scale]
  have mono := scale_strictMono.monotone
  apply Subset.antisymm
  · have bounds : ∀ i, (tiles i).x + (tiles i).side ≤ 112 ∧
        (tiles i).y + (tiles i).side ≤ 112 := by decide
    refine iUnion_subset fun i => Icc_subset_Icc ?_ ?_
    · rw [← h₀]
      exact ⟨mono (Nat.zero_le _), mono (Nat.zero_le _)⟩
    · rw [← h₁]
      exact ⟨mono (bounds i).1, mono (bounds i).2⟩
  · rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, hu', hv'⟩
    rw [← h₀] at hu hv
    rw [← h₁] at hu' hv'
    obtain ⟨a, ha, ha'⟩ := exists_strip (n := 11) (fun j => scale (xCuts j)) hu hu'
    obtain ⟨b, hb, hb'⟩ := exists_strip (n := 9) (fun j => scale (yCuts j)) hv hv'
    obtain ⟨i, hx, hx', hy, hy'⟩ := grid_covered a b
    exact mem_iUnion.mpr ⟨i, ⟨(mono hx).trans ha, (mono hy).trans hb⟩,
      ha'.trans (mono hx'), hb'.trans (mono hy')⟩

private theorem disjoint_interiors {i j : Fin 21} (hne : i ≠ j) :
    Disjoint (interior (tiles i).square) (interior (tiles j).square) := by
  simp only [Tile.square, Icc_prod_eq, interior_prod_eq, interior_Icc, disjoint_left]
  rintro p ⟨⟨hix, hix'⟩, hiy, hiy'⟩ ⟨⟨hjx, hjx'⟩, hjy, hjy'⟩
  have mono := scale_strictMono.monotone
  rcases tiles_separated i j hne with h | h | h | h
  · exact (hix'.trans_le (mono h)).not_ge hjx.le
  · exact (hjx'.trans_le (mono h)).not_ge hix.le
  · exact (hiy'.trans_le (mono h)).not_ge hjy.le
  · exact (hjy'.trans_le (mono h)).not_ge hiy.le

/--
**Squaring the square with distinct squares.** There are an integer $n > 1$ and real numbers
$x_i$, $y_i$ and $s_i > 0$ for $i = 1, \dots, n$, with the $s_i$ pairwise distinct, such that
the union of the closed squares $[x_i, x_i + s_i] \times [y_i, y_i + s_i]$ is the unit square
$[0, 1] \times [0, 1]$ and any two of these squares with different indices have disjoint
interiors.

Source: S. Ruziewicz, Problem 59 of the
Scottish Book, asking whether a square can be decomposed into a finite
number of squares all different from one another; the answer is
affirmative. The first published solution is R. Sprague's 1939
squaring of the square with distinct squares; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015),
and the 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867).
-/
public theorem squaringTheSquareDistinctSquares :
    ∃ (n : ℕ) (x y s : Fin n → ℝ),
      (1 < n) ∧
      (∀ i, 0 < s i) ∧
      (∀ i j, i ≠ j → s i ≠ s j) ∧
      (⋃ i, Set.Icc (x i, y i) (x i + s i, y i + s i) =
        Set.Icc (0, 0) (1, 1)) ∧
      ∀ i j, i ≠ j →
        Disjoint
          (interior (Set.Icc (x i, y i) (x i + s i, y i + s i)))
          (interior (Set.Icc (x j, y j) (x j + s j, y j + s j))) := by
  refine ⟨21, fun i => scale (tiles i).x, fun i => scale (tiles i).y,
    fun i => scale (tiles i).side, by decide, ?_, ?_, ?_, ?_⟩
  · have pos : ∀ i, 0 < (tiles i).side := by decide
    intro i
    simpa [scale] using scale_strictMono (pos i)
  · have distinct : ∀ i j, i ≠ j → (tiles i).side ≠ (tiles j).side := by decide
    exact fun i j hij => scale_strictMono.injective.ne (distinct i j hij)
  · simpa only [Tile.square, scale_add] using tiles_cover
  · intro i j hij
    simpa only [Tile.square, scale_add] using disjoint_interiors hij

end MathlibExt.Geometry.ScottishBook59Wanted
