/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.BooleanCubeRectangles
import Mathlib.Tactic.NormNum

/-!
# Finite fixtures for Boolean cube rectangles

Coordinates are numbered from the least significant bit. From vertex 0 the disjoint masks 3 and 4
and the overlapping masks 3 and 7 give the same four-set {0, 3, 4, 7}. Only 3 and 4 mark its
side classes; 7 joins opposite corners. In contrast, the nonzero offsets 3, 5, 6 of the plane
{0, 3, 5, 6} intersect pairwise, so no two can serve as disjoint side masks.
-/

@[expose] public section

namespace CubeRectangleTest

-- Evaluating the three-bit finset images checks the actual unlabelled collections.
set_option maxRecDepth 8192

open Finset CubeRectangle
open scoped symmDiff

/-- Vertices of the three-dimensional test cube. -/
abbrev V := Finset (Fin 3)

/-- The two low coordinates in the block rectangle. -/
abbrev lo : V := {0, 1}

/-- The remaining high coordinate in the block rectangle. -/
abbrev hi : V := {2}

/-- The block rectangle with bit patterns 000, 011, 100 and 111. -/
abbrev box : Finset V := {∅, lo, hi, univ}

/-- In dimension two the four-set and its two marked classes are counted directly. -/
theorem square_counts : (rectangles (Fin 2)).card = 1 ∧ (markings (Fin 2)).card = 2 ∧
    ((markings (Fin 2)).filter (fun p => p.2.card = 1)).card = 2 := by decide

/-- The three-bit rectangle with integer corners 0, 3, 4, 7 has two marks of different sizes.
Vertex 0 has just one unit-distance neighbour in the four-set, ruling out a unit-edge cycle
through all four corners. -/
theorem block_example : corners (∅ : V) lo hi = box ∧ box ∈ rectangles (Fin 3) ∧
    (box, lo) ∈ markings (Fin 3) ∧ (box, hi) ∈ markings (Fin 3) ∧
    lo.card = 2 ∧ hi.card = 1 ∧ box.filter (fun v => ((∅ : V) ∆ v).card = 1) = {hi} := by
  decide

/-- The marked two-coordinate class in the block example consists of the unordered edges
0–3 and 4–7. Its restriction chart recovers the complementary low words and both backgrounds. -/
theorem edge_chart : sides box lo = {{∅, lo}, {hi, univ}} ∧
    ((chartEquiv lo ⟨box, block_example.2.2.1⟩).1 = ({∅, lo}, {∅, hi})) := by decide

/-- From 0 the overlapping masks 3 and 7 generate the rectangle {0, 3, 4, 7}. Its side masks
are 3 and 4; mask 7 joins opposite corners and is not a marking. -/
theorem overlapping_generators : corners (∅ : V) lo univ = box ∧ box ∈ rectangles (Fin 3) ∧
    (box, lo) ∈ markings (Fin 3) ∧ (box, hi) ∈ markings (Fin 3) ∧
    (box, (univ : V)) ∉ markings (Fin 3) := by decide

/-- From 0 the masks 3 and 5 generate the four-set {0, 3, 5, 6}. Its nonzero offsets 3, 5 and 6
intersect pairwise, so no two of them can be disjoint side masks. This four-set is not a rectangle. -/
theorem nonrectangular_plane : let b : V := {0, 2}; let U : Finset V := {∅, lo, b, {1, 2}};
    corners (∅ : V) lo b = U ∧ U.card = 4 ∧ U ∉ rectangles (Fin 3) := by decide

/-- There are twelve rectangles but only six ordinary unit faces in three dimensions. The
latter use singleton masks for both sides. -/
theorem cube_faces : (rectangles (Fin 3)).card = 12 ∧
    (((presentations (univ.erase (∅ : V))).filter fun p => p.2.1.card = 1 ∧ p.2.2.card = 1).image
      fun p => corners p.1 p.2.1 p.2.2).card = 6 := by
  constructor
  · have h := card_rectangles (ι := Fin 3)
    norm_num only [Fintype.card_fin, Nat.reducePow, Nat.reduceAdd] at h
    omega
  · decide

/-- The census in dimension three gives 24 marks: 18 single-coordinate and six double-coordinate
marks. -/
theorem cube_marks : (markings (Fin 3)).card = 24 ∧
    ((markings (Fin 3)).filter (fun p => p.2.card = 1)).card = 18 ∧
    ((markings (Fin 3)).filter (fun p => p.2.card = 2)).card = 6 := by
  refine ⟨by rw [card_markings, cube_faces.1], ?_, ?_⟩
  · rw [card_markings_singleton (by decide)]; decide
  · rw [card_markings_size 2 (by decide) (by decide)]; decide

/-- Dimension four gives 100 rectangles, 200 marks and size distribution 112, 72, 16. -/
theorem four_cube : (rectangles (Fin 4)).card = 100 ∧ (markings (Fin 4)).card = 200 ∧
    ((markings (Fin 4)).filter (fun p => p.2.card = 1)).card = 112 ∧
    ((markings (Fin 4)).filter (fun p => p.2.card = 2)).card = 72 ∧
    ((markings (Fin 4)).filter (fun p => p.2.card = 3)).card = 16 := by
  have solve (r : ℕ) (h : 8 * r + 2 * 4^4 = 6^4 + 2^4) : r = 100 := by omega
  have hr := solve (rectangles (Fin 4)).card (by
    simpa only [Fintype.card_fin] using card_rectangles (ι := Fin 4))
  refine ⟨hr, by rw [card_markings, hr], ?_, ?_, ?_⟩
  · rw [card_markings_singleton (by decide)]; decide
  · rw [card_markings_size 2 (by decide) (by decide)]; decide
  · rw [card_markings_size 3 (by decide) (by decide)]; decide

/-- Putting unit weight at the opposite corners 0 and 7 and zero elsewhere makes the marked
low-block product negative; with constant weights the very same mark has zero product. -/
theorem weights_example : let w := fun v : V => if v = ∅ ∨ v = univ then (1 : ℝ) else 0;
    sideProduct w ∅ lo hi = -1 ∧ sideProduct w hi lo hi = -1 ∧
      sideProduct (fun _ : V => (0 : ℝ)) ∅ lo hi = 0 := by
  dsimp only
  have eqv : corners hi lo hi = corners (∅ : V) lo hi := by decide
  rw [sideProduct_eq_of_same_mark _ (by decide) (by decide) (by decide) (by decide) (by decide) eqv]
  norm_num [sideProduct, show (∅ : V) ∆ lo = lo by decide, show (∅ : V) ∆ hi = hi by decide,
    show lo ∆ hi = univ by decide, show lo ≠ ∅ by decide, show lo ≠ univ by decide,
    show hi ≠ ∅ by decide, show hi ≠ univ by decide]

end CubeRectangleTest
