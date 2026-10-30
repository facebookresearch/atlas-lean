/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceDomino

/-!
# Extreme cells and convex corners of finite lattice sets

An extreme cell of a set `K` of sites of `ℤ²` is the leftmost of its topmost cells: a cell with
maximal key `(y, -x)` in lexicographic order. Every finite nonempty `K` has one. The dart pointing
left out of an extreme cell is a boundary dart, and the boundary contour turns left there
(`turnZ = -1`, a convex corner of `K`), because the two cells above it are outside `K`. Hence the
boundary orbit through it has at least one convex corner and fewer concave corners than darts.

This is the existence of one convex corner, the starting point of an ear-removal induction. It is
much weaker than the two ears theorem for simple polygons (Meisters), which is not proved here.

## Main definitions

* `StatMech.Lattice.leftDart c`: the dart from `c` to its left neighbour `c + (-1, 0)`.
* `StatMech.Lattice.lexKey v`: the key `(v 1, -v 0)` in lexicographic order.
* `StatMech.Lattice.IsExtremeCell K c`: `c` is a cell of `K` with maximal key.
* `StatMech.Lattice.extremeBase K c hc`: the leftward dart of an extreme cell, as a boundary dart.

## Main results

* `StatMech.Lattice.exists_extremeCell`: every finite nonempty set of sites has an extreme cell.
* `StatMech.Lattice.extremeCell_boundary`, `StatMech.Lattice.extremeCell_turnZ`: the leftward
  dart of an extreme cell is a boundary dart with turn `-1`.
* `StatMech.Lattice.exists_convex_corner_dart`: every finite nonempty set of sites has a boundary
  dart at a convex corner.
* `StatMech.Lattice.extremeCell_orbit_one_le_leftCornerCount`,
  `StatMech.Lattice.extremeCell_orbit_rightCornerCount_lt_period`: the boundary orbit through that
  dart has a convex corner and fewer concave corners than darts.

## References

* G. H. Meisters, *Polygons have ears*, Amer. Math. Monthly 82 (1975).
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

theorem unitWt_negx : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]

/-- The dart from `c` to its left neighbour `c + (-1, 0)`. -/
noncomputable def leftDart (c : Site 2) : Dart := mkDart c ![-1, 0] unitWt_negx

@[simp] theorem leftDart_tail (c : Site 2) : (leftDart c).tail = c := rfl

theorem leftDart_dir (c : Site 2) : (leftDart c).dir = ![-1, 0] := by
  rw [leftDart, mkDart_dir]

theorem leftDart_head (c : Site 2) : (leftDart c).head = c + ![-1, 0] := by
  rw [leftDart, mkDart_head]

theorem leftDart_travel (c : Site 2) : -rot90Fun (leftDart c).dir = ![0, 1] := by
  rw [leftDart_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem leftDart_head_coord0 (c : Site 2) : (leftDart c).head 0 = c 0 - 1 := by
  rw [leftDart_head, Pi.add_apply]; simp; ring

theorem leftDart_head_coord1 (c : Site 2) : (leftDart c).head 1 = c 1 := by
  rw [leftDart_head, Pi.add_apply]; simp

theorem leftDart_front_coord0 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 0 = c 0 - 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord0]; simp

theorem leftDart_front_coord1 (c : Site 2) :
    ((leftDart c).head + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_head_coord1]; simp

theorem leftDart_side_coord0 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 0 = c 0 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp

theorem leftDart_side_coord1 (c : Site 2) :
    ((leftDart c).tail + (-rot90Fun (leftDart c).dir)) 1 = c 1 + 1 := by
  rw [leftDart_travel, Pi.add_apply, leftDart_tail]; simp

/-- The key `(y, -x)` of a site `(x, y)`, ordered lexicographically. A site with maximal key
is the leftmost of the topmost sites. -/
noncomputable def lexKey (v : Site 2) : ℤ ×ₗ ℤ := toLex (v 1, - v 0)

/-- `c` is an extreme cell of `K`: a cell of `K` with maximal key `lexKey`, i.e. the leftmost of
the topmost cells of `K`. -/
structure IsExtremeCell (K : Set (Site 2)) (c : Site 2) : Prop where
  mem : c ∈ K
  maximal : ∀ v ∈ K, lexKey v ≤ lexKey c

/-- Every finite nonempty set of sites has an extreme cell. -/
theorem exists_extremeCell (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, IsExtremeCell K c := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image hK.toFinset lexKey hfne
  refine ⟨c, ⟨by rwa [Set.Finite.mem_toFinset] at hc, ?_⟩⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])

/-- No cell of `K` lies in a row above an extreme cell. -/
theorem extremeCell_not_mem_of_higher (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : c 1 < v 1) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega

/-- No cell of `K` lies to the left of an extreme cell in its row. -/
theorem extremeCell_not_mem_of_left (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : v 1 = c 1) (hx : v 0 < c 0) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega

theorem extremeCell_front_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_front_coord1]; omega

theorem extremeCell_side_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).tail + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_side_coord1]; omega

theorem extremeCell_head_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hc
  · rw [leftDart_head_coord1]
  · rw [leftDart_head_coord0]; omega

/-- The leftward dart of an extreme cell is a boundary dart. -/
theorem extremeCell_boundary (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    IsBoundaryDart K (leftDart c) :=
  ⟨by rw [leftDart_tail]; exact hc.mem, extremeCell_head_nmem K c hc⟩

/-- The boundary contour turns left (a convex corner, `turnZ = -1`) at the leftward dart of an
extreme cell. -/
theorem extremeCell_turnZ (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    turnZ K (leftDart c) = -1 := by
  unfold turnZ
  rw [ite_eq_right (extremeCell_front_nmem K c hc), ite_eq_right (extremeCell_side_nmem K c hc)]

/-- Every finite nonempty set of sites has a boundary dart at which the contour turns left, i.e. a
convex corner. -/
theorem exists_convex_corner_dart (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨leftDart c, extremeCell_boundary K c hc, extremeCell_turnZ K c hc⟩

/-- A walk of positive length along the boundary that starts at a convex corner has at least one
convex corner. -/
theorem one_le_leftCornerCount_of_first (K : Set (Site 2)) (e : Dart) (p : ℕ) (hp : 0 < p)
    (h0 : turnZ K e = -1) : 1 ≤ leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  have hmem : 0 ∈ (Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hp, by rw [Function.iterate_zero_apply]; exact h0⟩
  have : 1 ≤ ((Finset.range p).filter
      (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this

/-- The leftward dart of an extreme cell, as an element of the subtype of boundary darts. -/
noncomputable def extremeBase (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    {e : Dart // IsBoundaryDart K e} :=
  ⟨leftDart c, extremeCell_boundary K c hc⟩

/-- The boundary orbit through the leftward dart of an extreme cell has at least one convex
corner. -/
theorem extremeCell_orbit_one_le_leftCornerCount (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    1 ≤ leftCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) := by
  apply one_le_leftCornerCount_of_first
  · exact dartOrbitPeriod_pos K hK (extremeBase K c hc)
  · change turnZ K (leftDart c) = -1
    exact extremeCell_turnZ K c hc

/-- The boundary orbit through the leftward dart of an extreme cell has fewer concave corners than
darts. -/
theorem extremeCell_orbit_rightCornerCount_lt_period (K : Set (Site 2)) (hK : K.Finite)
    (c : Site 2) (hc : IsExtremeCell K c) :
    rightCornerCount K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc)) <
      (dartOrbitPeriod K (extremeBase K c hc) : ℤ) := by
  have hpart :=
    orbitStep_partition K (extremeBase K c hc).1 (dartOrbitPeriod K (extremeBase K c hc))
  have hleft := extremeCell_orbit_one_le_leftCornerCount K hK c hc
  have hstraight : (0 : ℤ) ≤ straightStepCount K (extremeBase K c hc).1
      (dartOrbitPeriod K (extremeBase K c hc)) := by
    unfold straightStepCount; positivity
  linarith

/-- Removing an extreme cell from a finite set lowers its cardinality. -/
theorem removeExtremeCell_ncard_lt (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) : (K \ {c}).ncard < K.ncard :=
  Set.ncard_sdiff_singleton_lt_of_mem hc.mem hK

end Lattice

end StatMech
