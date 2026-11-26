/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffSupportConnected

/-!
# Connectivity off a bounded set through the exterior of a box

Let `B` be a set of sites contained in the box `box 2 R = [-R, R]²`. The exterior of the box
(`exterior 2 R`, the sites with some coordinate of absolute value `> R`) is connected and misses
`B`, so the complement of `B` is connected as soon as every site off `B` can walk to the
exterior without meeting `B`. This file sets up that criterion, `arcxc_ReachesExterior`, and
proves it for a single site and for sites whose row is clear to the right edge of the box.

## Main definitions

* `StatMech.Lattice.arcxc_extToOffSupportHom`: the inclusion of the box exterior into the
  lattice with `B` removed, as a graph homomorphism.
* `StatMech.Lattice.arcxc_ReachesExterior B R`: `B ⊆ box 2 R`, and every site off `B` reaches
  the exterior of the box by a walk avoiding `B`.

## Main results

* `StatMech.Lattice.arcxc_exterior_reachable_offSupport`: two exterior sites are connected in the
  lattice with `B` removed.
* `StatMech.Lattice.arcxc_connected_of_reachesExterior`: `arcxc_ReachesExterior B R` implies
  that the complement of `B` is connected (`arcns_OffSupportConnected B`).
* `StatMech.Lattice.arcxc_reachesExterior_of_rowClear`: a site whose row is free of `B` from it
  to column `R + 1` reaches the exterior.
* `StatMech.Lattice.arcxc_singlePoint_reachesExterior`: the criterion holds for a single site.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Sites outside the box are not in `B ⊆ box 2 R`. This is `exterior_subset_compl` stated
elementwise. -/
theorem arcxc_exterior_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {z : Site 2}
    (hz : z ∈ exterior 2 R) : z ∉ B := by
  intro hzB
  rw [exterior_eq_compl_box] at hz
  exact hz (hB hzB)

theorem arcxc_exterior_adj_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {x y : Site 2}
    (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) (hadj : (hypercubicLattice 2).Adj x y) :
    (ffc_offSupportLattice B).Adj x y :=
  ⟨hadj, arcxc_exterior_offSupport hB hx, arcxc_exterior_offSupport hB hy⟩

/-- The inclusion of the induced graph on the box exterior into the lattice with `B` removed,
for `B ⊆ box 2 R`. -/
noncomputable def arcxc_extToOffSupportHom {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) :
    (hypercubicLattice 2).induce (exterior 2 R) →g ffc_offSupportLattice B where
  toFun := fun z => (z : Site 2)
  map_rel' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hadj
    exact arcxc_exterior_adj_offSupport hB hx hy hadj

/-- Two sites outside the box are connected in the lattice with `B ⊆ box 2 R` removed. See also
`exterior_reachable_compl`, the same statement for the induced graph on `Bᶜ`. -/
theorem arcxc_exterior_reachable_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (ffc_offSupportLattice B).Reachable x y := by
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map (arcxc_extToOffSupportHom hB)
  simpa [arcxc_extToOffSupportHom] using hmap

/-- Two sites outside the box are joined by a lattice walk avoiding `B ⊆ box 2 R`. -/
theorem arcxc_exterior_walk_offSupport {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B :=
  (ffc_reachable_iff_offSupportWalk (arcxc_exterior_offSupport hB hx)).mp
    (arcxc_exterior_reachable_offSupport hB hx hy)

/-- `B` lies in the box `box 2 R`, and every site off `B` reaches the exterior of the box by a
lattice walk avoiding `B`. -/
def arcxc_ReachesExterior (B : Set (Site 2)) (R : ℕ) : Prop :=
  B ⊆ box 2 R ∧
    ∀ x : Site 2, x ∉ B → ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk x e),
      (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R

/-- If every site off `B ⊆ box 2 R` walks to the exterior avoiding `B`, the complement of `B` is
connected. -/
theorem arcxc_connected_of_reachesExterior {B : Set (Site 2)} {R : ℕ}
    (h : arcxc_ReachesExterior B R) : arcns_OffSupportConnected B := by
  obtain ⟨hB, hreach⟩ := h
  intro x y hx hy
  obtain ⟨ex, px, hpx, hex⟩ := hreach x hx
  obtain ⟨ey, py, hpy, hey⟩ := hreach y hy
  refine ((?_ : (ffc_offSupportLattice B).Reachable x ex).trans
    (?_ : (ffc_offSupportLattice B).Reachable ex ey)).trans
    (?_ : (ffc_offSupportLattice B).Reachable ey y)
  · exact (ffc_reachable_iff_offSupportWalk hx).mpr ⟨px, hpx⟩
  · exact arcxc_exterior_reachable_offSupport hB hex hey
  · exact ((ffc_reachable_iff_offSupportWalk hy).mpr ⟨py, hpy⟩).symm

theorem arcxc_mem_exterior_of_col_high (R : ℕ) {z : Site 2} (hz : (R : ℤ) + 1 ≤ z 0) :
    z ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  have h2 : (R : ℤ) < |z 0| :=
    lt_of_lt_of_le (by omega : (R : ℤ) < z 0) (le_abs_self _)
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2

theorem arcxc_mem_exterior_of_row_high (R : ℕ) {z : Site 2} (hz : (R : ℤ) + 1 ≤ z 1) :
    z ∈ exterior 2 R := by
  refine ⟨1, ?_⟩
  have h2 : (R : ℤ) < |z 1| :=
    lt_of_lt_of_le (by omega : (R : ℤ) < z 1) (le_abs_self _)
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2

/-- If no site `(t, z 1)` with `t` between `z 0` and `R + 1` lies in `B`, then `z` reaches the
exterior site `(R + 1, z 1)` along its row avoiding `B`. -/
theorem arcxc_reachesExterior_of_rowClear {B : Set (Site 2)} {R : ℕ} {z : Site 2}
    (hrow : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ B) :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e),
      (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
  set e : Site 2 := ![(R : ℤ) + 1, z 1] with he
  have heExt : e ∈ exterior 2 R := arcxc_mem_exterior_of_col_high R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, p, ?_, heExt⟩
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  exact hrow t ht

/-- A site off `B ⊆ box 2 R` in a column `≥ R` reaches the exterior avoiding `B`. -/
theorem arcxc_reachesExterior_of_col_ge {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {z : Site 2}
    (hzcol : (R : ℤ) ≤ z 0) (hzoff : z ∉ B) :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e),
      (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
  rcases lt_or_ge (R : ℤ) (z 0) with hlt | hge
  · refine ⟨z, SimpleGraph.Walk.nil, ?_, arcxc_mem_exterior_of_col_high R (by omega)⟩
    intro w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    exact hw ▸ hzoff
  · have hzR : z 0 = R := le_antisymm hge hzcol
    apply arcxc_reachesExterior_of_rowClear
    intro t ht hmem
    rw [Set.mem_uIcc] at ht
    have htbox : (![t, z 1] : Site 2) ∈ box 2 R := hB hmem
    have htabs : t.natAbs ≤ R := by have := htbox 0; simpa using this
    have htle : t ≤ (R : ℤ) := by
      have : |t| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast htabs
      exact (abs_le.mp this).2
    have htR : t = (R : ℤ) := by omega
    subst htR
    have hzeq : (![(R : ℤ), z 1] : Site 2) = z := by
      ext i; fin_cases i
      · simpa using hzR.symm
      · simp
    rw [hzeq] at hmem
    exact hzoff hmem

/-- A single site `u` in the box satisfies the exterior-reachability criterion: every other site
reaches column `R + 1` by an L-shaped walk avoiding `u`. -/
theorem arcxc_singlePoint_reachesExterior (u : Site 2) {R : ℕ} (hu : u ∈ box 2 R) :
    arcxc_ReachesExterior ({u} : Set (Site 2)) R := by
  classical
  refine ⟨by intro q hq; rw [Set.mem_singleton_iff] at hq; subst hq; exact hu, ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  set r : ℤ := if x 1 = u 1 then x 1 + 1 else x 1 with hr
  have hru : r ≠ u 1 := by rw [hr]; split_ifs with h <;> omega
  have hx0ne : x 1 = u 1 → x 0 ≠ u 0 := by
    intro h hc; exact hx (by funext i; fin_cases i <;> simp_all)
  set e : Site 2 := ![(R : ℤ) + 1, r] with he
  have heExt : e ∈ exterior 2 R := arcxc_mem_exterior_of_col_high R (by rw [he]; simp)
  have estart : (![x 0, x 1] : Site 2) = x := by funext i; fin_cases i <;> rfl
  refine ⟨e, (arcns_vlshape (x 0) (x 1) ((R : ℤ) + 1) r).copy estart rfl, ?_, heExt⟩
  intro w hw hwu
  rw [Set.mem_singleton_iff] at hwu
  rw [Walk.support_copy, arcns_vlshape_support] at hw
  rcases hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hw0 : x 0 = u 0 := by have := congrFun hwu 0; simpa using this
    have hw1 : t = u 1 := by have := congrFun hwu 1; simpa using this
    by_cases hc : x 1 = u 1
    · exact hx0ne hc hw0
    · rw [hr, ite_eq_right hc, Set.uIcc_self, Set.mem_singleton_iff] at ht
      exact hc (by rw [← ht, hw1])
  · have hw1 : r = u 1 := by have := congrFun hwu 1; simpa using this
    exact hru hw1

/-- If `insert u' S` satisfies the exterior-reachability criterion, adding `u'` to `S` keeps
the complement connected. -/
theorem arcxc_leafRemovable_of_reachesExterior {S : Set (Site 2)} {u' : Site 2} {R : ℕ}
    (h : arcxc_ReachesExterior (insert u' S) R) : arcns_LeafRemovable S u' :=
  fun _ => arcxc_connected_of_reachesExterior h

theorem arcxc_exterior_reachesExterior {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R) {z : Site 2}
    (hz : z ∈ exterior 2 R) :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk z e),
      (∀ w ∈ p.support, w ∉ B) ∧ e ∈ exterior 2 R := by
  refine ⟨z, SimpleGraph.Walk.nil, ?_, hz⟩
  intro w hw
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
  exact hw ▸ arcxc_exterior_offSupport hB hz

/-- If every site off `B` has a clear row to column `R + 1`, then `B` satisfies the
exterior-reachability criterion. -/
theorem arcxc_reachesExterior_of_allRowClear {B : Set (Site 2)} {R : ℕ} (hB : B ⊆ box 2 R)
    (hall : ∀ z : Site 2, z ∉ B →
        ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ B) :
    arcxc_ReachesExterior B R :=
  ⟨hB, fun z hz => arcxc_reachesExterior_of_rowClear (hall z hz)⟩

end Lattice

end StatMech
