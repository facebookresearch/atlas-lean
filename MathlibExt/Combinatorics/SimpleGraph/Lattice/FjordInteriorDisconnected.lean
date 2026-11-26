/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.SegmentDownCounterexample

/-!
# A simple closed lattice walk with a disconnected interior

The interior sites of a simple closed walk in the square lattice need not be connected in the
lattice with the walk removed. For the slotted rectangle walk `sdc_fjord`, the right room
`iwc_RightPocket = {5, 6} × {1, 2, 3}` is closed under lattice steps to sites off the walk, so no
lattice path avoiding the walk joins the interior sites `(5, 1)` and `(1, 1)`
(`iwc_interior_disconnected`), and no seed is row-linked (`iwc_exists_rowLinked_seed_false`).

The walk is simple but not 4-thin in the sense of `mci_FourThin`: the support sites `(3, 1)` and
`(4, 1)` are lattice neighbours without being joined by an edge of the walk
(`mci_fjord_not_fourThin`). In digital topology, Rosenfeld's Jordan curve theorem is stated for
simple closed 4-curves, in which each site has exactly two lattice neighbours on the curve; such
curves have an 8-connected (king-move connected) interior. The fjord walk is outside that class,
and its interior is not king-move connected either: the two rooms are three columns apart.

## Main definitions

* `StatMech.Lattice.iwc_RightPocket`: the right room `{5, 6} × {1, 2, 3}` of `sdc_fjord`.

## Main results

* `StatMech.Lattice.iwc_offSupport_walk_in_rightPocket`: a lattice walk avoiding `sdc_fjord` that
  starts in the right room stays there.
* `StatMech.Lattice.iwc_interior_disconnected`: `(5, 1)` and `(1, 1)` are off-support interior
  sites of `sdc_fjord` with no lattice path between them avoiding the walk.
* `StatMech.Lattice.iwc_exists_rowLinked_seed_false`: `sdc_fjord` has no row-linked seed.

## References

* A. Rosenfeld, *Arcs and curves in digital pictures*, J. ACM 20 (1973), 81–87.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The right room `{5, 6} × {1, 2, 3}` of the fjord walk `sdc_fjord`. -/
def iwc_RightPocket : Set (Site 2) :=
  {z | (z 0 = 5 ∨ z 0 = 6) ∧ (z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3)}

@[simp] theorem iwc_mem_rightPocket (z : Site 2) :
    z ∈ iwc_RightPocket ↔ (z 0 = 5 ∨ z 0 = 6) ∧ (z 1 = 1 ∨ z 1 = 2 ∨ z 1 = 3) := Iff.rfl

theorem iwc_on_42 : (![4, 2] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left
  exact sdc_vsegUp_mem' 4 0 3 2 (by norm_num) (by norm_num)

theorem iwc_on_43 : (![4, 3] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; left
  exact sdc_vsegUp_mem' 4 0 3 3 (by norm_num) (by norm_num)

theorem iwc_on_72 : (![7, 2] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 7 0 4 2 (by norm_num) (by norm_num)

theorem iwc_on_73 : (![7, 3] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 7 0 4 3 (by norm_num) (by norm_num)

theorem iwc_on_54 : (![5, 4] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; right; left
  exact sdc_hsegRight_mem' 4 0 7 5 (by norm_num) (by norm_num)

theorem iwc_on_64 : (![6, 4] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; right; left
  exact sdc_hsegRight_mem' 4 0 7 6 (by norm_num) (by norm_num)

/-- A lattice step from the right room to a site off `sdc_fjord` stays in the right room. -/
theorem iwc_rightPocket_step {u v : Site 2} (hu : u ∈ iwc_RightPocket)
    (hadj : (hypercubicLattice 2).Adj u v) (hv : v ∉ sdc_fjord.support) :
    v ∈ iwc_RightPocket := by
  rw [iwc_mem_rightPocket] at hu ⊢
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  obtain ⟨hu0, hu1⟩ := hu
  have hadj' : (v 0 = u 0 + 1 ∧ v 1 = u 1) ∨ (v 0 = u 0 - 1 ∧ v 1 = u 1) ∨
      (v 0 = u 0 ∧ v 1 = u 1 + 1) ∨ (v 0 = u 0 ∧ v 1 = u 1 - 1) := by omega
  by_contra hvnot
  apply hv
  have hframe : (v 0 = 4 ∧ v 1 = 1) ∨ (v 0 = 4 ∧ v 1 = 2) ∨ (v 0 = 4 ∧ v 1 = 3) ∨
      (v 0 = 7 ∧ v 1 = 1) ∨ (v 0 = 7 ∧ v 1 = 2) ∨ (v 0 = 7 ∧ v 1 = 3) ∨
      (v 0 = 5 ∧ v 1 = 0) ∨ (v 0 = 6 ∧ v 1 = 0) ∨
      (v 0 = 5 ∧ v 1 = 4) ∨ (v 0 = 6 ∧ v 1 = 4) := by
    simp only [not_and_or] at hvnot
    clear hadj hv
    rcases hu0 with hu0 | hu0 <;> rcases hu1 with hu1 | hu1 | hu1 <;>
      rcases hadj' with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;> omega
  have hveq : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  rw [hveq]
  rcases hframe with ⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩ <;> rw [a, b]
  · exact sdc_fjord_on_41
  · exact iwc_on_42
  · exact iwc_on_43
  · exact sdc_fjord_on_71
  · exact iwc_on_72
  · exact iwc_on_73
  · exact sdc_fjord_on_50
  · exact sdc_fjord_on_60
  · exact iwc_on_54
  · exact iwc_on_64

/-- A lattice walk avoiding `sdc_fjord` that starts in the right room stays in the right room. -/
theorem iwc_offSupport_walk_in_rightPocket {x y : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (hp : ∀ w ∈ p.support, w ∉ sdc_fjord.support)
    (hx : x ∈ iwc_RightPocket) : ∀ w ∈ p.support, w ∈ iwc_RightPocket := by
  induction p with
  | nil =>
    intro w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    exact hw ▸ hx
  | @cons a b c hab q ih =>
    have hboff : b ∉ sdc_fjord.support := hp b (by
      rw [SimpleGraph.Walk.support_cons]; right; exact q.start_mem_support)
    have hbRP : b ∈ iwc_RightPocket := iwc_rightPocket_step hx hab hboff
    have hq : ∀ w ∈ q.support, w ∉ sdc_fjord.support := fun w hw =>
      hp w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    have ihq := ih hq hbRP
    intro w hw
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with h | h
    · exact h ▸ hx
    · exact ihq w h

theorem iwc_mem_rightPocket_51 : (![5, 1] : Site 2) ∈ iwc_RightPocket := by
  rw [iwc_mem_rightPocket]; simp

theorem iwc_not_rightPocket_11 : (![1, 1] : Site 2) ∉ iwc_RightPocket := by
  rw [iwc_mem_rightPocket]; simp

/-- No lattice path avoiding `sdc_fjord` joins `(5, 1)` to `(1, 1)`. -/
theorem iwc_no_offSupport_walk_51_to_11 :
    ¬ ∃ p : (hypercubicLattice 2).Walk (![5, 1] : Site 2) (![1, 1] : Site 2),
        ∀ w ∈ p.support, w ∉ sdc_fjord.support := by
  rintro ⟨p, hp⟩
  have hend := iwc_offSupport_walk_in_rightPocket p hp iwc_mem_rightPocket_51
    (![1, 1] : Site 2) p.end_mem_support
  exact iwc_not_rightPocket_11 hend

/-- No off-support interior site of `sdc_fjord` is a row-linked seed. -/
theorem iwc_no_rowLinked_seed :
    ¬ ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧
        jil_RowLinked sdc_fjord seed := by
  rintro ⟨seed, hseed, hres⟩
  by_cases hRP : seed ∈ iwc_RightPocket
  · obtain ⟨p, hp⟩ := hres (![1, 1] : Site 2) sdc_fjord_mem_interior_11
    have hprev : ∀ w ∈ p.reverse.support, w ∉ sdc_fjord.support := by
      intro w hw
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
      exact hp w hw
    have hend := iwc_offSupport_walk_in_rightPocket p.reverse hprev hRP
      (![1, 1] : Site 2) p.reverse.end_mem_support
    exact iwc_not_rightPocket_11 hend
  · obtain ⟨p, hp⟩ := hres (![5, 1] : Site 2) sdc_fjord_mem_interior_51
    have hend := iwc_offSupport_walk_in_rightPocket p hp iwc_mem_rightPocket_51
      seed p.end_mem_support
    exact hRP hend

/-- The lexicographically least off-support interior site of `sdc_fjord` is not a row-linked seed.
-/
theorem iwc_rowLinked_false :
    ∃ seed : Site 2, seed ∈ jil_offSupportInterior sdc_fjord ∧
      ¬ jil_RowLinked sdc_fjord seed := by
  obtain ⟨M, _hMb⟩ := rlc_interior_bounded sdc_fjord
  obtain ⟨seed, hseed, _hmin⟩ :=
    rlc_exists_lexMin_seed sdc_fjord sdc_fjord_mem_interior_11 M
  exact ⟨seed, hseed, fun hres => iwc_no_rowLinked_seed ⟨seed, hseed, hres⟩⟩

/-- The off-support interior of `sdc_fjord` has no row-linked seed: it is not connected in the
lattice with the walk removed. -/
theorem iwc_exists_rowLinked_seed_false :
    ¬ ∃ seed ∈ jil_offSupportInterior sdc_fjord, jil_RowLinked sdc_fjord seed :=
  iwc_no_rowLinked_seed

/-- The off-support interior of the simple closed walk `sdc_fjord` is disconnected: `(5, 1)` and
`(1, 1)` are off-support interior sites with no lattice path between them avoiding the walk. So
connectivity of the interior sites is not a consequence of simplicity alone; compare the 4-curve
hypothesis of Rosenfeld (*Arcs and curves in digital pictures*, 1973). -/
theorem iwc_interior_disconnected :
    (![5, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord ∧
    (![1, 1] : Site 2) ∈ jil_offSupportInterior sdc_fjord ∧
    ¬ ∃ p : (hypercubicLattice 2).Walk (![5, 1] : Site 2) (![1, 1] : Site 2),
        ∀ w ∈ p.support, w ∉ sdc_fjord.support :=
  ⟨sdc_fjord_mem_interior_51, sdc_fjord_mem_interior_11, iwc_no_offSupport_walk_51_to_11⟩

end Lattice

end StatMech
