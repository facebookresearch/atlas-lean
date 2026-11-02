/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FigureEightFourThin

/-!
# King separations of four-thin lattice cycles

In a cycle every site has exactly two neighbors in the subgraph traced by the walk. For a
four-thin cycle every lattice edge between walk sites is a walk edge, so each walk site has at
most two lattice neighbors on the walk, and three lattice neighbors on the walk force a thick
point. The figure-eight walk `wpc_fig8` is four-thin but not a cycle. The target statement, that the
interior of a four-thin simple lattice cycle is king-connected, is not proved here: the
conditional cycle theorems that restated it from `cat_CrossArcThick` were removed, since for a
four-thin walk that predicate is equivalent to the conclusion. Despite the file name, no
Peierls-type counting argument appears in it.

## Main definitions

* `StatMech.Lattice.pcy_fig8_A`, `StatMech.Lattice.pcy_fig8_B`: the two loops of `wpc_fig8`.

## Main results

* `StatMech.Lattice.pcy_thickPoint_of_three_support_neighbors`,
  `StatMech.Lattice.pcy_le_two_support_neighbors`: neighbor counts on four-thin cycles.
* `StatMech.Lattice.pcy_fig8_not_cycle`: the figure-eight walk is not a cycle.
* `StatMech.Lattice.pcy_fjord_three_support_neighbors`: if the fjord were a cycle, its throat
  site `(3, 1)` would be a thick point.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- In a four-thin walk, a lattice neighbor on the walk of a walk site is a neighbor in the subgraph
traced by the walk. -/
theorem pcy_toSubgraph_neighbor_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hthin : mci_FourThin Vc) {u v : Site 2} (hu : u ∈ Vc.support) (hv : v ∈ Vc.support)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ Vc.toSubgraph.neighborSet u := by
  rw [Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact hthin u v hu hv hadj

/-- A cycle with a site that has three distinct lattice neighbors on the walk has a thick point. -/
theorem pcy_thickPoint_of_three_support_neighbors {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hcyc : Vc.IsCycle)
    {u v₁ v₂ v₃ : Site 2} (hu : u ∈ Vc.support)
    (h1 : (hypercubicLattice 2).Adj u v₁) (h2 : (hypercubicLattice 2).Adj u v₂)
    (h3 : (hypercubicLattice 2).Adj u v₃)
    (hv1 : v₁ ∈ Vc.support) (hv2 : v₂ ∈ Vc.support) (hv3 : v₃ ∈ Vc.support)
    (hne12 : v₁ ≠ v₂) (hne13 : v₁ ≠ v₃) (hne23 : v₂ ≠ v₃) :
    kns_ThickPoint Vc := by
  rw [kns_thickPoint_iff_not_fourThin]
  intro hthin
  have m1 : v₁ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv1 h1
  have m2 : v₂ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv2 h2
  have m3 : v₃ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv3 h3
  have hcard := hcyc.ncard_neighborSet_toSubgraph_eq_two hu
  have hfin : (Vc.toSubgraph.neighborSet u).Finite := Vc.finite_neighborSet_toSubgraph
  have hsub : ({v₁, v₂, v₃} : Set (Site 2)) ⊆ Vc.toSubgraph.neighborSet u := by
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3card : ({v₁, v₂, v₃} : Set (Site 2)).ncard = 3 := by
    rw [Set.ncard_eq_three]; exact ⟨v₁, v₂, v₃, hne12, hne13, hne23, rfl⟩
  have hle := Set.ncard_le_ncard hsub hfin
  rw [h3card, hcard] at hle
  omega

/-- In a four-thin cycle, every walk site has at most two lattice neighbors on the walk. -/
theorem pcy_le_two_support_neighbors {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (hthin : mci_FourThin Vc) {u : Site 2} (hu : u ∈ Vc.support) :
    {v : Site 2 | (hypercubicLattice 2).Adj u v ∧ v ∈ Vc.support}.ncard ≤ 2 := by
  have hsub : {v : Site 2 | (hypercubicLattice 2).Adj u v ∧ v ∈ Vc.support}
      ⊆ Vc.toSubgraph.neighborSet u := by
    rintro v ⟨hadj, hv⟩
    exact pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv hadj
  have hfin : (Vc.toSubgraph.neighborSet u).Finite := Vc.finite_neighborSet_toSubgraph
  have hle := Set.ncard_le_ncard hsub hfin
  rwa [hcyc.ncard_neighborSet_toSubgraph_eq_two hu] at hle

/-- A cycle through `(x, y)` that also visits its west, east and south neighbors has a thick point.
-/
theorem pcy_thickPoint_of_WES {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {x y : ℤ}
    (hu : (![x, y] : Site 2) ∈ Vc.support)
    (hW : (![x - 1, y] : Site 2) ∈ Vc.support)
    (hE : (![x + 1, y] : Site 2) ∈ Vc.support)
    (hS : (![x, y - 1] : Site 2) ∈ Vc.support) :
    kns_ThickPoint Vc := by
  refine pcy_thickPoint_of_three_support_neighbors Vc hcyc hu
    (v₁ := (![x - 1, y] : Site 2)) (v₂ := (![x + 1, y] : Site 2)) (v₃ := (![x, y - 1] : Site 2))
    ?_ ?_ ?_ hW hE hS ?_ ?_ ?_
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 1; simp at this; omega
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega

/-- The first loop of the figure-eight walk: the boundary of `[0, 2]²` from `(2, 2)`. -/
noncomputable def pcy_fig8_A : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![(2:ℤ),2] :=
  let a1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![0,2] :=
    ((jec_hsegRight 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a2 : (hypercubicLattice 2).Walk ![(0:ℤ),2] ![0,0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a3 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![2,0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let a4 : (hypercubicLattice 2).Walk ![(2:ℤ),0] ![2,2] :=
    (jec_vsegUp 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  a1.append (a2.append (a3.append a4))

/-- The second loop of the figure-eight walk: the boundary of `[2, 4]²` from `(2, 2)`. -/
noncomputable def pcy_fig8_B : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![(2:ℤ),2] :=
  let b1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![4,2] :=
    (jec_hsegRight 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b2 : (hypercubicLattice 2).Walk ![(4:ℤ),2] ![4,4] :=
    (jec_vsegUp 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b3 : (hypercubicLattice 2).Walk ![(4:ℤ),4] ![2,4] :=
    ((jec_hsegRight 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let b4 : (hypercubicLattice 2).Walk ![(2:ℤ),4] ![2,2] :=
    ((jec_vsegUp 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  b1.append (b2.append (b3.append b4))

/-- The figure-eight walk is the concatenation of its two loops. -/
theorem pcy_fig8_eq : wpc_fig8 = pcy_fig8_A.append pcy_fig8_B := rfl

theorem pcy_fig8_A_not_nil : ¬ pcy_fig8_A.Nil := by
  rw [pcy_fig8_A, SimpleGraph.Walk.nil_append_iff]
  rintro ⟨h1, _⟩
  have h0 := congrFun h1.eq 0; simp at h0

theorem pcy_fig8_B_not_nil : ¬ pcy_fig8_B.Nil := by
  rw [pcy_fig8_B, SimpleGraph.Walk.nil_append_iff]
  rintro ⟨h1, _⟩
  have h0 := congrFun h1.eq 0; simp at h0

/-- The figure-eight walk is not a cycle: it visits `(2, 2)` in the middle as well as at its ends.
-/
theorem pcy_fig8_not_cycle : ¬ wpc_fig8.IsCycle := by
  intro hcyc
  have htail := hcyc.support_nodup
  rw [pcy_fig8_eq, SimpleGraph.Walk.tail_support_append, List.nodup_append] at htail
  obtain ⟨_, _, hdisj⟩ := htail
  have hA : (![2, 2] : Site 2) ∈ pcy_fig8_A.support.tail :=
    SimpleGraph.Walk.end_mem_tail_support pcy_fig8_A_not_nil
  have hB : (![2, 2] : Site 2) ∈ pcy_fig8_B.support.tail :=
    SimpleGraph.Walk.end_mem_tail_support pcy_fig8_B_not_nil
  exact hdisj _ hA _ hB rfl

theorem pcy_fjord_on_32 : (![3, 2] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 2 (by norm_num) (by norm_num)

theorem pcy_fjord_on_30 : (![3, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 0 (by norm_num) (by norm_num)

/-- The throat site `(3, 1)` of the fjord has three distinct lattice neighbors `(3, 0)`, `(3, 2)`,
`(4, 1)` on the walk. -/
theorem pcy_fjord_throat_three_neighbors :
    (![3, 1] : Site 2) ∈ sdc_fjord.support ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 0] : Site 2) ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 2] : Site 2) ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![4, 1] : Site 2) ∧
    (![3, 0] : Site 2) ∈ sdc_fjord.support ∧ (![3, 2] : Site 2) ∈ sdc_fjord.support ∧
    (![4, 1] : Site 2) ∈ sdc_fjord.support ∧
    (![3, 0] : Site 2) ≠ (![3, 2] : Site 2) ∧ (![3, 0] : Site 2) ≠ (![4, 1] : Site 2) ∧
    (![3, 2] : Site 2) ≠ (![4, 1] : Site 2) :=
  ⟨mci_fjord_on_31,
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   pcy_fjord_on_30, pcy_fjord_on_32, sdc_fjord_on_41,
   (by intro h; have := congrFun h 1; simp at this),
   (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega),
   (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)⟩

/-- If the fjord were a cycle, it would have a thick point at its throat. -/
theorem pcy_fjord_three_support_neighbors (hcyc : sdc_fjord.IsCycle) :
    kns_ThickPoint sdc_fjord :=
  pcy_thickPoint_of_three_support_neighbors sdc_fjord hcyc
    (u := (![3, 1] : Site 2)) (v₁ := (![3, 0] : Site 2)) (v₂ := (![3, 2] : Site 2))
    (v₃ := (![4, 1] : Site 2))
    mci_fjord_on_31
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    pcy_fjord_on_30 pcy_fjord_on_32 sdc_fjord_on_41
    (by intro h; have := congrFun h 1; simp at this)
    (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)
    (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)

end Lattice

end StatMech
