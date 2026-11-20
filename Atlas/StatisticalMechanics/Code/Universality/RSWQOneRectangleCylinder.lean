/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Universality.RSWQOneInfiniteVolume

open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal

namespace StatMech
namespace Universality

open StatMech.Lattice
open StatMech.FK
open StatMech.RSW.Box





def rq1_finiteRectangleEvent (N : ℕ) (a b c d : ℤ) :
    Set (ConfigSpace (Sym2 (boxVerts 2 N))) :=
  extendEdge 2 N ⁻¹' horizontalCrossingEvent a b c d




theorem rq1_rect_subset_box_of_bounds {N : ℕ} {a b c d : ℤ}
    (ha : -(N : ℤ) ≤ a) (hb : b ≤ (N : ℤ))
    (hc : -(N : ℤ) ≤ c) (hd : d ≤ (N : ℤ)) :
    rect a b c d ⊆ box 2 N := by
  intro z hz
  rw [mem_box]
  intro i
  fin_cases i
  · have habs : |z 0| ≤ (N : ℤ) :=
      abs_le.mpr ⟨ha.trans hz.1, hz.2.1.trans hb⟩
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs
  · have habs : |z 1| ≤ (N : ℤ) :=
      abs_le.mpr ⟨hc.trans hz.2.2.1, hz.2.2.2.trans hd⟩
    rw [Int.abs_eq_natAbs] at habs
    exact_mod_cast habs

private theorem rq1_extendEdge_rect_pair (N : ℕ) (a b c d : ℤ)
    (hrect : rect a b c d ⊆ box 2 N)
    (eta : ConfigSpace (Sym2 (boxVerts 2 N))) {x y : Site 2}
    (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d) :
    extendEdge 2 N eta s(x, y) =
      eta s((⟨x, hrect hx⟩ : boxVerts 2 N),
        (⟨y, hrect hy⟩ : boxVerts 2 N)) := by
  let xb : boxVerts 2 N := ⟨x, hrect hx⟩
  let yb : boxVerts 2 N := ⟨y, hrect hy⟩
  have heq : edgeIncl 2 N s(xb, yb) = s(x, y) := by
    simp [edgeIncl, Sym2.map_mk, xb, yb]
  rw [← heq, extendEdge_eq_of_range]



theorem rq1_finiteRectangleEvent_dependsOn (N : ℕ) (a b c d : ℤ)
    (hrect : rect a b c d ⊆ box 2 N) :
    _root_.DependsOn
      ((rq1_finiteRectangleEvent N a b c d).indicator (fun _ => (1 : ℝ)))
      ((boxGraph 2 N).edgeFinset : Set (Sym2 (boxVerts 2 N))) := by
  intro eta eta' hagree
  have hgraph : openSubgraphInduce 2 (extendEdge 2 N eta) (rect a b c d) =
      openSubgraphInduce 2 (extendEdge 2 N eta') (rect a b c d) := by
    apply SimpleGraph.ext
    ext x y
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 N := ⟨x, hrect x.2⟩
      let yb : boxVerts 2 N := ⟨y, hrect y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 N).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_rect_pair N a b c d hrect eta x.2 y.2] at hopen
      rw [rq1_extendEdge_rect_pair N a b c d hrect eta' x.2 y.2]
      exact heq ▸ hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨hadj, ?_⟩
      let xb : boxVerts 2 N := ⟨x, hrect x.2⟩
      let yb : boxVerts 2 N := ⟨y, hrect y.2⟩
      have hbe : s(xb, yb) ∈ (boxGraph 2 N).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph,
          SimpleGraph.comap_adj]
        exact hadj
      have heq := hagree s(xb, yb) hbe
      rw [rq1_extendEdge_rect_pair N a b c d hrect eta' x.2 y.2] at hopen
      rw [rq1_extendEdge_rect_pair N a b c d hrect eta x.2 y.2]
      exact heq.symm ▸ hopen
  have hevent : eta ∈ rq1_finiteRectangleEvent N a b c d ↔
      eta' ∈ rq1_finiteRectangleEvent N a b c d := by
    change HorizontalCrossing (extendEdge 2 N eta) a b c d ↔
      HorizontalCrossing (extendEdge 2 N eta') a b c d
    unfold HorizontalCrossing ConnectedWithin
    rw [hgraph]
  by_cases heta : eta ∈ rq1_finiteRectangleEvent N a b c d
  · rw [Set.indicator_of_mem heta, Set.indicator_of_mem (hevent.mp heta)]
  · rw [Set.indicator_of_notMem heta,
      Set.indicator_of_notMem (fun h => heta (hevent.mpr h))]

private theorem rq1_extend_restrict_rect_pair (N : ℕ) (a b c d : ℤ)
    (hrect : rect a b c d ⊆ box 2 N)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (hx : x ∈ rect a b c d) (hy : y ∈ rect a b c d) :
    extendEdge 2 N (boxRestrict 2 N omega) s(x, y) = omega s(x, y) := by
  rw [rq1_extendEdge_rect_pair N a b c d hrect
    (boxRestrict 2 N omega) hx hy]
  simp [boxRestrict, edgeIncl, Sym2.map_mk]




theorem rq1_finiteRectangleEvent_preimage (N : ℕ) (a b c d : ℤ)
    (hrect : rect a b c d ⊆ box 2 N) :
    boxRestrict 2 N ⁻¹' rq1_finiteRectangleEvent N a b c d =
      horizontalCrossingEvent a b c d := by
  ext omega
  change HorizontalCrossing (extendEdge 2 N (boxRestrict 2 N omega)) a b c d ↔
    HorizontalCrossing omega a b c d
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect a b c d) (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv =>
        rq1_extend_restrict_rect_pair N a b c d hrect omega hu hv)).mp hxy
  · rintro ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    exact (StatMech.Percolation.connWithinR_congr
      (rect a b c d) (leftSide_subset x.2) (rightSide_subset y.2)
      (fun u hu v hv =>
        rq1_extend_restrict_rect_pair N a b c d hrect omega hu hv)).mpr hxy






theorem rq1_wiredInfiniteVolume_rectangle_eq_bernoulli
    (N : ℕ) (a b c d : ℤ) (hrect : rect a b c d ⊆ box 2 N)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 1) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (horizontalCrossingEvent a b c d) =
      (bernoulliProductMeasure (E := Sym2 (Site 2))
        (⟨p, hp.le⟩ : ℝ≥0) (by exact_mod_cast hp1.le)).real
        (horizontalCrossingEvent a b c d) := by
  rw [← rq1_finiteRectangleEvent_preimage N a b c d hrect]
  exact rq1_wiredInfiniteVolume_graphCylinder_eq_bernoulli
    (d := 2) N hp hp1 (rq1_finiteRectangleEvent N a b c d)
      (rq1_finiteRectangleEvent_dependsOn N a b c d hrect)




theorem rq1_wiredInfiniteVolume_rectangle_eq
    (N : ℕ) (a b c d : ℤ) (hrect : rect a b c d ⊆ box 2 N) :
    (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) :
      Measure (ConfigSpace (Sym2 (Site 2)))).real
        (horizontalCrossingEvent a b c d) =
      rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  simpa [rba_selfDualMeasure] using
    (rq1_wiredInfiniteVolume_rectangle_eq_bernoulli N a b c d hrect
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1))








theorem rq1_wiredInfiniteVolume_square_half
    (N : ℕ) (a c m : ℤ) (hm : 0 < m)
    (hrect : rect a (a + m) c (c + m) ⊆ box 2 N) :
    (1 : ℝ) / 2 ≤
      (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (horizontalCrossingEvent a (a + m) c (c + m)) := by
  rw [rq1_wiredInfiniteVolume_rectangle_eq N a (a + m) c (c + m) hrect]
  have htranslate := cti_horizontalCrossing_translation_invariant
    0 m 0 m (![a, c] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 m 0 m)
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent a (a + m) c (c + m)) =
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 m 0 m) := by
    simpa [add_comm] using htranslate
  rw [heq]
  exact rlc_square_half m hm

end Universality
end StatMech
