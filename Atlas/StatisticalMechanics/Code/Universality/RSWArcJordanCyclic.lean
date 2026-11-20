/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWArcJordan
















open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box



def rlc_contourEdgeLocal {n : ℤ}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (f g : Site 2) : Prop :=
  rlc_reflectedTargetLocallySupported G
      s(rlc_dualReflect f, rlc_dualReflect g) ∧
    rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g)



theorem rlc_orderedContourArc_edges_disjoint_complementary
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsTrail)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_orderedContourArc c hx hy).edges.Disjoint
      (rlc_complementaryContourArc c hx hy).edges := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hdisjoint := (hc.rotate hx).disjoint_edges_takeUntil_dropUntil hy'
  simpa [rlc_orderedContourArc, rlc_complementaryContourArc,
    SimpleGraph.Walk.edges_reverse] using hdisjoint




theorem rlc_not_contourArcLocalSide_iff_bad_edges_both
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    ¬ RlcContourArcLocalSide G omega c hx hy ↔
      ∃ f₁ g₁ f₂ g₂ : Site 2,
        s(f₁, g₁) ∈ (rlc_orderedContourArc c hx hy).edges ∧
        ¬ rlc_contourEdgeLocal G f₁ g₁ ∧
        s(f₂, g₂) ∈ (rlc_complementaryContourArc c hx hy).edges ∧
        ¬ rlc_contourEdgeLocal G f₂ g₂ ∧
        s(f₁, g₁) ≠ s(f₂, g₂) := by
  classical
  simp only [rlc_contourEdgeLocal]
  rw [RlcContourArcLocalSide]
  constructor
  · intro hnot
    push Not at hnot
    obtain ⟨⟨f₁, g₁, he₁, hbad₁⟩, ⟨f₂, g₂, he₂, hbad₂⟩⟩ := hnot
    refine ⟨f₁, g₁, f₂, g₂, he₁, ?_, he₂, ?_, ?_⟩
    · rintro ⟨htarget, hsource⟩
      exact hbad₁ htarget hsource
    · rintro ⟨htarget, hsource⟩
      exact hbad₂ htarget hsource
    · intro heq
      apply (rlc_orderedContourArc_edges_disjoint_complementary
        c hc hx hy) he₁
      exact heq.symm ▸ he₂
  · rintro ⟨f₁, g₁, f₂, g₂, he₁, hbad₁, he₂, hbad₂, _⟩
    push Not
    exact ⟨⟨f₁, g₁, he₁, fun htarget hsource =>
        hbad₁ ⟨htarget, hsource⟩⟩,
      ⟨f₂, g₂, he₂, fun htarget hsource =>
        hbad₂ ⟨htarget, hsource⟩⟩⟩




theorem rlc_contourArcLocalSide_of_atMostOne_bad_edge
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hbad : ∀ {f₁ g₁ f₂ g₂ : Site 2},
      s(f₁, g₁) ∈ c.edges → ¬ rlc_contourEdgeLocal G f₁ g₁ →
      s(f₂, g₂) ∈ c.edges → ¬ rlc_contourEdgeLocal G f₂ g₂ →
      s(f₁, g₁) = s(f₂, g₂)) :
    RlcContourArcLocalSide G omega c hx hy := by
  by_contra hside
  obtain ⟨f₁, g₁, f₂, g₂, he₁, hbad₁, he₂, hbad₂, hne⟩ :=
    (rlc_not_contourArcLocalSide_iff_bad_edges_both
      G omega c hc hx hy).mp hside
  apply hne
  exact hbad
    (rlc_orderedContourArc_edges_subset c hx hy he₁) hbad₁
    (rlc_complementaryContourArc_edges_subset c hx hy he₂) hbad₂



theorem rlc_mixedWired_exists_faceBoundary_not_local
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ∃ f g : Site 2,
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      ¬ rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) ∧
      ¬ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
  obtain ⟨f, g, hfg, htarget, hsource⟩ :=
    rlc_mixedWired_exists_faceBoundary_outside_transportSupport
      G hn hlt omega
  refine ⟨f, g, hfg, ?_, ?_⟩
  · intro hlocal
    apply htarget
    rw [rlc_mem_exposed_union_mixedAxisGapEdges_iff G]
    rcases hlocal with hexposed | hgap | hright | hleft
    · exact Or.inl hexposed
    · exact Or.inr (Or.inl
        (rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap G hgap))
    · exact Or.inr (Or.inr (Or.inl hright))
    · exact Or.inr (Or.inr (Or.inr hleft))
  · intro hlocal
    apply hsource
    rw [rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
      G hn hlt omega hfg]
    rcases hlocal with hgap | hright | hleft
    · exact Or.inl (rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G hgap)
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hleft)

end Universality
end StatMech
