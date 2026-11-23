/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity
public import MathlibExt.Probability.Percolation.TwoDimensional.Crossings
public import MathlibExt.Probability.Percolation.RSW.Defs
public import MathlibExt.Probability.Percolation.RSW.Strip
public import MathlibExt.Probability.Percolation.Universality.Defs
public import MathlibExt.Probability.Percolation.Universality.RSWStrip
public import MathlibExt.Probability.Percolation.Universality.HVIntersection
public import MathlibExt.Probability.Percolation.Universality.VSeparates

/-!
# Vertical crossings separate the sides of a rectangle

If `x_B` on the bottom side of the overlap `[m, m'] × [c, d]` is joined to the top side by an open
path inside the overlap, then every open left–right path of `[α, β] × [c, d]` meets the open cluster
of `x_B` inside the overlap. This is the separation hypothesis needed for RSW gluing, stated here in
a form that can hold for every configuration (compare `VSeparatesH`, which asks it for every point
`x_B` and therefore fails for nondegenerate rectangles). It is reduced to a discrete Jordan-type
statement `CrossingArcSides`: a set `L` containing the left side, avoiding the right side, whose
edge boundary inside the rectangle touches the cluster of `x_B`.

## Main definitions

* `StatMech.Universality.CrossingSeparatesH`: the separation property described above.
* `StatMech.Universality.CrossingArcSides`: the discrete Jordan-type separation by a set `L`.

## Main results

* `StatMech.Universality.crossingSeparatesH_of_crossingArcSides`: `CrossingArcSides` implies
  `CrossingSeparatesH`.
* `StatMech.Universality.rsw_strip_glue_of_crossingSeparatesH`,
  `StatMech.Universality.rsw_strip_glue_of_crossingArcSides`: the product lower bound
  `μ(H_{[a, m']}) μ(V_{[m, m']}) μ(H_{[m, b]}) ≤ μ(H_{[a, b]})` for a positively associated
  probability measure, under these hypotheses for every configuration. The hypothesis
  `CrossingArcSides` is discharged for all configurations by
  `StatMech.Lattice.jec_crossingArcSides` in
  `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure`.

## References

* V. Tassion, *Crossing probabilities for Voronoi percolation*, Ann. Probab. 44 (2016), 3385–3398.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- For the configuration `ω`: whenever `x_B` on the bottom side of the overlap
`[m, m'] × [c, d]` is joined to the top side inside the overlap, every open left–right path of
`[α, β] × [c, d]` meets the open cluster of `x_B` inside the overlap. -/
def CrossingSeparatesH (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  xB ∈ bottomSide m m' c d →
  ∀ (yT : Site 2) (hyT : yT ∈ topSide m m' c d),
  ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, topSide_subset hyT⟩ →
  ∀ (x y : rect α β c d), (x : Site 2) 0 = α → (y : Site 2) 0 = β →
  ∀ (w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y),
    ∃ z ∈ w.support, (z : Site 2) ∈ overlapComp ω m m' c d xB hxB

theorem hvMeet_of_crossingSeparatesH (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (hsep : CrossingSeparatesH ω α β m m' c d) : HVMeetProperty ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xL yR hcH xB yT hcV
  have hxBmem : (xB : Site 2) ∈ rect m m' c d := bottomSide_subset xB.2
  obtain ⟨wH⟩ := hcH
  have hx0 : ((⟨(xL : Site 2), leftSide_subset xL.2⟩ : rect α β c d) : Site 2) 0 = α :=
    xL.2.2
  have hy0 : ((⟨(yR : Site 2), rightSide_subset yR.2⟩ : rect α β c d) : Site 2) 0 = β :=
    yR.2.2
  obtain ⟨z, hzs, hzP⟩ := hsep hαm hmm' hm'β (xB : Site 2) hxBmem xB.2 (yT : Site 2) yT.2
    hcV ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩
    hx0 hy0 wH
  obtain ⟨hzO, hzVconn⟩ := hzP
  exact ⟨(z : Site 2), hzO, z.2, ⟨wH.takeUntil z hzs⟩, hzVconn⟩

theorem hvIntersection_of_crossingSeparatesH (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : CrossingSeparatesH ω a m' m m' c d)
    (hsepR : CrossingSeparatesH ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d :=
  hvIntersection_of_meet ω ham hmm' hm'b
    (hvMeet_of_crossingSeparatesH ω a m' m m' c d hsepL)
    (hvMeet_of_crossingSeparatesH ω m b m m' c d hsepR)

theorem rsw_strip_glue_of_crossingSeparatesH (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ ω, CrossingSeparatesH ω a m' m m' c d)
    (hsepR : ∀ ω, CrossingSeparatesH ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  rsw_strip_glue_of_intersection μ hpa
    (fun ω => hvIntersection_of_crossingSeparatesH ω ham hmm' hm'b (hsepL ω) (hsepR ω))

/-- For the configuration `ω`: whenever `x_B` on the bottom of the overlap is joined to its top,
there is a set `L` containing the left side of `[α, β] × [c, d]` and disjoint from its right side
such that every lattice edge of the rectangle crossing the boundary of `L` has an endpoint in the
open cluster of `x_B` inside the overlap. -/
def CrossingArcSides (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  xB ∈ bottomSide m m' c d →
  ∀ (yT : Site 2) (hyT : yT ∈ topSide m m' c d),
  ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, topSide_subset hyT⟩ →
  ∃ L : Set (Site 2),
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = α → z ∈ L) ∧
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = β → z ∉ L) ∧
    (∀ u v : Site 2, u ∈ rect α β c d → v ∈ rect α β c d →
        (hypercubicLattice 2).Adj u v → bdEdge L s(u, v) →
        u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB)

theorem crossingSeparatesH_of_crossingArcSides (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (harc : CrossingArcSides ω α β m m' c d) :
    CrossingSeparatesH ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xB hxB hxBbot yT hyT hcV x y hx0 hy0 wH
  obtain ⟨L, hLleft, hLright, hLedge⟩ := harc hαm hmm' hm'β xB hxB hxBbot yT hyT hcV
  set wL : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    liftWalk ω (rect α β c d) wH with hwL
  have hxL : (x : Site 2) ∈ L := hLleft (x : Site 2) x.2 hx0
  have hyL : (y : Site 2) ∉ L := hLright (y : Site 2) y.2 hy0
  have hodd : ¬ Even (crossCount L wL) := by
    rw [crossCount_parity]
    intro h
    exact hyL (h.mp hxL)
  have hbd : ∃ e ∈ wL.edges, bdEdge L e := by
    by_contra hcon
    apply hodd
    have hz : crossCount L wL = 0 := by
      rw [crossCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      exact fun hb => hcon ⟨e, he, hb⟩
    rw [hz]; exact ⟨0, rfl⟩
  obtain ⟨e, hemem, hebd⟩ := hbd
  induction e with
  | h u v =>
    have hu_supp : u ∈ wL.support := wL.fst_mem_support_of_mem_edges hemem
    have hv_supp : v ∈ wL.support := wL.snd_mem_support_of_mem_edges hemem
    obtain ⟨u', hu'_mem, hu'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hu_supp
    obtain ⟨v', hv'_mem, hv'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hv_supp
    have hu_box : u ∈ rect α β c d := hu'_eq ▸ u'.2
    have hv_box : v ∈ rect α β c d := hv'_eq ▸ v'.2
    have huv_adj : (hypercubicLattice 2).Adj u v := wL.adj_of_mem_edges hemem
    rcases hLedge u v hu_box hv_box huv_adj hebd with hUcomp | hVcomp
    · exact ⟨u', hu'_mem, hu'_eq ▸ hUcomp⟩
    · exact ⟨v', hv'_mem, hv'_eq ▸ hVcomp⟩

/-- RSW gluing: for a positively associated probability measure `μ`, if `CrossingArcSides` holds
for every configuration, then `μ(H_{[a, m']}) μ(V_{[m, m']}) μ(H_{[m, b]}) ≤ μ(H_{[a, b]})`. -/
theorem rsw_strip_glue_of_crossingArcSides (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (harcL : ∀ ω, CrossingArcSides ω a m' m m' c d)
    (harcR : ∀ ω, CrossingArcSides ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  rsw_strip_glue_of_crossingSeparatesH μ hpa ham hmm' hm'b
    (fun ω => crossingSeparatesH_of_crossingArcSides ω a m' m m' c d (harcL ω))
    (fun ω => crossingSeparatesH_of_crossingArcSides ω m b m m' c d (harcR ω))

end Universality

end StatMech
