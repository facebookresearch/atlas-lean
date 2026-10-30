/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWStrip

/-!
# Horizontal and vertical crossings meet

The intersection step of RSW gluing: if every open left–right path of `[α, β] × [c, d]` passes
through the open cluster (inside the overlap `[m, m'] × [c, d]`) of a point `x_B` of the overlap,
then a horizontal crossing and a vertical crossing of the overlap meet, and hence
`HVIntersectionProperty` holds.

## Main definitions

* `StatMech.Universality.HVMeetProperty`: a horizontal crossing of `[α, β] × [c, d]` and a vertical
  crossing of the overlap reach a common point.
* `StatMech.Universality.overlapComp`: the open cluster of `x_B` inside the overlap.
* `StatMech.Universality.VSeparatesH`: every open left–right path meets `overlapComp ω … x_B`, for
  every point `x_B` of the overlap.

## Main results

* `StatMech.Universality.hvMeet_of_separates`, `StatMech.Universality.hv_intersection`.

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

/-- For the configuration `ω`: whenever `x_L` (left side of `[α, β] × [c, d]`) is joined to the
right side and `x_B` (bottom of the overlap `[m, m'] × [c, d]`) is joined to its top, there is a
point `z` of the overlap reached from `x_L` inside `[α, β] × [c, d]` and from `x_B` inside the
overlap. -/
def HVMeetProperty (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xL : leftSide α β c d) (yR : rightSide α β c d),
    ConnectedWithin 2 ω (rect α β c d)
      ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩ →
  ∀ (xB : bottomSide m m' c d) (yT : topSide m m' c d),
    ConnectedWithin 2 ω (rect m m' c d)
      ⟨(xB : Site 2), bottomSide_subset xB.2⟩ ⟨(yT : Site 2), topSide_subset yT.2⟩ →
  ∃ (z : Site 2) (hzO : z ∈ rect m m' c d) (hzH : z ∈ rect α β c d),
    ConnectedWithin 2 ω (rect α β c d)
        ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨z, hzH⟩ ∧
    ConnectedWithin 2 ω (rect m m' c d)
        ⟨(xB : Site 2), bottomSide_subset xB.2⟩ ⟨z, hzO⟩

theorem hvIntersection_of_meet (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hmeetL : HVMeetProperty ω a m' m m' c d)
    (hmeetR : HVMeetProperty ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d := by
  intro hH hV hHr
  obtain ⟨xL, pR, hcL⟩ := hH
  obtain ⟨xB, yT, hcV⟩ := hV
  obtain ⟨qL, yR, hcR⟩ := hHr
  obtain ⟨p, hpO, hpL, hcLp, hcVp⟩ :=
    hmeetL ham hmm' le_rfl xL pR hcL xB yT hcV
  obtain ⟨q, hqO, hqR, hcRq, hcVq⟩ :=
    hmeetR le_rfl hmm' hm'b qL yR hcR xB yT hcV
  have hcPQ : ConnectedWithin 2 ω (rect m m' c d) ⟨p, hpO⟩ ⟨q, hqO⟩ :=
    hcVp.symm.trans hcVq
  have hcQyR : ConnectedWithin 2 ω (rect m b c d) ⟨q, hqR⟩
      ⟨(yR : Site 2), rightSide_subset yR.2⟩ := hcRq.symm.trans hcR
  exact hv_glue ham hm'b xL.2 hpO hpL hcLp hqO hcPQ yR.2 hqR hcQyR

/-- The open cluster of `x_B` inside the overlap rectangle `[m, m'] × [c, d]`. -/
def overlapComp (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect m m' c d, ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨z, hz⟩}

/-- For the configuration `ω` and every point `x_B` of the overlap `[m, m'] × [c, d]`, every open
left–right path of `[α, β] × [c, d]` meets the open cluster of `x_B` inside the overlap.
For `c < d` this fails for some `ω`; see `CrossingSeparatesH` for the version that only
concerns bottom points `x_B` joined to the top. -/
def VSeparatesH (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  ∀ (x y : rect α β c d), (x : Site 2) 0 = α → (y : Site 2) 0 = β →
  ∀ (w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y),
    ∃ z ∈ w.support, (z : Site 2) ∈ overlapComp ω m m' c d xB hxB

theorem hvMeet_of_separates (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (hsep : VSeparatesH ω α β m m' c d) : HVMeetProperty ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xL yR hcH xB yT hcV
  have hxBmem : (xB : Site 2) ∈ rect m m' c d := bottomSide_subset xB.2
  obtain ⟨wH⟩ := hcH
  have hx0 : ((⟨(xL : Site 2), leftSide_subset xL.2⟩ : rect α β c d) : Site 2) 0 = α :=
    xL.2.2
  have hy0 : ((⟨(yR : Site 2), rightSide_subset yR.2⟩ : rect α β c d) : Site 2) 0 = β :=
    yR.2.2
  obtain ⟨z, hzs, hzP⟩ := hsep hαm hmm' hm'β (xB : Site 2) hxBmem
    ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩
    hx0 hy0 wH
  obtain ⟨hzO, hzVconn⟩ := hzP
  exact ⟨(z : Site 2), hzO, z.2, ⟨wH.takeUntil z hzs⟩, hzVconn⟩

theorem hv_intersection (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : VSeparatesH ω a m' m m' c d)
    (hsepR : VSeparatesH ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d :=
  hvIntersection_of_meet ω ham hmm' hm'b
    (hvMeet_of_separates ω a m' m m' c d hsepL)
    (hvMeet_of_separates ω m b m m' c d hsepR)

end Universality

end StatMech
