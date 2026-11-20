/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.CrossingParity
import Code.TwoDim.Crossings
import Code.RSW.Defs
import Code.RSW.Strip
import Code.Universality.Defs
import Code.Universality.RSWStrip

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip


















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













def overlapComp (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect m m' c d, ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨z, hz⟩}
















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













theorem rsw_strip_glue_unconditional (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ ω, VSeparatesH ω a m' m m' c d)
    (hsepR : ∀ ω, VSeparatesH ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  rsw_strip_glue_of_intersection μ hpa
    (fun ω => hv_intersection ω ham hmm' hm'b (hsepL ω) (hsepR ω))

end Universality

end StatMech
