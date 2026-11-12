/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.BKForestLib
import Code.Percolation.BKHallSDRClose
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.ForestSelectorProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.ForestAcyclicityClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}











theorem fps_cutX_sep_of_privateFar_x (ω : ConfigSpace (Sym2 (Site d))) {x bx by_ y : Site d}
    (hpriv : ¬ Connected d (removeSite x ω) bx y)
    (hfar : Connected d (removeSite x ω) by_ y) :
    ¬ Connected d (removeSite x ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.trans hfar)




theorem fps_cutY_sep_of_privateFar_y (ω : ConfigSpace (Sym2 (Site d))) {y bx by_ x : Site d}
    (hpriv : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite y ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.symm.trans hfar)



























theorem fps_eitherCut_sep_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d)))
    {x y bx by_ : Site d}
    (hprivx : ¬ Connected d (removeSite x ω) bx y)
    (hprivy : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite x ω) by_ y ∨ Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite x ω) bx by_ ∨ ¬ Connected d (removeSite y ω) bx by_ := by
  rcases hfar with hfarx | hfary
  · 
    exact Or.inl (fps_cutX_sep_of_privateFar_x ω hprivx hfarx)
  · 
    exact Or.inr (fps_cutY_sep_of_privateFar_y ω hprivy hfary)

























def fps_TwoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      (¬ Connected d (removeSite x ω) (b x) y) ∧
      (¬ Connected d (removeSite y ω) (b y) x) ∧
      (Connected d (removeSite x ω) (b y) y ∨ Connected d (removeSite y ω) (b x) x))






theorem fps_pairwiseCutSeparation_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fps_TwoSidedPrivateFar ω n) :
    fac_PairwiseCutSeparation ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hprivx, hprivy, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  exact fps_eitherCut_sep_of_twoSidedPrivateFar ω hprivx hprivy hfar



theorem fps_globalForestArms_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fps_TwoSidedPrivateFar ω n) :
    aed_GlobalForestArms ω n :=
  fac_globalForestArms_of_pairwiseCutSeparation ω n
    (fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n h)
























theorem fps_twoSidedPrivateFar_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daepf_PrivateArm ω n) :
    fps_TwoSidedPrivateFar ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  
  obtain ⟨hprivx, hfarx⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  
  obtain ⟨hprivy, _⟩ := hpair y hybox htriy x hxbox htri (Ne.symm hxy) hconn.symm
  exact ⟨hprivx, hprivy, Or.inl hfarx⟩



theorem fps_globalForestArms_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daepf_PrivateArm ω n) :
    aed_GlobalForestArms ω n :=
  fps_globalForestArms_of_twoSidedPrivateFar ω n
    (fps_twoSidedPrivateFar_of_privateArm ω n h)












theorem fps_eitherCut_sep_via_farY_only (ω : ConfigSpace (Sym2 (Site d)))
    {x y bx by_ : Site d}
    (hprivy : ¬ Connected d (removeSite y ω) by_ x)
    (hfary : Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite y ω) bx by_ :=
  fps_cutY_sep_of_privateFar_y ω hprivy hfary











theorem fps_twoSidedPrivateFar_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fps_TwoSidedPrivateFar ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)





theorem fps_twoSidedPrivateFar_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fps_TwoSidedPrivateFar ω n :=
  fps_twoSidedPrivateFar_of_privateArm ω n
    (daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)







theorem fps_twoSidedPrivateFar_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
    (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
    (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
    (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
    fps_TwoSidedPrivateFar ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro x hxbox htri y hybox htriy hxy _hconn
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · 
        exact ⟨hpriv_xy, hpriv_yx, Or.inl hfar_xy⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · 
        
        exact ⟨hpriv_yx, hpriv_xy, Or.inr hfar_xy⟩
      · exact absurd rfl hxy



















theorem fps_claw_satisfies_pairwiseCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    fac_PairwiseCutSeparation ω n :=
  fac_pairwiseCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf
    hGstar hsingle b hbdata hcy hcx hcentral











theorem fps_Tcount_le_boundary_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fps_TwoSidedPrivateFar ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fac_Tcount_le_boundary_of_pairwiseCutSeparation ω n hn
    (fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n h)
















theorem fps_burton_keane_bernoulli_of_twoSidedPrivateFar (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fps_TwoSidedPrivateFar ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  fac_burton_keane_bernoulli_of_pairwiseCutSeparation hd p hp1 hp0
    (fun ω n hn => fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
