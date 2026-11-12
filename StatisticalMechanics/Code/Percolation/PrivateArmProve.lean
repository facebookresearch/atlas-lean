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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}













theorem pap_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  daepf_arm_class_unique ω hd12 hd13 hd23 v










theorem pap_two_branches_avoid_vertex (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) :=
  daep2_two_branches_avoid ω hd12 hd13 hd23 v



















theorem pap_exists_private_branch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (_ha3box : a₃ ∈ box d n)
    (hc1 : Connected d ω x a₁) (hc2 : Connected d ω x a₂) (_hc3 : Connected d ω x a₃)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (_hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ∃ a, a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSite x ω) a).Infinite ∧
      ¬ Connected d (removeSite x ω) a v := by
  rcases pap_two_branches_avoid_vertex ω hd12 hd13 hd23 v with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₂, ha2box, hc2, hi2, h2⟩












theorem pap_adj_removeSite_of_avoid (ω : ConfigSpace (Sym2 (Site d))) {x u w : Site d}
    (hu : u ≠ x) (hw : w ≠ x) (hadj : (openSubgraph d ω).Adj u w) :
    (openSubgraph d (removeSite x ω)).Adj u w := by
  rw [openSubgraph_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  have hxnot : x ∉ s(u, w) := by
    rw [Sym2.mem_iff, not_or]; exact ⟨fun h => hu h.symm, fun h => hw h.symm⟩
  rw [removeSite_apply_of_notMem hxnot]; exact hadj.2









theorem pap_connected_removeSite_of_walk_avoid (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {u w : Site d} (p : (openSubgraph d ω).Walk u w) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) u w := by
  induction p with
  | nil => exact connected_rfl
  | @cons a b c hadj p' ih =>
    
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hx
    obtain ⟨hxa, hxrest⟩ := hx
    
    have hxb : x ≠ b := fun h => hxrest (h ▸ p'.start_mem_support)
    have hstep : (openSubgraph d (removeSite x ω)).Adj a b :=
      pap_adj_removeSite_of_avoid ω (Ne.symm hxa) (Ne.symm hxb) hadj
    exact (SimpleGraph.Adj.reachable hstep).trans (ih hxrest)





theorem pap_far_of_avoiding_path (ω : ConfigSpace (Sym2 (Site d))) {x y by_ : Site d}
    (p : (openSubgraph d ω).Walk by_ y) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) by_ y :=
  pap_connected_removeSite_of_walk_avoid ω x p hx






















def pap_CoherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) y ∧
        Connected d (removeSite x ω) (b y) y)




theorem pap_privateArm_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : pap_CoherentSelector ω n) : daepf_PrivateArm ω n := h



theorem pap_coherentSelector_iff_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    pap_CoherentSelector ω n ↔ daepf_PrivateArm ω n := Iff.rfl





















theorem pap_coherentSelector_of_twoTrif_local (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
    (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
    (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
    (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_twoTrif ω n b hx0y0 htwo hbx0 hby0
    hpriv_xy hfar_xy hpriv_yx hfar_yx



theorem pap_coherentSelector_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_noTrif ω n hno




theorem pap_coherentSelector_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    pap_CoherentSelector ω n :=
  daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq







theorem pap_Tcount_le_boundary_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : pap_CoherentSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn (pap_privateArm_of_coherentSelector ω n h)














theorem pap_burton_keane_bernoulli_of_coherentSelector (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      pap_CoherentSelector ω n)
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
  daepf_burton_keane_bernoulli_of_privateArm hd p hp1 hp0
    (fun ω n hn => pap_privateArm_of_coherentSelector ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
