/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.BKForestLib
import Code.Percolation.ForestSelectorProve
import Code.Percolation.RootedForestPeelClose
import Code.Walls.bc26forest
import Code.Walls.bc27forestroot
import Code.Walls.bc31globalarm
import Code.Walls.bc34ray

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














theorem bc35_downArmSplit_of_privateFar (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d} (h : bkfl_PrivateFar ω b y x) :
    ¬ Connected d (removeSite y ω) (b y) (b x) :=
  bkfl_singleCut_sep_of_privateFar ω b h

































theorem bc35_TavoidingRayData_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : rfp_RootedArmDivergence ω n) :
    ∃ rank : Site d → ℕ ×ₗ ℕ, bc33_TavoidingRayData ω n rank := by
  
  obtain ⟨b, rank, hbdata, hrank, hdiv⟩ :=
    rfp_rootedSingleCutSeparation_of_armDivergence ω n h
  refine ⟨rank, ?_⟩
  apply bc34_TavoidingRayData_of_globalCutArm ω n rank b hbdata
  
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact fun hc => hdiv x hxbox htri y hybox htriy hxy hconn hlt hc.symm












theorem bc35_burton_keane_bernoulli_of_rootedArmDivergence (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rfp_RootedArmDivergence ω n)
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
          {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  classical
  
  
  
  
  set bfun : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → Site d :=
    fun ω n => if hn : 1 ≤ n then (hres ω n hn).choose else id with hbfun
  set rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ :=
    fun ω n => if hn : 1 ≤ n then (hres ω n hn).choose_spec.choose else fun _ => 0 with hrank
  have hbeq : ∀ ω n (hn : 1 ≤ n), bfun ω n = (hres ω n hn).choose := by
    intro ω n hn; simp only [hbfun, dif_pos hn]
  have hreq : ∀ ω n (hn : 1 ≤ n), rank ω n = (hres ω n hn).choose_spec.choose := by
    intro ω n hn; simp only [hrank, dif_pos hn]
  refine bc34_burton_keane_bernoulli_of_globalCutArm hd p hp1 hp0 rank bfun ?_ ?_ ?_ htrif
  · 
    intro ω n x hxbox htri y hybox htriy hxy hconn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · 
      rw [bc24_box_zero, Set.mem_singleton_iff] at hxbox hybox
      exact absurd (hxbox.trans hybox.symm) hxy
    · have hn : 1 ≤ n := hpos
      rw [hreq ω n hn]
      exact (hres ω n hn).choose_spec.choose_spec.2.1 x hxbox htri y hybox htriy hxy hconn
  · 
    intro ω n hn x hxbox htri
    rw [hbeq ω n hn]
    exact (hres ω n hn).choose_spec.choose_spec.1 x hxbox htri
  · 
    intro ω n hn x hxbox htri y hybox htriy hxy hconn hlt
    rw [hreq ω n hn] at hlt
    rw [hbeq ω n hn]
    set b := (hres ω n hn).choose with hb
    obtain ⟨hbdata, _hrankInj, hdiv⟩ := (hres ω n hn).choose_spec.choose_spec
    
    intro hc
    
    set T := tfc_trifFinset ω n with hTdef
    have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    have hbxnotin : b x ∉ T :=
      stac_infiniteCluster_notMem T ω (hbdata x hxbox htri).2.2
    have hbynotin : b y ∉ T :=
      stac_infiniteCluster_notMem T ω (hbdata y hybox htriy).2.2
    have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
    have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
    have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
    have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
    
    exact fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by
      (hdiv x hxbox htri y hybox htriy hxy hconn hlt) hc.symm


















theorem bc35_TavoidingRayData_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc26_PrivateFarOrder ω n) :
    bc33_TavoidingRayData ω n rank := by
  obtain ⟨b, hdata, hpair⟩ := h
  apply bc34_TavoidingRayData_of_globalCutArm ω n rank b
  · intro x hxbox htri; exact hdata x hxbox htri
  · intro x hxbox htri y hybox htriy hxy hconn _hlt
    exact bc35_downArmSplit_of_privateFar ω b
      (hpair y hybox htriy x hxbox htri (Ne.symm hxy) hconn.symm)
















theorem bc35_globalCutArm_of_singleCutTfree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x bx : Site d} (hbbox : bx ∈ box d n) (hbconn : Connected d ω x bx)
    (hinf : (cluster d (removeSite x ω) bx).Infinite)
    (hTfree : ∀ z, Connected d (removeSite x ω) bx z → z ∉ tfc_trifFinset ω n) :
    bx ∈ box d n ∧ Connected d ω x bx ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) bx).Infinite :=
  ⟨hbbox, hbconn, bc31_globalCut_infinite_of_singleCut_Tfree ω hinf hTfree⟩


















theorem bc35_globalCutArm_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) :=
  bc34_TavoidingRayData_of_threeChain_globalCut ω n b hx0box hmbox hgbox hx0m hx0g hmg
    hthree harm hsxm hsxg hsmg















theorem bc35_globalCutArm_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  apply bc34_TavoidingRayData_of_globalCutArm ω n rank b harm
  
  intro x hxbox htri yv hyvbox htriv hxy _hconn hlt
  rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
  · 
    rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
    · exact absurd rfl hxy
    · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · 
    rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
    · exact hsx0 i
    · rw [hry j, hry i] at hlt
      have hji : (j : ℕ) < i := by
        rw [Prod.Lex.toLex_lt_toLex] at hlt
        rcases hlt with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl 1)
        · exact h
      exact hssib i j hji
























theorem bc35_TavoidingRayData_of_clawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
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
    ∃ rank : Site d → ℕ ×ₗ ℕ, bc33_TavoidingRayData ω n rank :=
  bc35_TavoidingRayData_of_rootedArmDivergence ω n
    (rfp_rootedArmDivergence_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

end StatMech.Walls
