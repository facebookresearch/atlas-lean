/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Mathlib
import Code.Walls.bfinfinalclose
import Code.Walls.bcvcutvertex

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

#check @bfin_SuperCutBridge













def bsc_IsBoxCentre (L : ℕ) (y : Site d) : Prop :=
  ∀ x : Site d, x ∈ bc61_boxAround d L y ↔ bgn_idx L x = bgn_idx L y


theorem bsc_ediv_zero_iff {L : ℕ} {a : ℤ} :
    (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = 0 ↔ a.natAbs ≤ L := by
  have hb : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  constructor
  · intro hq
    have h1 : (a + (L : ℤ)) % (2 * (L : ℤ) + 1) = a + (L : ℤ) := by
      have := Int.emod_add_ediv (a + (L : ℤ)) (2 * (L : ℤ) + 1)
      rw [hq] at this; omega
    have h2 : 0 ≤ (a + (L : ℤ)) % (2 * (L : ℤ) + 1) := Int.emod_nonneg _ (by omega)
    have h3 : (a + (L : ℤ)) % (2 * (L : ℤ) + 1) < 2 * (L : ℤ) + 1 := Int.emod_lt_of_pos _ hb
    rw [h1] at h2 h3; omega
  · intro h
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)




theorem bsc_boxCentre_zero (d L : ℕ) : bsc_IsBoxCentre L (0 : Site d) := by
  intro x
  have hidx0 : bgn_idx L (0 : Site d) = 0 := by
    funext i
    show ((0 : Site d) i + (L : ℤ)) / (2 * (L : ℤ) + 1) = (0 : Site d) i
    simp only [Pi.zero_apply, zero_add]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by omega)
  rw [hidx0, bc61_mem_boxAround, sub_zero, mem_box]
  constructor
  · intro h; funext i
    have : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = 0 := (bsc_ediv_zero_iff).mpr (h i)
    simpa [bgn_idx] using this
  · intro h i
    have := congrFun h i
    simp only [bgn_idx, Pi.zero_apply] at this
    exact (bsc_ediv_zero_iff).mp this

#check @bsc_boxCentre_zero









theorem bsc_box_isolated {L : ℕ} {y a : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (ha : a ∈ bc61_boxAround d L y) (w : Site d) :
    ¬ (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a w := by
  intro hadj
  have hopen : removeSites (bc61_boxAround d L y) ω s(a, w) = true := hadj.2
  unfold removeSites at hopen
  rw [if_pos ⟨a, ha, by rw [Sym2.mem_iff]; left; rfl⟩] at hopen
  exact absurd hopen (by simp)


theorem bsc_notMem_box_of_infinite {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    a ∉ bc61_boxAround d L y := by
  intro ha
  
  have hsub : cluster d (removeSites (bc61_boxAround d L y) ω) a ⊆ {a} := by
    intro z hz
    have hr : (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Reachable a z := hz
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact Set.mem_singleton_iff.mpr rfl
    | cons hadj _ => exact absurd hadj (bsc_box_isolated ω ha _)
  exact hinf (Set.Finite.subset (Set.finite_singleton a) hsub)





theorem bsc_hub_adj_armImage {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y)
    (hinc : bc67_GnIncident ω L y a)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    bgn_idx L a ≠ bgn_idx L y ∧ (bgn_Gn ω L).Adj (bgn_idx L y) (bgn_idx L a) := by
  have haout : a ∉ bc61_boxAround d L y := bsc_notMem_box_of_infinite hinf
  have hne : bgn_idx L a ≠ bgn_idx L y := by
    intro h; exact haout ((hy a).mpr h)
  refine ⟨hne, hne.symm, ?_⟩
  obtain ⟨b, hbbox, hbadj⟩ := hinc
  have hbidx : bgn_idx L b = bgn_idx L y := (hy b).mp hbbox
  exact ⟨b, a, hbidx, rfl, hbadj⟩











theorem bsc_superReach_of_siteConn {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) {a b : Site d}
    (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj q ih =>
    refine Reachable.trans ?_ ih
    
    have hopen : removeSites (bc61_boxAround d L y) ω s(x, z) = true := hadj.2
    have hcond : ¬ ∃ t ∈ bc61_boxAround d L y, t ∈ s(x, z) := by
      intro hh; unfold removeSites at hopen; rw [if_pos hh] at hopen; exact absurd hopen (by simp)
    have hxout : x ∉ bc61_boxAround d L y := fun hx => hcond ⟨x, hx, by rw [Sym2.mem_iff]; left; rfl⟩
    have hzout : z ∉ bc61_boxAround d L y := fun hz => hcond ⟨z, hz, by rw [Sym2.mem_iff]; right; rfl⟩
    have hxne : bgn_idx L x ≠ bgn_idx L y := fun hh => hxout ((hy x).mpr hh)
    have hzne : bgn_idx L z ≠ bgn_idx L y := fun hh => hzout ((hy z).mpr hh)
    
    have hωopen : (openSubgraph d ω).Adj x z := by
      refine ⟨hadj.1, ?_⟩
      have hle := bc61_removeBox_le d L y ω s(x, z)
      rw [hopen] at hle
      revert hle; cases ω s(x, z) <;> simp
    by_cases hxz : bgn_idx L x = bgn_idx L z
    · exact hxz ▸ Reachable.refl _
    · have hedge : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Adj (bgn_idx L x) (bgn_idx L z) :=
        ⟨⟨hxz, x, z, rfl, rfl, hωopen⟩, hxne, hzne⟩
      exact hedge.reachable

#check @bsc_hub_adj_armImage
#check @bsc_superReach_of_siteConn








theorem bsc_ediv_eq_iff {L : ℕ} {a m : ℤ} :
    (a + (L : ℤ)) / (2 * (L : ℤ) + 1) = m ↔ (a - (2 * (L : ℤ) + 1) * m).natAbs ≤ L := by
  have hb : (0 : ℤ) < 2 * (L : ℤ) + 1 := by positivity
  have hkey : (a + (L : ℤ)) / (2 * (L : ℤ) + 1)
      = (a - (2 * (L : ℤ) + 1) * m + (L : ℤ)) / (2 * (L : ℤ) + 1) + m := by
    rw [← Int.add_mul_ediv_right _ m (by omega : (2 * (L : ℤ) + 1) ≠ 0)]
    congr 1; ring
  rw [hkey]
  constructor
  · intro h; exact (bsc_ediv_zero_iff).mp (by omega)
  · intro h; have := (bsc_ediv_zero_iff).mpr h; omega



theorem bsc_fiber_finite (L : ℕ) (j : Site d) : {x : Site d | bgn_idx L x = j}.Finite := by
  set c : Site d := fun i => (2 * (L : ℤ) + 1) * j i with hc
  have hset : {x : Site d | bgn_idx L x = j} = ↑(bc61_boxAround d L c) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, bc61_mem_boxAround, mem_box]
    constructor
    · intro h i
      have := congrFun h i
      simp only [bgn_idx] at this
      have h2 := (bsc_ediv_eq_iff).mp this
      simpa [Pi.sub_apply, hc] using h2
    · intro h; funext i
      simp only [bgn_idx]
      refine (bsc_ediv_eq_iff).mpr ?_
      have := h i
      simpa [Pi.sub_apply, hc] using this
  rw [hset]; exact (bc61_boxAround d L c).finite_toSet


theorem bsc_deleteWalk_support_avoid {V : Type*} {G : SimpleGraph V} {t : V} :
    ∀ {u v : V} (p : (bkg_deleteVertex G t).Walk u v), u ≠ t → t ∉ p.support := by
  intro u v p
  induction p with
  | nil => intro hu; simpa using hu.symm
  | @cons u z v hadj q ih =>
    intro hu
    rw [Walk.support_cons, List.mem_cons]; push_neg
    exact ⟨hu.symm, ih hadj.2.2⟩


theorem bsc_ray34_of_deleteReach {V : Type*} {G : SimpleGraph V} {t u v : V}
    (hu : u ≠ t) (h : (bkg_deleteVertex G t).Reachable u v) :
    ray34_AvoidReach G {t} u v := by
  obtain ⟨p⟩ := h
  have hle : bkg_deleteVertex G t ≤ G := fun a b hab => hab.1
  refine ⟨p.mapLe hle, ?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  simp only [Set.mem_singleton_iff]
  intro hwt; subst hwt
  exact bsc_deleteWalk_support_avoid p hu hw




theorem bsc_arm_ray_infinite {L : ℕ} {y a : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} (bgn_idx L a)).Infinite := by
  have haout : a ∉ bc61_boxAround d L y := bsc_notMem_box_of_infinite hinf
  have haidx : bgn_idx L a ≠ bgn_idx L y := fun h => haout ((hy a).mpr h)
  
  have himg : (bgn_idx L) '' (cluster d (removeSites (bc61_boxAround d L y) ω) a)
      ⊆ ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} (bgn_idx L a) := by
    rintro _ ⟨c, hc, rfl⟩
    have hconn : Connected d (removeSites (bc61_boxAround d L y) ω) a c := hc
    have hreach := bsc_superReach_of_siteConn hy hconn
    exact bsc_ray34_of_deleteReach haidx hreach
  refine Set.Infinite.mono himg ?_
  
  intro hfin
  apply hinf
  have hsub : cluster d (removeSites (bc61_boxAround d L y) ω) a
      ⊆ ⋃ j ∈ (bgn_idx L) '' (cluster d (removeSites (bc61_boxAround d L y) ω) a),
          {x : Site d | bgn_idx L x = j} := by
    intro x hx
    exact Set.mem_biUnion ⟨x, hx, rfl⟩ rfl
  exact Set.Finite.subset (hfin.biUnion (fun j _ => bsc_fiber_finite L j)) hsub

#check @bsc_arm_ray_infinite

















def bsc_BoxesInternallyConnected (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∀ u v : Site d, bgn_idx L u = bgn_idx L v → bgn_idx L u ≠ bgn_idx L y →
    Connected d (removeSites (bc61_boxAround d L y) ω) u v






theorem bsc_siteConn_of_superReach {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    {a b : Site d} (ha : bgn_idx L a ≠ bgn_idx L y) (hb : bgn_idx L b ≠ bgn_idx L y)
    (h : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b)) :
    Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
  obtain ⟨p⟩ := h
  
  have key : ∀ {j k : Site d}
      (p : (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Walk j k),
      ∀ a' b', bgn_idx L a' = j → bgn_idx L b' = k →
        j ≠ bgn_idx L y → k ≠ bgn_idx L y →
        Connected d (removeSites (bc61_boxAround d L y) ω) a' b' := by
    intro j k p
    induction p with
    | nil =>
      intro a' b' ha' hb' hjne hkne
      
      exact hint a' b' (ha'.trans hb'.symm) (by rw [ha']; exact hjne)
    | @cons j z k hadj q ih =>
      intro a' b' ha' hb' hjne hkne
      obtain ⟨hbgnadj, hjne', hzne⟩ := hadj
      obtain ⟨_, c, e, hc, he, hce⟩ := hbgnadj
      
      have hac : Connected d (removeSites (bc61_boxAround d L y) ω) a' c :=
        hint a' c (ha'.trans hc.symm) (by rw [ha']; exact hjne)
      
      have hcout : c ∉ bc61_boxAround d L y := fun hcbox => hjne (hc ▸ (hy c).mp hcbox)
      have heout : e ∉ bc61_boxAround d L y := fun hebox => hzne (he ▸ (hy e).mp hebox)
      have hce_conn : Connected d (removeSites (bc61_boxAround d L y) ω) c e :=
        bc61_cut_adj_connected hce.1 hce.2 hcout heout
      
      have heb : Connected d (removeSites (bc61_boxAround d L y) ω) e b' := ih e b' he hb' hzne hkne
      exact (hac.trans hce_conn).trans heb
  exact key p a b rfl rfl ha hb





theorem bsc_super_disconnected {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    {a b : Site d} (ha : bgn_idx L a ≠ bgn_idx L y) (hb : bgn_idx L b ≠ bgn_idx L y)
    (hdis : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable (bgn_idx L a) (bgn_idx L b) :=
  fun hr => hdis (bsc_siteConn_of_superReach hy hint ha hb hr)







theorem bsc_bridge_of_internalConn {L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hy : bsc_IsBoxCentre L y) (hint : bsc_BoxesInternallyConnected ω L y)
    (htri : bc67_IsGnTrifurcation ω L y) :
    ∃ w₁ w₂ w₃ : Site d,
      w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite := by
  obtain ⟨a₁, a₂, a₃, ⟨hi₁, hi₂, hi₃⟩, ⟨hf₁, hf₂, hf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := htri
  
  have hd₁₂ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ := hcut₁₂
  have hd₁₃ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ := hcut₁₃
  have hd₂₃ : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃ := hcut₂₃
  obtain ⟨hne₁, hadj₁⟩ := bsc_hub_adj_armImage hy hi₁ hf₁
  obtain ⟨hne₂, hadj₂⟩ := bsc_hub_adj_armImage hy hi₂ hf₂
  obtain ⟨hne₃, hadj₃⟩ := bsc_hub_adj_armImage hy hi₃ hf₃
  refine ⟨bgn_idx L a₁, bgn_idx L a₂, bgn_idx L a₃, hne₁, hne₂, hne₃,
    hadj₁, hadj₂, hadj₃, ?_, ?_, ?_,
    bsc_arm_ray_infinite hy hf₁, bsc_arm_ray_infinite hy hf₂, bsc_arm_ray_infinite hy hf₃⟩
  · exact bsc_super_disconnected hy hint hne₁ hne₂ hd₁₂
  · exact bsc_super_disconnected hy hint hne₁ hne₃ hd₁₃
  · exact bsc_super_disconnected hy hint hne₂ hne₃ hd₂₃





theorem bsc_bfin_SuperCutBridge_of_hyp (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ)
    (H : ∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
      bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) :
    bfin_SuperCutBridge ω L := by
  intro y htri
  obtain ⟨hy, hint⟩ := H y htri
  exact bsc_bridge_of_internalConn hy hint htri

#check @bsc_siteConn_of_superReach
#check @bsc_bfin_SuperCutBridge_of_hyp







theorem bsc_upperLines_forward {L : ℕ} (hL : 3 ≤ L) :
    ∃ w₁ w₂ w₃ : Site 2,
      (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧
      ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧
      ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite) := by
  have hy := bsc_boxCentre_zero 2 L
  obtain ⟨a₁, a₂, a₃, ⟨hi₁, hi₂, hi₃⟩, ⟨hf₁, hf₂, hf₃⟩, _⟩ :=
    bc67_upperLines_is_G_n_trifurcation hL
  obtain ⟨hne₁, hadj₁⟩ := bsc_hub_adj_armImage hy hi₁ hf₁
  obtain ⟨hne₂, hadj₂⟩ := bsc_hub_adj_armImage hy hi₂ hf₂
  obtain ⟨hne₃, hadj₃⟩ := bsc_hub_adj_armImage hy hi₃ hf₃
  exact ⟨bgn_idx L a₁, bgn_idx L a₂, bgn_idx L a₃, ⟨hne₁, hne₂, hne₃⟩,
    ⟨hadj₁, hadj₂, hadj₃⟩,
    ⟨bsc_arm_ray_infinite hy hf₁, bsc_arm_ray_infinite hy hf₂, bsc_arm_ray_infinite hy hf₃⟩⟩

#check @bsc_upperLines_forward







































theorem bsc_status {L : ℕ} (hL : 3 ≤ L) :
    
    (∃ w₁ w₂ w₃ : Site 2,
      (w₁ ≠ bgn_idx L (0 : Site 2) ∧ w₂ ≠ bgn_idx L (0 : Site 2) ∧ w₃ ≠ bgn_idx L (0 : Site 2)) ∧
      ((bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₁ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₂ ∧
       (bgn_Gn bc60_upperLines L).Adj (bgn_idx L (0 : Site 2)) w₃) ∧
      ((ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₁).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₂).Infinite ∧
       (ray34_AvoidCluster (bgn_Gn bc60_upperLines L) {bgn_idx L (0 : Site 2)} w₃).Infinite)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))),
      (∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
        bsc_IsBoxCentre L y ∧ bsc_BoxesInternallyConnected ω L y) →
      bfin_SuperCutBridge ω L) := by
  exact ⟨bsc_upperLines_forward hL, fun ω H => bsc_bfin_SuperCutBridge_of_hyp ω L H⟩

#check @bsc_status

end StatMech.Walls


#print axioms StatMech.Walls.bsc_hub_adj_armImage
#print axioms StatMech.Walls.bsc_arm_ray_infinite
#print axioms StatMech.Walls.bsc_superReach_of_siteConn
#print axioms StatMech.Walls.bsc_siteConn_of_superReach
#print axioms StatMech.Walls.bsc_bridge_of_internalConn
#print axioms StatMech.Walls.bsc_bfin_SuperCutBridge_of_hyp
#print axioms StatMech.Walls.bsc_upperLines_forward
#print axioms StatMech.Walls.bsc_status
