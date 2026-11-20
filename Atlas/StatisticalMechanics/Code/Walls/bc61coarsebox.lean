/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Walls.bc60upperlines
import Code.Walls.bc54coarse
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}









noncomputable def bc61_boxAround (d L : ℕ) (y : Site d) : Finset (Site d) := by
  classical
  exact ((box_finite d L).image (fun z => z + y)).toFinset


theorem bc61_mem_boxAround {d L : ℕ} {y x : Site d} :
    x ∈ bc61_boxAround d L y ↔ (x - y) ∈ box d L := by
  classical
  unfold bc61_boxAround
  rw [Set.Finite.mem_toFinset, Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; simpa using hz
  · intro h; exact ⟨x - y, h, by ring⟩


theorem bc61_boxAround_zero (d L : ℕ) : bc61_boxAround d L 0 = boxFinsetBK d L := by
  classical
  ext x
  rw [bc61_mem_boxAround, boxFinsetBK, Set.Finite.mem_toFinset]
  simp



theorem bc61_removeBox_le (d L : ℕ) (y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d L y) ω ≤ ω :=
  daep_removeSites_le _ ω


theorem bc61_connected_of_cut {d L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    {a b : Site d} (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    Connected d ω a b :=
  connected_mono (bc61_removeBox_le d L y ω) h



theorem bc61_removeBox_apply_of_notMem {d L : ℕ} {y : Site d} {a b : Site d}
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d L y) ω s(a, b) = ω s(a, b) := by
  classical
  unfold removeSites
  rw [if_neg]
  rintro ⟨t, ht, htmem⟩
  rw [Sym2.mem_iff] at htmem
  rcases htmem with rfl | rfl
  · exact ha ht
  · exact hb ht



theorem bc61_cut_adj_connected {d L : ℕ} {y : Site d} {a b : Site d}
    {ω : ConfigSpace (Sym2 (Site d))}
    (hadj : (hypercubicLattice d).Adj a b) (hopen : ω s(a, b) = true)
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y) :
    Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
  refine IsOpenEdge.connected ⟨hadj, ?_⟩
  rw [bc61_removeBox_apply_of_notMem ha hb ω]; exact hopen














def bc61_IsCoarseTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    
    (∃ b₁ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₁ a₁) ∧
    (∃ b₂ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₂ a₂) ∧
    (∃ b₃ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₃ a₃) ∧
    
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    
    (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃)















theorem bc61_mem_boxAround_zero {L : ℕ} {x : Site 2} :
    x ∈ bc61_boxAround 2 L 0 ↔ x ∈ box 2 L := by
  rw [bc61_mem_boxAround]; simp


theorem bc61_pt_outside_boxAround {L : ℕ} {k h : ℤ} (hk : (L : ℤ) < k) :
    bc57_pt k h ∉ bc61_boxAround 2 L 0 := by
  rw [bc61_mem_boxAround_zero, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  rw [bc57_pt_fst]; omega




theorem bc61_upperLines_rightArm_reach {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1 + (j : ℤ)) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt ((L : ℤ) + 1) h)
  | succ i ih =>
    have hcol : (L : ℤ) < (L : ℤ) + 1 + (i : ℤ) := by omega
    have hcol1 : (L : ℤ) < (L : ℤ) + 1 + (i : ℤ) + 1 := by omega
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
        (bc57_pt ((L : ℤ) + 1 + (i : ℤ)) h) (bc57_pt ((L : ℤ) + 1 + (i : ℤ) + 1) h) :=
      bc61_cut_adj_connected (bc57_pt_adj _ h) (bc60_open _ hh)
        (bc61_pt_outside_boxAround hcol) (bc61_pt_outside_boxAround hcol1)
    have hcast : ((L : ℤ) + 1 + ((i + 1 : ℕ) : ℤ)) = (L : ℤ) + 1 + (i : ℤ) + 1 := by
      push_cast; ring
    rw [hcast]; exact ih.trans hstep



theorem bc61_upperLines_rightArm_infinite {L : ℕ} {h : ℤ} (hh : 1 ≤ h) :
    (cluster 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h)).Infinite := by
  rw [cluster_infinite_iff]
  intro j
  refine ⟨bc57_pt ((L : ℤ) + 1 + ((L : ℤ) + 1 + (j : ℤ))) h, ?_, ?_⟩
  · rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
    rw [bc57_pt_fst]
    have : (L : ℤ) + 1 + ((L : ℤ) + 1 + (j : ℤ)) ≥ (j : ℤ) + 1 := by omega
    omega
  · have := bc61_upperLines_rightArm_reach (L := L) hh ((L : ℤ) + 1 + (j : ℤ)).toNat
    have hcast : (((L : ℤ) + 1 + (j : ℤ)).toNat : ℤ) = (L : ℤ) + 1 + (j : ℤ) := by
      rw [Int.toNat_of_nonneg]; positivity
    rwa [hcast] at this





theorem bc61_upperLines_arm_disconnected {L : ℕ} {h h' : ℤ} (hne : h ≠ h') :
    ¬ Connected 2 (removeSites (bc61_boxAround 2 L 0) bc60_upperLines)
      (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1) h') := by
  intro hconn
  have hω : Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) h) (bc57_pt ((L : ℤ) + 1) h') :=
    bc61_connected_of_cut hconn
  have hht : (bc57_pt ((L : ℤ) + 1) h') 1 = h :=
    bc60_height_invariant (by rw [bc57_pt_snd]) hω
  rw [bc57_pt_snd] at hht
  exact hne hht.symm




theorem bc61_upperLines_arm_boxAdjacent {L : ℕ} {h : ℤ} (hh : 1 ≤ h) (hhL : h ≤ (L : ℤ)) :
    ∃ b ∈ bc61_boxAround 2 L 0, (openSubgraph 2 bc60_upperLines).Adj b (bc57_pt ((L : ℤ) + 1) h) := by
  refine ⟨bc57_pt (L : ℤ) h, ?_, ?_⟩
  · rw [bc61_mem_boxAround_zero, mem_box]; intro i; fin_cases i
    · change ((bc57_pt (L : ℤ) h) 0).natAbs ≤ L; rw [bc57_pt_fst]; simp
    · change ((bc57_pt (L : ℤ) h) 1).natAbs ≤ L; rw [bc57_pt_snd]; omega
  · exact ⟨bc57_pt_adj (L : ℤ) h, bc60_open (L : ℤ) hh⟩










theorem bc61_wholeBox_severs_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
  refine ⟨bc57_pt ((L : ℤ) + 1) 1, bc57_pt ((L : ℤ) + 1) 2, bc57_pt ((L : ℤ) + 1) 3,
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (1:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (2:ℤ) ≤ L)),
    bc61_upperLines_arm_boxAdjacent (by norm_num) (by exact_mod_cast (by omega : (3:ℤ) ≤ L)),
    ⟨bc61_upperLines_rightArm_infinite (by norm_num),
     bc61_upperLines_rightArm_infinite (by norm_num),
     bc61_upperLines_rightArm_infinite (by norm_num)⟩,
    ⟨?_, ?_, ?_⟩⟩
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)
  · exact bc61_upperLines_arm_disconnected (by norm_num)








theorem bc61_singleSite_fails_upperLines {G : Finset (Sym2 (Site 2))} {a a' : Site 2}
    (ha : a 1 ≤ 1) (ha' : a' 1 ≤ 1)
    (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
    (hinf' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' :=
  bc60_arms_connected ha ha' hinf hinf'









theorem bc61_contrast_upperLines {L : ℕ} (hL : 3 ≤ L) :
    bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧
    (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 →
      (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite →
      (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite →
      Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a') :=
  ⟨bc61_wholeBox_severs_upperLines hL,
   fun _ _ _ ha ha' hinf hinf' => bc61_singleSite_fails_upperLines ha ha' hinf hinf'⟩















noncomputable def bc61_coarseTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc61_IsCoarseTrifurcation ω L y)


theorem bc61_mem_coarseTrifFinset {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d} :
    y ∈ bc61_coarseTrifFinset ω L R ↔
      y ∈ box d R ∧ bc61_IsCoarseTrifurcation ω L y := by
  classical
  rw [bc61_coarseTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]


noncomputable def bc61_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : ℕ :=
  (bc61_coarseTrifFinset ω L R).card








def bc61_CoarseForestLeafCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj) (ιT : Site d → W) (lamL : W → Site d),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    
    (∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → 3 ≤ G.degree (ιT y)) ∧
    (∀ y, y ∈ box d R → bc61_IsCoarseTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc61_IsCoarseTrifurcation ω L z → ιT y = ιT z → y = z) ∧
    
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))












theorem bc61_coarseTcount_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨W, _, _, _, G, _, ιT, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  have hιinjOn : Set.InjOn ιT Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, bc61_mem_coarseTrifFinset] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [bc61_mem_coarseTrifFinset] at hyT
    exact hdeg3 y hyT.1 hyT.2
  
  calc bc61_coarseTcount ω L R = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card :=
        flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ boxSV_boundaryCard d R := flc2_leaf_card_le_boundary G R lamL hlammap hlaminj






















theorem bc61_coarseTrif_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | bc61_IsCoarseTrifurcation ω L 0} with hp
  have hkey : ∀ R, ((boxFinsetBK d R).card : ℝ≥0∞) * p ≤ (bdry R : ℝ≥0∞) := by
    intro R
    have hle : ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞) := by
      calc ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry R : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω; simp only; exact_mod_cast hbound ω R
        _ = (bdry R : ℝ≥0∞) := by rw [lintegral_const]; simp
    rw [hexp R]; exact hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ R, ((boxFinsetBK d R).card : ℝ) * pr ≤ (bdry R : ℝ) := by
    intro R
    have h := hkey R
    have h' : (((boxFinsetBK d R).card : ℝ≥0∞) * p).toReal ≤ (bdry R : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ R, (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := fun R => by exact_mod_cast hvol R
  have hle : ∀ R, pr ≤ (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ) := by
    intro R
    rw [le_div_iff₀ (hvolr R)]
    linarith [hkeyr R]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this




















def bc61_CoarseTrifExistence (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ) : Prop :=
  0 < μ {ω | numInfiniteClusters d ω = ⊤} →
    0 < μ {ω | bc61_IsCoarseTrifurcation ω L 0}









theorem bc61_infiniteClusters_top_null_of_coarse
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ) (bdry : ℕ → ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
    (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  have hprob0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
    bc61_coarseTrif_prob_eq_zero μ L bdry hexp hbound hvol hdens
  by_contra htop
  have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr htop
  have := hexist hpos
  rw [hprob0] at this
  exact lt_irrefl 0 this
































theorem bc61_status :
    
    (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) ∧
    (∀ {L : ℕ}, 3 ≤ L →
      (∀ (G : Finset (Sym2 (Site 2))) (a a' : Site 2), a 1 ≤ 1 → a' 1 ≤ 1 →
        (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite →
        (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite →
        Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a')) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bc61_CoarseForestLeafCount ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) :=
  ⟨fun hL => bc61_wholeBox_severs_upperLines hL,
   fun _hL _G _a _a' ha ha' hi hi' => bc61_singleSite_fails_upperLines ha ha' hi hi',
   fun ω L R h => bc61_coarseTcount_le_boundary_of_forest ω L R h⟩

end StatMech.Walls
