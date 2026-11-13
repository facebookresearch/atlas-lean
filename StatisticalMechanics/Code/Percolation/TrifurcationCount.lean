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
import Code.Percolation.BurtonKeaneMergeGeom
import Code.Percolation.BurtonKeaneClose

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












theorem tfc_boundary_cross_vertex (n : ℕ) (hn : 1 ≤ n) (z z' : Site d) (hz : z ∈ box d n)
    (hz' : z' ∉ box d n) (hadj : (hypercubicLattice d).Adj z z') :
    z ∈ vertexBoundary d n := by
  rw [mem_box] at hz; rw [mem_box] at hz'; push_neg at hz'
  obtain ⟨i, hi⟩ := hz'
  rw [hypercubicLattice_adj] at hadj
  
  have hipos : 1 ≤ (z i - z' i).natAbs := by
    rcases Nat.eq_zero_or_pos (z i - z' i).natAbs with h0 | hpos
    · exfalso; rw [Int.natAbs_eq_zero, sub_eq_zero] at h0
      have := hz i; rw [h0] at this; omega
    · exact hpos
  
  have hterm : (z i - z' i).natAbs = 1 := by
    by_contra hne
    have hge2 : 2 ≤ (z i - z' i).natAbs := by omega
    have hle : (z i - z' i).natAbs ≤ ∑ j, (z j - z' j).natAbs :=
      Finset.single_le_sum (f := fun j => (z j - z' j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  
  have hzin : (z i).natAbs = n := by have h1 := hz i; omega
  refine ⟨fun j => hz j, ?_⟩
  rw [mem_box]; push_neg
  exact ⟨i, by rw [hzin]; omega⟩











theorem tfc_walk_crossing {V : Type*} (G : SimpleGraph V) (p : V → Prop) [DecidablePred p] :
    ∀ {x y : V} (w : G.Walk x y), p x → ¬ p y →
      ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧ G.Reachable x a := by
  intro x y w
  induction w with
  | nil => intro hx hy; exact absurd hx hy
  | @cons u v z hadj w' ih =>
    intro hu hz
    by_cases hv : p v
    · obtain ⟨a, b, hab, ha, hb, hr⟩ := ih hv hz
      exact ⟨a, b, hab, ha, hb, (hadj.reachable).trans hr⟩
    · exact ⟨u, v, hadj, hu, hv, Reachable.refl u⟩












theorem tfc_trif_cluster_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (htri : IsTrifurcation d ω x) : (cluster d ω x).Infinite := by
  obtain ⟨a₁, _, _, _, hconn, hinf, _⟩ := htri
  rw [cluster_eq_of_connected hconn.1]; exact hinf.1





theorem tfc_trif_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ z ∈ vertexBoundary d n, Connected d ω x z := by
  classical
  have hxinf : (cluster d ω x).Infinite := tfc_trif_cluster_infinite ω x htri
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω x).mp hxinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨a, b, hab, ha, hb, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω) (fun v => v ∈ box d n) w hxbox hybox
  have hablat : (hypercubicLattice d).Adj a b := (openSubgraph_le ω) hab
  exact ⟨a, tfc_boundary_cross_vertex n hn a b ha hb hablat, hr⟩



open Classical in


noncomputable def tfc_trifFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) :=
  (boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)

theorem tfc_trifFinset_card (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (tfc_trifFinset ω n).card = Tcount d ω n := rfl


noncomputable def tfc_boundaryFinset (d n : ℕ) : Finset (Site d) :=
  (vertexBoundary_finite d n).toFinset

theorem tfc_boundaryFinset_card (d n : ℕ) :
    (tfc_boundaryFinset d n).card = boxSV_boundaryCard d n := rfl

theorem tfc_mem_trifFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x : Site d} :
    x ∈ tfc_trifFinset ω n ↔ x ∈ box d n ∧ IsTrifurcation d ω x := by
  classical
  rw [tfc_trifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

theorem tfc_mem_boundaryFinset {d n : ℕ} {x : Site d} :
    x ∈ tfc_boundaryFinset d n ↔ x ∈ vertexBoundary d n := by
  rw [tfc_boundaryFinset, Set.Finite.mem_toFinset]


theorem tfc_boundaryCard_zero (d : ℕ) : boxSV_boundaryCard d 0 = 0 := by
  unfold boxSV_boundaryCard
  rw [Set.Finite.toFinset_eq_empty.mpr, Finset.card_empty]
  rw [vertexBoundary]; norm_num












theorem tfc_Tcount_le_of_injOn (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : ∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmaps x hx.1 hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    exact hinj x hx.1 hx.2 y hy.1 hy.2 hxy




theorem tfc_Tcount_le_card (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : Set.MapsTo φ (tfc_trifFinset ω n) (tfc_boundaryFinset d n))
    (hinj : Set.InjOn φ (tfc_trifFinset ω n)) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  exact Finset.card_le_card_of_injOn φ hmaps hinj




















def tfc_BoundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y)




theorem tfc_Tcount_le_boundary_of_residue (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tfc_BoundaryArmInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact tfc_Tcount_le_of_injOn ω n φ hmaps hinj









theorem tfc_Tcount_le_boundary_of_injection
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), tfc_BoundaryArmInjection ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n => tfc_Tcount_le_boundary_of_residue ω n (hres ω n)




















def tfc_DistinctArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      φ x ∈ vertexBoundary d n ∧ Connected d ω x (φ x)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y)




theorem tfc_boundaryArmInjection_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) : tfc_BoundaryArmInjection ω n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact ⟨φ, fun x hx htri => (hmaps x hx htri).1, hinj⟩



theorem tfc_Tcount_le_boundary_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n (tfc_boundaryArmInjection_of_distinctArmEnds ω n h)



def tfc_armEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) : Set (Site d) :=
  {z | z ∈ vertexBoundary d n ∧ Connected d ω x z}






theorem tfc_armEnds_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    (tfc_armEnds ω n x).Nonempty := by
  obtain ⟨z, hzb, hzc⟩ := tfc_trif_reaches_boundary ω n hn x hxbox htri
  exact ⟨z, hzb, hzc⟩







theorem tfc_distinctArmEnds_iff_injSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    tfc_DistinctArmEnds ω n ↔
      ∃ φ : Site d → Site d,
        (∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ tfc_armEnds ω n x) ∧
        (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
          IsTrifurcation d ω y → φ x = φ y → x = y) := by
  constructor
  · rintro ⟨φ, hmaps, hinj⟩
    exact ⟨φ, fun x hx htri => hmaps x hx htri, hinj⟩
  · rintro ⟨φ, hmaps, hinj⟩
    exact ⟨φ, fun x hx htri => hmaps x hx htri, hinj⟩








theorem tfc_distinctArmEnds_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    tfc_DistinctArmEnds ω n := by
  classical
  
  refine ⟨fun x => if hx : x ∈ box d n ∧ IsTrifurcation d ω x then
      (tfc_armEnds_nonempty ω n hn x hx.1 hx.2).choose else x, ?_, ?_⟩
  · intro x hxbox htri
    simp only [dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    have hspec := (tfc_armEnds_nonempty ω n hn x hxbox htri).choose_spec
    exact ⟨hspec.1, hspec.2⟩
  · 
    intro x hxbox htri y hybox htriy _
    exact hsub x y hxbox htri hybox htriy












theorem tfc_residue_zero_iff_no_origin_trif (ω : ConfigSpace (Sym2 (Site d))) :
    tfc_BoundaryArmInjection ω 0 ↔ ¬ IsTrifurcation d ω 0 := by
  classical
  constructor
  · rintro ⟨φ, hmaps, _⟩ htri0
    have h0box : (0 : Site d) ∈ box d 0 := by
      rw [mem_box]; intro i; rw [show (0 : Site d) i = 0 from rfl]; simp
    have hmem := hmaps 0 h0box htri0
    rw [vertexBoundary] at hmem
    simp only [Nat.zero_sub, Set.mem_diff] at hmem
    exact hmem.2 hmem.1
  · intro h0
    have hx0 : ∀ x : Site d, x ∈ box d 0 → x = 0 := by
      intro x hxbox
      funext i; have := (mem_box.mp hxbox) i
      rw [show (0 : Site d) i = 0 from rfl]; omega
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro x hxbox htri
      exact absurd ((hx0 x hxbox) ▸ htri) h0
    · intro x hxbox htri y _ _ _
      exact absurd ((hx0 x hxbox) ▸ htri) h0




theorem tfc_Tcount_zero_le_boundary_iff (ω : ConfigSpace (Sym2 (Site d))) :
    Tcount d ω 0 ≤ boxSV_boundaryCard d 0 ↔ ¬ IsTrifurcation d ω 0 := by
  classical
  rw [tfc_boundaryCard_zero, Nat.le_zero, ← tfc_trifFinset_card, Finset.card_eq_zero,
    tfc_trifFinset, Finset.filter_eq_empty_iff]
  constructor
  · intro h htri0
    have h0box : (0 : Site d) ∈ boxFinsetBK d 0 := by
      rw [boxFinsetBK, Set.Finite.mem_toFinset, mem_box]; intro i
      rw [show (0 : Site d) i = 0 from rfl]; simp
    exact h h0box htri0
  · intro h0 x hxbox
    rw [boxFinsetBK, Set.Finite.mem_toFinset] at hxbox
    have hx0 : x = 0 := by
      funext i; have := (mem_box.mp hxbox) i
      rw [show (0 : Site d) i = 0 from rfl]; omega
    exact hx0 ▸ h0

















theorem tfc_trifurcation_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0)) :
    μ {ω | IsTrifurcation d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsTrifurcation d ω 0} with hp
  have hkey : ∀ n, 1 ≤ n → ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (bdry n : ℝ≥0∞) := by
    intro n hn
    have hexp := expected_Tcount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ ≤ (bdry n : ℝ≥0∞) := by
      calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry n : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω; simp only
            exact_mod_cast hbound ω n hn
        _ = (bdry n : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n, 1 ≤ n → ((boxFinsetBK d n).card : ℝ) * pr ≤ (bdry n : ℝ) := by
    intro n hn
    have h := hkey n hn
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal ≤ (bdry n : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by
    intro n; exact_mod_cast hvol n
  have hle : ∀ᶠ n in atTop, pr ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [le_div_iff₀ (hvolr n)]; linarith [hkeyr n hn]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this




theorem tfc_numInfiniteClusters_ae_const_ne_top
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  have htri0 : μ {ω | IsTrifurcation d ω 0} = 0 :=
    tfc_trifurcation_prob_eq_zero μ herg.isTranslationInvariant bdry hbound hvol hdens
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const_uniqueness μ herg
  refine ⟨k, ?_, hk⟩
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0





theorem tfc_burton_keane_uniqueness_full
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ :=
      tfc_numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top
      (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)
  exact ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩


























theorem tfc_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      tfc_DistinctArmEnds ω n)
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
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (fun ω n hn => tfc_Tcount_le_boundary_of_distinctArmEnds ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
