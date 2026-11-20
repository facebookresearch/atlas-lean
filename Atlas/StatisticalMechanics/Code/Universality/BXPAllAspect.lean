/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Code.Universality.BXPFromRSW

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip













theorem bxa_adj_coord_diff_le {d : ℕ} {x y : Site d}
    (h : (hypercubicLattice d).Adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  rw [hypercubicLattice_adj] at h
  calc (x i - y i).natAbs
      ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 1 := h






theorem bxa_walk_first_hit {ω : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 ω).Walk x y) (i : Fin 2) (t : ℤ)
    (hx : x i < t) (hy : t ≤ y i) :
    ∃ j ≤ p.length, (p.getVert j) i = t ∧ ∀ m < j, (p.getVert m) i < t := by
  
  
  have hlen : t ≤ (p.getVert p.length) i := by rw [p.getVert_length]; exact hy
  classical
  
  let P : ℕ → Prop := fun m => t ≤ (p.getVert m) i
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : t ≤ (p.getVert j) i := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  
  have hbelow : ∀ m < j, (p.getVert m) i < t := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact absurd hjP (not_le.2 hx)
  
  
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : (p.getVert k) i < t := hbelow k hkj
  
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  rw [hk] at hjP
  have hadj' : (hypercubicLattice 2).Adj (p.getVert k) (p.getVert (k + 1)) := hadj.1
  have hdiff := bxa_adj_coord_diff_le hadj' i
  
  have hle : (p.getVert (k + 1)) i ≤ t := by
    have habs : ((p.getVert k) i - (p.getVert (k + 1)) i).natAbs ≤ 1 := hdiff
    have hb : |(p.getVert k) i - (p.getVert (k + 1)) i| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast habs
    rw [abs_le] at hb
    omega
  have hjP' : t ≤ (p.getVert (k + 1)) i := hjP
  refine ⟨k + 1, by omega, le_antisymm hle hjP', ?_⟩
  intro m hm
  exact hbelow m (by omega)










theorem bxa_connectedWithin_restrict {ω : ConfigSpace (Sym2 (Site 2))}
    {S T : Set (Site 2)} {x y : Site 2} (hxS : x ∈ S) (hyS : y ∈ S)
    (h : ConnectedWithin 2 ω S ⟨x, hxS⟩ ⟨y, hyS⟩)
    (i : Fin 2) (t : ℤ) (hx : x i < t) (hy : t ≤ y i)
    (hslab : ∀ z ∈ S, z i ≤ t → z ∈ T) :
    ∃ (u : Site 2) (_ : u ∈ S), u i = t ∧
      ∃ (huT : u ∈ T) (hxT : x ∈ T),
        ConnectedWithin 2 ω T ⟨x, hxT⟩ ⟨u, huT⟩ := by
  classical
  
  obtain ⟨w⟩ := h
  let p : (openSubgraph 2 ω).Walk x y :=
    (w.map (SimpleGraph.Embedding.induce S).toHom)
  
  have hpsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce S).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, _, rfl⟩ := hz'
    exact a.2
  
  obtain ⟨j, hjle, hju, hjbelow⟩ := bxa_walk_first_hit p i t hx hy
  set u : Site 2 := p.getVert j with hu_def
  have huS : u ∈ S := hpsupp u (p.getVert_mem_support j)
  
  let q : (openSubgraph 2 ω).Walk x u := p.take j
  
  have hcoord : ∀ n ≤ j, (p.getVert n) i ≤ t := by
    intro n hn
    rcases lt_or_eq_of_le hn with hnj | hnj
    · exact le_of_lt (hjbelow n hnj)
    · rw [hnj]; exact le_of_eq hju
  
  have hqsupp : ∀ z ∈ q.support, z ∈ T := by
    intro z hz
    
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS : z ∈ S := hpsupp z hzp
    obtain ⟨n, hzn, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzp
    
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hzm : z = p.getVert m := by
      have hjm : m ≤ p.length := le_trans hmle hjle
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hjm]
    have hzi : z i ≤ t := by rw [hzm]; exact hcoord m hmle
    exact hslab z hzS hzi
  
  have hxT : x ∈ T := hqsupp x q.start_mem_support
  have huT : u ∈ T := hqsupp u q.end_mem_support
  refine ⟨u, huS, hju, huT, hxT, ?_⟩
  exact ⟨q.induce T hqsupp⟩








theorem bxa_horizontalCrossing_mono_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a')
    {ω : ConfigSpace (Sym2 (Site 2))} (h : HorizontalCrossing ω 0 a' 0 b) :
    HorizontalCrossing ω 0 a 0 b := by
  obtain ⟨xl, yr, hconn⟩ := h
  
  have hxl0 : (xl : Site 2) 0 = 0 := xl.2.2
  have hyr0 : (yr : Site 2) 0 = a' := yr.2.2
  have hxlS : (xl : Site 2) ∈ rect 0 a' 0 b := leftSide_subset xl.2
  have hyrS : (yr : Site 2) ∈ rect 0 a' 0 b := rightSide_subset yr.2
  
  obtain ⟨u, _, hu0, huT, hxT, hconn'⟩ :=
    bxa_connectedWithin_restrict hxlS hyrS hconn 0 a (by rw [hxl0]; exact ha)
      (by rw [hyr0]; exact haa')
      (fun z hz hzle => by
        rw [mem_rect] at hz ⊢
        exact ⟨hz.1, hzle, hz.2.2.1, hz.2.2.2⟩)
  
  refine ⟨⟨(xl : Site 2), ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hxT, hxl0⟩
  · exact ⟨huT, hu0⟩
  · exact hconn'






theorem bxa_verticalCrossing_mono_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d')
    {ω : ConfigSpace (Sym2 (Site 2))} (h : VerticalCrossing ω 0 a 0 d') :
    VerticalCrossing ω 0 a 0 d := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxb1 : (xb : Site 2) 1 = 0 := xb.2.2
  have hyt1 : (yt : Site 2) 1 = d' := yt.2.2
  have hxbS : (xb : Site 2) ∈ rect 0 a 0 d' := bottomSide_subset xb.2
  have hytS : (yt : Site 2) ∈ rect 0 a 0 d' := topSide_subset yt.2
  obtain ⟨u, _, hu1, huT, hxT, hconn'⟩ :=
    bxa_connectedWithin_restrict hxbS hytS hconn 1 d (by rw [hxb1]; exact hd)
      (by rw [hyt1]; exact hdd')
      (fun z hz hzle => by
        rw [mem_rect] at hz ⊢
        exact ⟨hz.1, hz.2.1, hz.2.2.1, hzle⟩)
  refine ⟨⟨(xb : Site 2), ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hxT, hxb1⟩
  · exact ⟨huT, hu1⟩
  · exact hconn'



theorem bxa_horizontalCrossingEvent_subset_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a') :
    horizontalCrossingEvent 0 a' 0 b ⊆ horizontalCrossingEvent 0 a 0 b :=
  fun _ hω => bxa_horizontalCrossing_mono_width ha haa' hω



theorem bxa_verticalCrossingEvent_subset_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d') :
    verticalCrossingEvent 0 a 0 d' ⊆ verticalCrossingEvent 0 a 0 d :=
  fun _ hω => bxa_verticalCrossing_mono_height hd hdd' hω



theorem bxa_horizontalCrossing_real_mono_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a') :
    rba_selfDualMeasure.real (horizontalCrossingEvent 0 a' 0 b)
      ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 a 0 b) :=
  measureReal_mono (bxa_horizontalCrossingEvent_subset_width ha haa')



theorem bxa_verticalCrossing_real_mono_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d') :
    rba_selfDualMeasure.real (verticalCrossingEvent 0 a 0 d')
      ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 a 0 d) :=
  measureReal_mono (bxa_verticalCrossingEvent_subset_height hd hdd')





theorem bxa_floor_le_natMul {ρ : ℝ} {k0 : ℕ} (hρk0 : ρ ≤ (k0 : ℝ)) (n : ℕ) :
    ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := by
  have hmul : ρ * (n : ℝ) ≤ (k0 : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hρk0 (by positivity)
  calc ⌊ρ * (n : ℝ)⌋ ≤ ⌊(k0 : ℝ) * (n : ℝ)⌋ := Int.floor_le_floor hmul
    _ = (k0 : ℤ) * (n : ℤ) := bxr_floor_natMul k0 n



theorem bxa_zero_lt_floor {ρ : ℝ} (hρ : 1 < ρ) {n : ℕ} (hn : 1 ≤ n) :
    (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ ρ * (n : ℝ) := by nlinarith [le_of_lt hρ]
  have : (1 : ℤ) ≤ ⌊ρ * (n : ℝ)⌋ := by
    rw [Int.le_floor]; exact_mod_cast h1
  omega





























theorem bxa_boxCrossingProperty_all
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
  intro ρ hρ
  
  set k0 : ℕ := max 2 ⌈ρ⌉₊ with hk0_def
  have hk0 : 2 ≤ k0 := Nat.le_max_left 2 ⌈ρ⌉₊
  have hρk0 : ρ ≤ (k0 : ℝ) := by
    have h1 : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
    have h2 : (⌈ρ⌉₊ : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast Nat.le_max_right 2 ⌈ρ⌉₊
    linarith
  have hk1 : 1 ≤ k0 := le_trans (by norm_num) hk0
  
  set c : ℝ := β * ((1 / 2) * γ) ^ (k0 - 1) with hc_def
  have hc : (0 : ℝ) < c := by rw [hc_def]; positivity
  
  have hbase : ∀ n : ℤ, 0 < n →
      c ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) := by
    intro n hn
    have := rai_cross_lb rba_selfDualMeasure hpa hn hβ hγ (hseed n hn)
      (cti_h2box_discharge (hmeas2box n hn) (h2box n hn))
      (cti_hband_discharge (hmeasband n hn) (hband n hn)) k0 hk1
    rwa [rai_cross_def] at this
  
  refine rba_bxp_of_uniform_seed rba_selfDualMeasure ρ hρ 1 c hc ?_ ?_
  · 
    intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfloor_pos : (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := bxa_zero_lt_floor hρ hn1
    have hfloor_le : ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := bxa_floor_le_natMul hρk0 n
    
    rw [bxr_translatedHorizontalCrossing_invariant τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)
        (hmeasGenH ⌊ρ * (n : ℝ)⌋ (n : ℤ) hfloor_pos hn)]
    
    calc c ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
          hbase (n : ℤ) hn
      _ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 ⌊ρ * (n : ℝ)⌋ 0 (n : ℤ)) :=
          bxa_horizontalCrossing_real_mono_width hfloor_pos hfloor_le
  · 
    intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfloor_pos : (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := bxa_zero_lt_floor hρ hn1
    have hfloor_le : ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := bxa_floor_le_natMul hρk0 n
    rw [bxr_translatedVerticalCrossing_invariant τ (n : ℤ) ⌊ρ * (n : ℝ)⌋
        (hmeasGenV (n : ℤ) ⌊ρ * (n : ℝ)⌋ hn hfloor_pos)]
    
    calc c ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
          hbase (n : ℤ) hn
      _ = rba_selfDualMeasure.real (verticalCrossingEvent 0 (n : ℤ) 0 ((k0 : ℤ) * n)) :=
          (hrefl k0 hk0 (n : ℤ) hn).symm
      _ ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 (n : ℤ) 0 ⌊ρ * (n : ℝ)⌋) :=
          bxa_verticalCrossing_real_mono_height hfloor_pos hfloor_le

end Universality

end StatMech
