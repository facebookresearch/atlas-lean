/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.Percolation.DctSurfacePartition
import Code.Percolation.SurfaceReassembly
import Code.Percolation.Sharpness

open MeasureTheory Function Set SimpleGraph Filter
open scoped NNReal ENNReal Topology
open StatMech

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}














theorem isPivotal_box_congr_erase (n : ℕ) (e : Sym2 (Site d))
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e' ∈ (((boxEdgeFinset d n).erase e : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))),
        ω e' = ω' e') :
    IsPivotal e (boxCrossingEvent d n) ω ↔ IsPivotal e (boxCrossingEvent d n) ω' := by
  classical
  set ω'' : ConfigSpace (Sym2 (Site d)) := Function.update ω e (ω' e) with hω''
  
  have hagree1 : ∀ e', e' ≠ e → ω e' = ω'' e' := by
    intro e' he'; rw [hω'', Function.update_of_ne he']
  have hstep1 : IsPivotal e (boxCrossingEvent d n) ω ↔ IsPivotal e (boxCrossingEvent d n) ω'' :=
    isPivotal_congr hagree1
  
  have hagree2 : ∀ e' ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω'' e' = ω' e' := by
    intro e' he'
    by_cases hee : e' = e
    · subst hee; rw [hω'', Function.update_self]
    · rw [hω'', Function.update_of_ne hee]
      exact h e' (by rw [Finset.coe_erase]; exact ⟨he', hee⟩)
  have hdep := pivotalEvent_dependsOn (boxCrossingEvent d n) (boxEdgeFinset d n) e
    (boxCrossingEvent_dependsOn n)
  have hstep2 : IsPivotal e (boxCrossingEvent d n) ω'' ↔ IsPivotal e (boxCrossingEvent d n) ω' := by
    have := hdep hagree2
    by_cases hmem : ω'' ∈ pivotalEvent e (boxCrossingEvent d n)
    · have hmem' : ω' ∈ pivotalEvent e (boxCrossingEvent d n) := by
        by_contra hc
        rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hc] at this; norm_num at this
      exact ⟨fun _ => hmem', fun _ => hmem⟩
    · have hmem' : ω' ∉ pivotalEvent e (boxCrossingEvent d n) := by
        intro hc
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_mem hc] at this; norm_num at this
      exact ⟨fun hc => absurd hc hmem, fun hc => absurd hc hmem'⟩
  exact hstep1.trans hstep2


theorem pivotalEvent_dependsOn_erase (n : ℕ) (e : Sym2 (Site d)) :
    DependsOn ((pivotalEvent e (boxCrossingEvent d n)).indicator (fun _ => (1 : ℝ)))
      (((boxEdgeFinset d n).erase e : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hpiv := isPivotal_box_congr_erase n e h
  by_cases hmem : ω ∈ pivotalEvent e (boxCrossingEvent d n)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hpiv.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hpiv.mpr hc))]


theorem coord_false_dependsOn {E : Type*} (e : E) :
    DependsOn (({ω : ConfigSpace E | ω e = false}).indicator (fun _ => (1 : ℝ)))
      ({e} : Set E) := by
  intro ω ω' h
  have he : ω e = ω' e := h e rfl
  by_cases hmem : ω ∈ {ω : ConfigSpace E | ω e = false}
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (by simp only [Set.mem_setOf_eq, ← he]; exact hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, ← he]; exact hmem)]



theorem coord_false_prob (p : ℝ≥0) (hp : p ≤ 1) (e : Sym2 (Site d)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | ω e = false}
      = 1 - (p : ℝ) := by
  classical
  have hcompl : {ω : ConfigSpace (Sym2 (Site d)) | ω e = false}
      = {ω : ConfigSpace (Sym2 (Site d)) | ω e = true}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Bool.not_eq_true]
  have hmeas : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
    refine measurableSet_of_dependsOn (F := ({e} : Finset (Sym2 (Site d)))) ?_
    simpa using coord_true_dependsOn (E := Sym2 (Site d)) e
  rw [hcompl, measureReal_compl hmeas, probReal_univ, coord_true_prob p hp]









theorem pivotalProb_closed_factor (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (e : Sym2 (Site d)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (pivotalEvent e (boxCrossingEvent d n) ∩ {ω | ω e = false})
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (pivotalEvent e (boxCrossingEvent d n)) * (1 - (p : ℝ)) := by
  classical
  have hdisj : Disjoint ((boxEdgeFinset d n).erase e) ({e} : Finset (Sym2 (Site d))) := by
    rw [Finset.disjoint_singleton_right]; exact Finset.notMem_erase e _
  rw [indep_cylinder_inf p hp _ _ ((boxEdgeFinset d n).erase e) ({e} : Finset (Sym2 (Site d)))
      hdisj (pivotalEvent_dependsOn_erase n e)
      (by simpa using coord_false_dependsOn (E := Sym2 (Site d)) e),
    coord_false_prob p hp]












theorem surfaceSet_subset_innerBox (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    (surfaceSet d n ω : Set (Site d)) ⊆ box d (n - 1) := by
  intro x hx
  rw [Finset.mem_coe, mem_surfaceSet] at hx
  obtain ⟨hxbox, hnc⟩ := hx
  by_contra hxnotinner
  exact hnc (connBdry_of_mem_boundary hxbox ⟨hxbox, hxnotinner⟩)






theorem connectedWithin_mono_set' (ω : ConfigSpace (Sym2 (Site d)))
    {S T : Set (Site d)} (hST : S ⊆ T) {x y : S}
    (h : ConnectedWithin d ω S x y) :
    ConnectedWithin d ω T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
  let f : (openSubgraph d ω).induce S →g (openSubgraph d ω).induce T :=
    { toFun := fun z => ⟨(z : Site d), hST z.2⟩
      map_rel' := fun {a b} hab => hab }
  exact h.map f



theorem connectedWithin_box_mono_omega {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hle : ω ≤ ω') {x y : ↥(box d n)} (h : ConnectedWithin d ω (box d n) x y) :
    ConnectedWithin d ω' (box d n) x y := by
  refine h.mono ?_
  intro u v huv
  simp only [openSubgraphInduce_adj, openSubgraph_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  have := hle s((u : Site d), (v : Site d))
  rw [huv.2] at this
  exact le_antisymm (Bool.le_true _) this


theorem origin_mem_box' (n : ℕ) : origin d ∈ box d n := fun i => by simp [origin]














theorem surface_boundary_edge_closed {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y)
    (hxS : x ∈ S) (hybox : y ∈ box d n) (hyS : y ∉ S) :
    ω s(x, y) = false := by
  by_contra hne
  rw [Bool.not_eq_false] at hne
  have hxbox : x ∈ box d n := (mem_surfaceSet.mp (hS ▸ hxS)).1
  
  have hcby : connBdry d n ω y := by
    by_contra hnc
    exact hyS (hS ▸ (mem_surfaceSet.mpr ⟨hybox, hnc⟩))
  
  have hopen : IsOpenEdge d ω x y := ⟨hadj, hne⟩
  exact (mem_surfaceSet.mp (hS ▸ hxS)).2 (connBdry_of_open_edge hxbox hybox hopen hcby)




theorem mem_boxCrossingEvent_iff_connBdry (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    ω ∈ boxCrossingEvent d n ↔ connBdry d n ω (origin d) := by
  rw [mem_boxCrossingEvent]
  constructor
  · rintro ⟨x, hx, hxb, h0, hconn⟩; exact ⟨h0, x, hx, hxb, hconn⟩
  · rintro ⟨h0, y, hy, hyb, hconn⟩; exact ⟨y, hy, hyb, h0, hconn⟩











theorem boundary_edge_isPivotal {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S) (h0S : origin d ∈ S)
    {x y : Site d} (hadj : (hypercubicLattice d).Adj x y)
    (hxS : x ∈ S) (hybox : y ∈ box d n) (hyS : y ∉ S)
    (hconn : ConnectedWithin d ω (S : Set (Site d))
      ⟨origin d, by exact_mod_cast h0S⟩ ⟨x, by exact_mod_cast hxS⟩) :
    IsPivotal (s(x, y) : Sym2 (Site d)) (boxCrossingEvent d n) ω := by
  classical
  set e : Sym2 (Site d) := s(x, y) with he
  have hxbox : x ∈ box d n := (mem_surfaceSet.mp (hS ▸ hxS)).1
  have hclosed : ω e = false := surface_boundary_edge_closed hS hadj hxS hybox hyS
  
  have hsetClosed : setClosed e ω = ω := by
    rw [setClosed]; exact Function.update_eq_self_iff.mpr hclosed.symm
  have h0notconn : ¬ connBdry d n ω (origin d) := by
    intro hc; exact (mem_surfaceSet.mp (hS ▸ h0S)).2 hc
  have hclosed_notin : setClosed e ω ∉ boxCrossingEvent d n := by
    rw [hsetClosed, mem_boxCrossingEvent_iff_connBdry]; exact h0notconn
  
  have hle : ω ≤ setOpen e ω := by
    intro j
    by_cases hje : j = e
    · subst hje; simp [setOpen]
    · rw [setOpen_of_ne hje]
  
  have hSbox : (S : Set (Site d)) ⊆ box d n := by
    intro z hz; exact (mem_surfaceSet.mp (hS ▸ (by exact_mod_cast hz : z ∈ S))).1
  have hconn_box_omega : ConnectedWithin d ω (box d n)
      ⟨origin d, by exact_mod_cast hSbox (by exact_mod_cast h0S)⟩
      ⟨x, hxbox⟩ := by
    have := connectedWithin_mono_set' ω hSbox hconn
    convert this using 2
  have hconn0x : ConnectedWithin d (setOpen e ω) (box d n)
      ⟨origin d, origin_mem_box' n⟩ ⟨x, hxbox⟩ :=
    connectedWithin_box_mono_omega hle hconn_box_omega
  
  have hxy_open : IsOpenEdge d (setOpen e ω) x y := ⟨hadj, by rw [he, setOpen_self]⟩
  have hadj_box : (openSubgraphInduce d (setOpen e ω) (box d n)).Adj ⟨x, hxbox⟩ ⟨y, hybox⟩ := by
    simp only [openSubgraphInduce_adj, openSubgraph_adj]; exact hxy_open
  have hconnxy : ConnectedWithin d (setOpen e ω) (box d n) ⟨x, hxbox⟩ ⟨y, hybox⟩ :=
    SimpleGraph.Adj.reachable hadj_box
  
  have hcby : connBdry d n ω y := by
    by_contra hnc
    exact hyS (hS ▸ (mem_surfaceSet.mpr ⟨hybox, hnc⟩))
  obtain ⟨_, z, hz, hzb, hyz⟩ := hcby
  have hyz' : ConnectedWithin d (setOpen e ω) (box d n) ⟨y, hybox⟩ ⟨z, hz⟩ :=
    connectedWithin_box_mono_omega hle hyz
  
  have hchain : ConnectedWithin d (setOpen e ω) (box d n)
      ⟨origin d, origin_mem_box' n⟩ ⟨z, hz⟩ :=
    (hconn0x.trans hconnxy).trans hyz'
  have hopen_in : setOpen e ω ∈ boxCrossingEvent d n :=
    ⟨z, hz, hzb, origin_mem_box' n, hchain⟩
  
  exact (isPivotal_iff_of_isIncreasing (boxCrossingEvent_isIncreasing n) ω).mpr
    ⟨hclosed_notin, hopen_in⟩








theorem boundaryEdges_adj {S : Finset (Site d)} {e : Site d × Site d}
    (he : e ∈ boundaryEdges d S) : (hypercubicLattice d).Adj e.1 e.2 := by
  obtain ⟨i, b, _, _, h2⟩ := boundaryEdges_outer he
  rw [h2]
  rw [hypercubicLattice_adj, Finset.sum_eq_single i]
  · simp only [coordShift, Function.update_self, stepSign]; cases b <;> simp
  · intro j _ hj; rw [coordShift, Function.update_of_ne hj, sub_self, Int.natAbs_zero]
  · intro h; exact absurd (Finset.mem_univ i) h




theorem boundaryEdge_mem_boxEdgeFinset {n : ℕ} {S : Finset (Site d)}
    (hSinner : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n)
    {e : Site d × Site d} (he : e ∈ boundaryEdges d S) :
    s(e.1, e.2) ∈ boxEdgeFinset d n := by
  obtain ⟨i, b, h1S, _, _⟩ := boundaryEdges_outer he
  have h1box : e.1 ∈ box d n := box_mono d (by omega) (hSinner (by exact_mod_cast h1S))
  have h2box : e.2 ∈ box d n := boundaryEdges_snd_mem_box hn hSinner he
  exact mem_boxEdgeFinset.mpr ⟨e.1, e.2, h1box, h2box, rfl⟩



theorem boundaryEdges_sym2_injOn (S : Finset (Site d)) :
    Set.InjOn (fun e : Site d × Site d => (s(e.1, e.2) : Sym2 (Site d)))
      (boundaryEdges d S : Set (Site d × Site d)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  obtain ⟨_, _, ha1, ha2, _⟩ := boundaryEdges_outer ha
  obtain ⟨_, _, hb1, hb2, _⟩ := boundaryEdges_outer hb
  simp only at hab
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · 
    exact absurd (h1 ▸ ha1) hb2



theorem sum_le_sum_injOn {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (φ : α → β) (g : α → ℝ) (f : β → ℝ)
    (hmap : ∀ a ∈ s, φ a ∈ t) (hinj : Set.InjOn φ s)
    (hle : ∀ a ∈ s, g a ≤ f (φ a)) (hf : ∀ b ∈ t, 0 ≤ f b) :
    ∑ a ∈ s, g a ≤ ∑ b ∈ t, f b := by
  calc ∑ a ∈ s, g a ≤ ∑ a ∈ s, f (φ a) := Finset.sum_le_sum hle
    _ = ∑ b ∈ s.image φ, f b := by rw [Finset.sum_image (fun a ha b hb => hinj ha hb)]
    _ ≤ ∑ b ∈ t, f b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb; rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb; exact hmap a ha
        · intro b hb _; exact hf b hb



theorem withinConn_surf_subset_pivotalClosed {n : ℕ} {S : Finset (Site d)}
    (h0S : origin d ∈ S) (hSinner : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n)
    {e : Site d × Site d} (he : e ∈ boundaryEdges d S) :
    withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ surfaceEvent d n S
      ⊆ (pivotalEvent (s(e.1, e.2)) (boxCrossingEvent d n) ∩ {ω | ω s(e.1, e.2) = false})
        ∩ surfaceEvent d n S := by
  obtain ⟨i, b, h1S, h2S, _⟩ := boundaryEdges_outer he
  have hadj : (hypercubicLattice d).Adj e.1 e.2 := boundaryEdges_adj he
  have h2box : e.2 ∈ box d n := boundaryEdges_snd_mem_box hn hSinner he
  intro ω hω
  obtain ⟨hwc, hsurf⟩ := hω
  have hS : surfaceSet d n ω = S := hsurf
  obtain ⟨ho, hx, hconn⟩ := hwc
  refine ⟨⟨?_, ?_⟩, hsurf⟩
  · 
    show IsPivotal (s(e.1, e.2)) (boxCrossingEvent d n) ω
    exact boundary_edge_isPivotal hS h0S hadj h1S h2box h2S hconn
  · 
    show ω s(e.1, e.2) = false
    exact surface_boundary_edge_closed hS hadj h1S h2box h2S






theorem perSurface_boundary_le_pivotal (p : ℝ≥0) (hp : p ≤ 1) {n : ℕ} {S : Finset (Site d)}
    (h0S : origin d ∈ S) (hSinner : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n) :
    ∑ e' ∈ boundaryEdges d S,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S)
      ≤ ∑ edge ∈ boxEdgeFinset d n,
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            ((pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
              ∩ surfaceEvent d n S) := by
  refine sum_le_sum_injOn (boundaryEdges d S) (boxEdgeFinset d n)
    (fun e' => s(e'.1, e'.2))
    (fun e' => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S))
    (fun edge => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
          ∩ surfaceEvent d n S))
    (fun e' he' => boundaryEdge_mem_boxEdgeFinset hSinner hn he')
    (boundaryEdges_sym2_injOn S)
    (fun e' he' => measureReal_mono (withinConn_surf_subset_pivotalClosed h0S hSinner hn he')
      (measure_ne_top _ _))
    (fun edge _ => measureReal_nonneg)







theorem perSurface_boundary_eq_phi (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < (p : ℝ))
    {n : ℕ} {S : Finset (Site d)} (h0S : origin d ∈ S) :
    ∑ e' ∈ boundaryEdges d S,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S)
      = (1 / (p : ℝ)) * (phi d p hp S
          * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S)) := by
  have hre := phi_reassembly p hp S h0S (surfaceEvent d n S) (boxEdgesOutside d n S)
    (disjoint_boxEdgesOutside n S) (surfaceEvent_dependsOn_outside n S)
  rw [← hre]
  field_simp




theorem measurableSet_pivotalClosed (n : ℕ) (edge : Sym2 (Site d)) :
    MeasurableSet (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}) := by
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_of_dependsOn (F := boxEdgeFinset d n)
      (pivotalEvent_dependsOn (boxCrossingEvent d n) (boxEdgeFinset d n) edge
        (boxCrossingEvent_dependsOn n))
  · exact measurableSet_of_dependsOn (F := ({edge} : Finset (Sym2 (Site d))))
      (by simpa using coord_false_dependsOn (E := Sym2 (Site d)) edge)




theorem sum_inter_surface_le (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ)
    {E : Set (ConfigSpace (Sym2 (Site d)))} (hE : MeasurableSet E) :
    ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (E ∩ surfaceEvent d n S)
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real E := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  have hdisj : ((boxFinset d n).powerset.filter (fun S => origin d ∈ S)
      : Set (Finset (Site d))).PairwiseDisjoint (fun S => E ∩ surfaceEvent d n S) := by
    intro S _ S' _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, hωS⟩ ⟨_, hωS'⟩
    exact hne (by rw [← (hωS : surfaceSet d n ω = S), ← (hωS' : surfaceSet d n ω = S')])
  have hmeas : ∀ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S),
      MeasurableSet (E ∩ surfaceEvent d n S) :=
    fun S _ => hE.inter (measurableSet_surfaceEvent n S)
  rw [← measureReal_biUnion_finset hdisj hmeas]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_iUnion₂] at hω
  obtain ⟨S, _, hωE, _⟩ := hω
  exact hωE






theorem biUnion_surface_not_origin (n : ℕ) :
    (⋃ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∉ S), surfaceEvent d n S)
      = boxCrossingEvent d n := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨S, ⟨_, h0S⟩, hωS⟩
    have hS : surfaceSet d n ω = S := hωS
    rw [mem_boxCrossingEvent_iff_connBdry]
    by_contra hnc
    exact h0S (hS ▸ (mem_surfaceSet.mpr ⟨origin_mem_box' n, hnc⟩))
  · intro hω
    refine ⟨surfaceSet d n ω, ⟨surfaceSet_subset_box n ω, ?_⟩, rfl⟩
    rw [mem_surfaceSet]
    rintro ⟨_, hnc⟩
    rw [mem_boxCrossingEvent_iff_connBdry] at hω
    exact hnc hω



theorem sum_surfaceProb_origin (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S)
      = 1 - boxCrossProb d p hp n := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  
  have hnotorigin : ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∉ S),
      μ.real (surfaceEvent d n S) = boxCrossProb d p hp n := by
    have hdisj : ((boxFinset d n).powerset.filter (fun S => origin d ∉ S)
        : Set (Finset (Site d))).PairwiseDisjoint (surfaceEvent d n) := by
      intro S _ S' _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω hωS hωS'
      exact hne (by rw [← (hωS : surfaceSet d n ω = S), ← (hωS' : surfaceSet d n ω = S')])
    have hmeas : ∀ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∉ S),
        MeasurableSet (surfaceEvent d n S) := fun S _ => measurableSet_surfaceEvent n S
    rw [measureReal_biUnion_finset hdisj hmeas |>.symm, biUnion_surface_not_origin n]
    rfl
  
  have hsplit : ∑ S ∈ (boxFinset d n).powerset, μ.real (surfaceEvent d n S)
      = (∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∈ S),
          μ.real (surfaceEvent d n S))
        + ∑ S ∈ (boxFinset d n).powerset.filter (fun S => origin d ∉ S),
          μ.real (surfaceEvent d n S) := by
    rw [← Finset.sum_filter_add_sum_filter_not (boxFinset d n).powerset
      (fun S => origin d ∈ S)]
  have hfull : ∑ S ∈ (boxFinset d n).powerset, μ.real (surfaceEvent d n S) = 1 :=
    sum_surfaceProb p hp n
  rw [hfull] at hsplit
  rw [hnotorigin] at hsplit
  linarith [hsplit]







theorem sum_pivotalClosed_eq (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    ∑ edge ∈ boxEdgeFinset d n,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
      = (1 - (p : ℝ)) * deriv (fun q =>
          prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ) := by
  rw [deriv_boxCrossProb_inf p hp n, Finset.mul_sum,
      ← Finset.sum_coe_sort (boxEdgeFinset d n)
        (fun edge => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}))]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [pivotalProb_closed_factor p hp n (↑e : Sym2 (Site d))]; ring




















theorem dct_differential_inequality (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℝ)
    (hm : ∀ S : Finset (Site d), origin d ∈ S → m ≤ phi d p hp S) :
    deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ)
      ≥ (1 / ((p : ℝ) * (1 - (p : ℝ)))) * m * (1 - boxCrossProb d p hp n) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  set D := deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) (p : ℝ)
    with hD
  have h1mp : (0 : ℝ) < 1 - (p : ℝ) := by linarith
  set P := (boxFinset d n).powerset.filter (fun S => origin d ∈ S) with hP
  
  
  set M : ℝ := ∑ S ∈ P, ∑ edge ∈ boxEdgeFinset d n,
      μ.real ((pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
        ∩ surfaceEvent d n S) with hM
  
  have hupper : M ≤ ∑ edge ∈ boxEdgeFinset d n,
      μ.real (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}) := by
    rw [hM, Finset.sum_comm]
    refine Finset.sum_le_sum (fun edge _ => ?_)
    exact sum_inter_surface_le p hp n (measurableSet_pivotalClosed n edge)
  
  have hlowerM : ∑ S ∈ P, ∑ e' ∈ boundaryEdges d S,
      μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S) ≤ M := by
    rw [hM]
    refine Finset.sum_le_sum (fun S hS => ?_)
    obtain ⟨hSpow, h0S⟩ := Finset.mem_filter.mp (by rw [← hP]; exact hS)
    have hSbox : (S : Set (Site d)) ⊆ box d n := by
      intro z hz; exact mem_boxFinset.mp (Finset.mem_powerset.mp hSpow (by exact_mod_cast hz))
    
    
    
    by_cases hSinner : (S : Set (Site d)) ⊆ box d (n - 1)
    · exact perSurface_boundary_le_pivotal p hp h0S hSinner hn
    · 
      have hempty : surfaceEvent d n S = ∅ := by
        ext ω; simp only [Set.mem_empty_iff_false, iff_false]
        intro hωS
        have hS' : surfaceSet d n ω = S := hωS
        exact hSinner (hS' ▸ surfaceSet_subset_innerBox n ω)
      have hzero : ∑ e' ∈ boundaryEdges d S,
          μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S)
            = 0 := by
        refine Finset.sum_eq_zero (fun e' _ => ?_)
        rw [hempty, Set.inter_empty, measureReal_empty]
      rw [hzero]
      refine Finset.sum_nonneg (fun edge _ => measureReal_nonneg)
  
  have hphi : ∑ S ∈ P, ∑ e' ∈ boundaryEdges d S,
      μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1 ∩ surfaceEvent d n S)
      = ∑ S ∈ P, (1 / (p : ℝ)) * (phi d p hp S * μ.real (surfaceEvent d n S)) := by
    refine Finset.sum_congr rfl (fun S hS => ?_)
    obtain ⟨_, h0S⟩ := Finset.mem_filter.mp (by rw [← hP]; exact hS)
    exact perSurface_boundary_eq_phi p hp hp0 h0S
  have hphi_ge : ∑ S ∈ P, (1 / (p : ℝ)) * (phi d p hp S * μ.real (surfaceEvent d n S))
      ≥ ∑ S ∈ P, (1 / (p : ℝ)) * (m * μ.real (surfaceEvent d n S)) := by
    refine Finset.sum_le_sum (fun S hS => ?_)
    obtain ⟨_, h0S⟩ := Finset.mem_filter.mp (by rw [← hP]; exact hS)
    have hsurfnn : 0 ≤ μ.real (surfaceEvent d n S) := measureReal_nonneg
    have hinvp : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have : m * μ.real (surfaceEvent d n S) ≤ phi d p hp S * μ.real (surfaceEvent d n S) :=
      mul_le_mul_of_nonneg_right (hm S h0S) hsurfnn
    exact mul_le_mul_of_nonneg_left this hinvp
  
  have hmsum : ∑ S ∈ P, (1 / (p : ℝ)) * (m * μ.real (surfaceEvent d n S))
      = (1 / (p : ℝ)) * (m * (1 - boxCrossProb d p hp n)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    congr 1
    exact sum_surfaceProb_origin p hp n
  
  have hpivcl_ge : ∑ edge ∈ boxEdgeFinset d n,
      μ.real (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
      ≥ (1 / (p : ℝ)) * (m * (1 - boxCrossProb d p hp n)) := by
    calc ∑ edge ∈ boxEdgeFinset d n,
            μ.real (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false})
        ≥ M := hupper
      _ ≥ ∑ S ∈ P, ∑ e' ∈ boundaryEdges d S,
            μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e'.1
              ∩ surfaceEvent d n S) := hlowerM
      _ = ∑ S ∈ P, (1 / (p : ℝ)) * (phi d p hp S * μ.real (surfaceEvent d n S)) := hphi
      _ ≥ ∑ S ∈ P, (1 / (p : ℝ)) * (m * μ.real (surfaceEvent d n S)) := hphi_ge
      _ = (1 / (p : ℝ)) * (m * (1 - boxCrossProb d p hp n)) := hmsum
  
  have hDeq : (∑ edge ∈ boxEdgeFinset d n,
      μ.real (pivotalEvent edge (boxCrossingEvent d n) ∩ {ω | ω edge = false}))
      = (1 - (p : ℝ)) * D := sum_pivotalClosed_eq p hp n
  rw [hDeq] at hpivcl_ge
  
  
  have hgoal : (1 / ((p : ℝ) * (1 - (p : ℝ)))) * m * (1 - boxCrossProb d p hp n) ≤ D := by
    have hkey : (1 / (p : ℝ)) * (m * (1 - boxCrossProb d p hp n)) ≤ (1 - (p : ℝ)) * D :=
      hpivcl_ge
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have h1mpne : (1 - (p : ℝ)) ≠ 0 := ne_of_gt h1mp
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hexp : (1 / (p : ℝ)) * (m * (1 - boxCrossProb d p hp n))
        = (m * (1 - boxCrossProb d p hp n)) / (p : ℝ) := by ring
    rw [hexp, div_le_iff₀ hp0] at hkey
    nlinarith [hkey]
  rw [hD]; exact hgoal














theorem firstExit {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (S : Set V)
    [DecidablePred (· ∈ S)] (ha : a ∈ S) (hb : b ∉ S) :
    ∃ (x y : V) (hx : x ∈ S) (_hy : y ∉ S) (_hadj : G.Adj x y),
      Nonempty ((G.induce S).Walk ⟨a, ha⟩ ⟨x, hx⟩) := by
  classical
  set Q : ℕ → Prop := fun m => m ≤ p.length ∧ p.getVert m ∉ S with hQ
  have hQex : ∃ m, Q m := ⟨p.length, le_refl _, by rwa [Walk.getVert_length]⟩
  set m := Nat.find hQex with hm
  obtain ⟨hmle, hmS⟩ : Q m := Nat.find_spec hQex
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, Walk.getVert_zero] at hmS; exact hmS ha
  have hprefix : ∀ k, k ≤ m - 1 → p.getVert k ∈ S := by
    intro k hk
    by_contra hkS
    have hQk : Q k := ⟨by omega, hkS⟩
    have hle : Nat.find hQex ≤ k := Nat.find_le hQk
    rw [← hm] at hle; omega
  have hm1S : p.getVert (m - 1) ∈ S := hprefix (m - 1) (le_refl _)
  have hadj : G.Adj (p.getVert (m - 1)) (p.getVert m) := by
    have := p.adj_getVert_succ (i := m - 1) (by omega)
    rwa [show m - 1 + 1 = m from by omega] at this
  set q := p.take (m - 1) with hq
  have hqsupp : ∀ z ∈ q.support, z ∈ S := by
    intro z hz
    rw [Walk.mem_support_iff_exists_getVert] at hz
    obtain ⟨k, hk, _⟩ := hz
    rw [hq, Walk.take_getVert] at hk
    rw [← hk]; exact hprefix _ (min_le_left _ _)
  refine ⟨p.getVert (m - 1), p.getVert m, hm1S, hmS, hadj, ⟨?_⟩⟩
  exact (q.induce S hqsupp).copy rfl rfl





theorem crossingEvent_eq_boxCrossingEvent (n : ℕ) (hn : 1 ≤ n) :
    crossingEvent d n = boxCrossingEvent d n := by
  classical
  ext ω
  constructor
  · rintro ⟨v, hconn, hv⟩
    have h0in : origin d ∈ box d (n - 1) := origin_mem_box' (n - 1)
    obtain ⟨p⟩ := hconn
    obtain ⟨x, y, hx, hy, hadj, ⟨w⟩⟩ := firstExit p (box d (n - 1)) h0in hv
    have hxbox : x ∈ box d n := box_mono d (by omega) hx
    have hopen : IsOpenEdge d ω x y := hadj
    have hybox : y ∈ box d n := by
      have := adj_box_step (m := n - 1) hx hadj.1
      rwa [show n - 1 + 1 = n from by omega] at this
    have hyb : y ∈ vertexBoundary d n := ⟨hybox, hy⟩
    have hconn0x : ConnectedWithin d ω (box d n)
        ⟨origin d, box_mono d (by omega) h0in⟩ ⟨x, hxbox⟩ :=
      connectedWithin_mono_set' ω (box_mono d (by omega))
        (x := ⟨origin d, h0in⟩) (y := ⟨x, hx⟩) ⟨w⟩
    have hadjbox : (openSubgraphInduce d ω (box d n)).Adj ⟨x, hxbox⟩ ⟨y, hybox⟩ := by
      simp only [openSubgraphInduce_adj, openSubgraph_adj]; exact hopen
    exact ⟨y, hybox, hyb, box_mono d (by omega) h0in,
      hconn0x.trans (SimpleGraph.Adj.reachable hadjbox)⟩
  · rintro ⟨x, hx, hxb, _, hconn⟩
    exact ⟨x, hconn.connected, hxb.2⟩



theorem crossProb_eq_boxCrossProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    crossProb d p hp n = boxCrossProb d p hp n := by
  unfold crossProb boxCrossProb
  rw [crossingEvent_eq_boxCrossingEvent n hn]











theorem crossProbReal_eq_prob (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    crossProbReal d (n + 1) t
      = prob t ((boxEdgeFinset d (n + 1)).restrict '' (boxCrossingEvent d (n + 1))) := by
  have hcr : crossProbReal d (n + 1) t
      = crossProb d t.toNNReal (Real.toNNReal_le_one.mpr ht1) (n + 1) := by
    unfold crossProbReal; rw [dif_pos ⟨ht0, ht1⟩]
  rw [hcr, crossProb_eq_boxCrossProb _ _ _ (by omega), boxCrossProb_eq_prob,
      Real.coe_toNNReal t ht0]



noncomputable def crossPoly (d n : ℕ) (t : ℝ) : ℝ :=
  prob t ((boxEdgeFinset d (n + 1)).restrict '' (boxCrossingEvent d (n + 1)))



theorem continuousOn_crossProbReal (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ContinuousOn (crossProbReal d (n + 1)) (Icc a b) := by
  refine ContinuousOn.congr (f := crossPoly d n) ?_ ?_
  · exact (differentiable_boxCrossProb (n + 1)).continuous.continuousOn
  · intro t ht
    exact crossProbReal_eq_prob n (le_trans ha ht.1) (le_trans ht.2 hb)



theorem hasDerivAt_crossProbReal (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (crossProbReal d (n + 1)) (deriv (crossPoly d n) t) t := by
  have hpoly : HasDerivAt (crossPoly d n) (deriv (crossPoly d n) t) t :=
    (differentiable_boxCrossProb (n + 1) t).hasDerivAt
  refine hpoly.congr_of_eventuallyEq ?_
  have hnhds : Ioo (0 : ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds ht0 ht1
  filter_upwards [hnhds] with s hs
  exact crossProbReal_eq_prob n (le_of_lt hs.1) (le_of_lt hs.2)



theorem phi_ge_one_of_gt_tildePc {p : ℝ≥0} (hp : p ≤ 1) (hgt : tildePc d < p)
    (S : Finset (Site d)) (h0S : origin d ∈ S) : 1 ≤ phi d p hp S := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : p ∈ tildePcSet d := ⟨hp, S, h0S, hlt⟩
  have hle : p ≤ tildePc d :=
    le_csSup ⟨1, fun q hq => (mem_tildePcSet.mp hq).1⟩ hmem
  exact absurd hle (not_le.mpr hgt)













theorem dct_diffineq_crossProbReal {q : ℝ≥0} (hq1 : (q : ℝ) < 1)
    (htpc0 : 0 < (tildePc d : ℝ)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (tildePc d : ℝ) (q : ℝ)) :
    deriv (crossPoly d n) t
      ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t) := by
  obtain ⟨htlo, hthi⟩ := ht
  have ht0 : 0 < t := lt_trans htpc0 htlo
  have ht1 : t < 1 := lt_trans hthi hq1
  set p : ℝ≥0 := t.toNNReal with hp_def
  have hp_le1 : p ≤ 1 := Real.toNNReal_le_one.mpr (le_of_lt ht1)
  have hpt : (p : ℝ) = t := Real.coe_toNNReal t (le_of_lt ht0)
  have hp0 : 0 < (p : ℝ) := by rw [hpt]; exact ht0
  have hpr1 : (p : ℝ) < 1 := by rw [hpt]; exact ht1
  
  have hp_gt : tildePc d < p := by
    rw [← NNReal.coe_lt_coe, hpt]; exact htlo
  
  have hm : ∀ S : Finset (Site d), origin d ∈ S → (1 : ℝ) ≤ phi d p hp_le1 S :=
    fun S h0S => phi_ge_one_of_gt_tildePc hp_le1 hp_gt S h0S
  have hdi := dct_differential_inequality p hp_le1 (n + 1) (by omega) hp0 hpr1 1 hm
  
  have hderiv_eq : deriv (crossPoly d n) t
      = deriv (fun q' => prob q' ((boxEdgeFinset d (n + 1)).restrict ''
          (boxCrossingEvent d (n + 1)))) (p : ℝ) := by
    rw [hpt]; rfl
  
  have hcross_eq : boxCrossProb d p hp_le1 (n + 1) = crossProbReal d (n + 1) t := by
    rw [crossProbReal_eq_prob n (le_of_lt ht0) (le_of_lt ht1), boxCrossProb_eq_prob, hpt]
  rw [hderiv_eq, ge_iff_le]
  
  rw [ge_iff_le, hcross_eq] at hdi
  calc (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)
      = (1 / ((p : ℝ) * (1 - (p : ℝ)))) * 1 * (1 - crossProbReal d (n + 1) t) := by
        rw [hpt]; ring
    _ ≤ deriv (fun q' => prob q' ((boxEdgeFinset d (n + 1)).restrict ''
          (boxCrossingEvent d (n + 1)))) (p : ℝ) := hdi










theorem theta_ge_meanField_unconditional (q : ℝ≥0) (hq : q ≤ 1)
    (htpc0 : 0 < (tildePc d : ℝ)) (hgt : tildePc d < q) (hq1 : (q : ℝ) < 1) :
    theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ))) := by
  have haq : (tildePc d : ℝ) < (q : ℝ) := by exact_mod_cast hgt
  exact theta_ge_meanField q hq (tildePc d : ℝ) htpc0 haq hq1
    (fun n t => deriv (crossPoly d n) t)
    (fun n => continuousOn_crossProbReal n (le_of_lt htpc0) (le_of_lt hq1))
    (fun n t ht => hasDerivAt_crossProbReal n (lt_trans htpc0 ht.1) (lt_trans ht.2 hq1))
    (fun n t ht => dct_diffineq_crossProbReal hq1 htpc0 n ht)

end Percolation

end StatMech
