/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Percolation.Theta
import Code.Percolation.PcNontrivial
import Code.Percolation.PcUpper
import Code.Lattice.PlanarTopology
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity

open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace Percolation

open StatMech.Lattice







theorem cylinder_all_closed {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) (F : Finset (Sym2 (Site d))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp)
      ((F : Set (Sym2 (Site d))).pi (fun _ => ({false} : Set Bool)))
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ F.card := by
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
    (s := F) (t := fun _ => ({false} : Set Bool)) (fun i _ => measurableSet_singleton _)
  rw [bernoulliProductMeasure, key]
  simp only [bernoulliMeasure_apply_false]
  rw [Finset.prod_const]











theorem sharedPrimalEdge_right' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a + 1, b] = s(![a + 1, b], ![a + 1, b + 1]) := by
  rw [sharedPrimalEdge_right]; rfl


theorem sharedPrimalEdge_left' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
  rw [sharedPrimalEdge_left]; rfl


theorem sharedPrimalEdge_top' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b + 1] = s(![a, b + 1], ![a + 1, b + 1]) := by
  rw [sharedPrimalEdge_top]; rfl


theorem sharedPrimalEdge_bottom' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b - 1] = s(![a, b], ![a + 1, b]) := by
  rw [sharedPrimalEdge_bottom]; rfl



theorem face_adj_dir {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    (g = ![f 0 + 1, f 1]) ∨ (g = ![f 0 - 1, f 1]) ∨
      (g = ![f 0, f 1 + 1]) ∨ (g = ![f 0, f 1 - 1]) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  by_cases h0 : f 0 = g 0
  · have hg1 : g 1 = f 1 + 1 ∨ g 1 = f 1 - 1 := by omega
    have hgform : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rcases hg1 with hh | hh
    · right; right; left; rw [hgform, ← h0, hh]
    · right; right; right; rw [hgform, ← h0, hh]
  · have h1 : f 1 = g 1 := by
      by_contra hne
      have : (f 0 - g 0).natAbs ≥ 1 := by omega
      have : (f 1 - g 1).natAbs ≥ 1 := by omega
      omega
    have hg0 : g 0 = f 0 + 1 ∨ g 0 = f 0 - 1 := by omega
    have hgform : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rcases hg0 with hh | hh
    · left; rw [hgform, ← h1, hh]
    · right; left; rw [hgform, ← h1, hh]





theorem sharedPrimalEdge_uncrossInj {f g f' g' : Site 2}
    (h : (hypercubicLattice 2).Adj f g) (h' : (hypercubicLattice 2).Adj f' g')
    (heq : sharedPrimalEdge f g = sharedPrimalEdge f' g') : s(f, g) = s(f', g') := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hf' : f' = ![f' 0, f' 1] := by funext i; fin_cases i <;> rfl
  rcases face_adj_dir h with hg | hg | hg | hg <;>
  rcases face_adj_dir h' with hg' | hg' | hg' | hg' <;>
    (rw [hf, hg] at heq; rw [hf', hg'] at heq;
     rw [hf, hg, hf', hg'];
     simp only [sharedPrimalEdge_right', sharedPrimalEdge_left', sharedPrimalEdge_top',
                sharedPrimalEdge_bottom', Sym2.eq_iff, site2_eq] at heq ⊢;
     omega)









noncomputable def primalEdgeFinset {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    Finset (Sym2 (Site 2)) :=
  (c.darts.map (fun D => sharedPrimalEdge D.fst D.snd)).toFinset



def closedCircuitEvent {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | ∀ D ∈ c.darts, ω (sharedPrimalEdge D.fst D.snd) = false}


theorem closedCircuitEvent_eq_pi {u v : Site 2} (c : (hypercubicLattice 2).Walk u v) :
    closedCircuitEvent c
      = ((primalEdgeFinset c : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))).pi
          (fun _ => ({false} : Set Bool)) := by
  ext ω
  simp only [closedCircuitEvent, primalEdgeFinset, Set.mem_setOf_eq, Set.mem_pi,
    List.coe_toFinset, List.mem_map, Set.mem_singleton_iff,
    forall_exists_index, and_imp]
  constructor
  · rintro h e D hD rfl; exact h D hD
  · intro h D hD; exact h _ D hD rfl



theorem measure_closedCircuitEvent (p : ℝ≥0) (hp : p ≤ 1) {u v : Site 2}
    (c : (hypercubicLattice 2).Walk u v) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c)
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ (primalEdgeFinset c).card := by
  rw [closedCircuitEvent_eq_pi, cylinder_all_closed]



theorem primalEdgeList_nodup {u : Site 2} (c : (hypercubicLattice 2).Walk u u)
    (hc : c.IsCycle) :
    (c.darts.map (fun D => sharedPrimalEdge D.fst D.snd)).Nodup := by
  have hed : c.edges.Nodup := hc.edges_nodup
  have hde : c.edges = c.darts.map (·.edge) := rfl
  have hdn : c.darts.Nodup := by rw [hde] at hed; exact hed.of_map _
  apply List.Nodup.map_on _ hdn
  intro D1 hD1 D2 hD2 heq
  have he : s(D1.fst, D1.snd) = s(D2.fst, D2.snd) :=
    sharedPrimalEdge_uncrossInj D1.adj D2.adj heq
  have hedm : (c.darts.map (·.edge)).Nodup := hde ▸ hed
  exact (List.inj_on_of_nodup_map hedm) hD1 hD2 he


theorem primalEdgeFinset_card_cycle {u : Site 2} (c : (hypercubicLattice 2).Walk u u)
    (hc : c.IsCycle) : (primalEdgeFinset c).card = c.length := by
  unfold primalEdgeFinset
  rw [List.toFinset_card_of_nodup (primalEdgeList_nodup c hc), List.length_map, c.length_darts]



theorem measure_closedCircuitEvent_cycle (p : ℝ≥0) (hp : p ≤ 1) {u : Site 2}
    (c : (hypercubicLattice 2).Walk u u) (hc : c.IsCycle) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedCircuitEvent c)
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ c.length := by
  rw [measure_closedCircuitEvent p hp c, primalEdgeFinset_card_cycle c hc]







noncomputable def anchorFinset (ℓ : ℕ) : Finset (Site 2) :=
  ((Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), 0] : Site 2))) ∪
  ((Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), -1] : Site 2)))


theorem anchorFinset_card (ℓ : ℕ) : (anchorFinset ℓ).card ≤ 2 * ℓ := by
  unfold anchorFinset
  calc ((((Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), 0] : Site 2))) ∪
        ((Finset.range ℓ).image (fun j : ℕ => (![ (j : ℤ), -1] : Site 2)))).card)
      ≤ _ := Finset.card_union_le _ _
    _ ≤ ℓ + ℓ := by
        apply Nat.add_le_add <;>
        · exact le_trans (Finset.card_image_le) (by rw [Finset.card_range])
    _ = 2 * ℓ := by ring

open Classical in


noncomputable def cyclesAtLen (ℓ : ℕ) :
    Finset (Σ u : Site 2, (hypercubicLattice 2).Walk u u) :=
  (anchorFinset ℓ).sigma
    (fun u => ((hypercubicLattice 2).finsetWalkLength ℓ u u).filter (·.IsCycle))

open Classical in


theorem cyclesAtLen_card (ℓ : ℕ) : (cyclesAtLen ℓ).card ≤ 2 * ℓ * 4 ^ ℓ := by
  unfold cyclesAtLen
  calc ((anchorFinset ℓ).sigma
          (fun u => ((hypercubicLattice 2).finsetWalkLength ℓ u u).filter (·.IsCycle))).card
      ≤ ((anchorFinset ℓ).sigma
          (fun u => (hypercubicLattice 2).finsetWalkLength ℓ u u)).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_sigma] at hx ⊢
        exact ⟨hx.1, Finset.filter_subset _ _ hx.2⟩
    _ ≤ (anchorFinset ℓ).card * (2 * 2) ^ ℓ := card_circuits_based_in_le_pow 2 _ ℓ
    _ ≤ (2 * ℓ) * 4 ^ ℓ := by
        apply Nat.mul_le_mul (anchorFinset_card ℓ); norm_num



open Classical in



theorem measure_cyclesAtLen_le (p : ℝ≥0) (hp : p ≤ 1) (ℓ : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
        (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2)
      ≤ (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ := by
  calc (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
          (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2)
      ≤ ∑ σ ∈ cyclesAtLen ℓ, (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
            (closedCircuitEvent σ.2) := measure_biUnion_finset_le _ _
    _ = ∑ _σ ∈ cyclesAtLen ℓ, ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        unfold cyclesAtLen at hσ
        rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hσ
        obtain ⟨_, hlen, hcyc⟩ := hσ
        rw [measure_closedCircuitEvent_cycle p hp σ.2 hcyc, hlen]
    _ = (cyclesAtLen ℓ).card * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ := by
        apply mul_le_mul' _ (le_refl _)
        exact_mod_cast cyclesAtLen_card ℓ




noncomputable def pcSummandTwo (p : ℝ) (ℓ : ℕ) : ℝ := (2 * ℓ * 4 ^ ℓ : ℕ) * ((1 - p) ^ ℓ)

theorem pcSummandTwo_eq (p : ℝ) (ℓ : ℕ) :
    pcSummandTwo p ℓ = 2 * ((ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ) := by
  unfold pcSummandTwo; push_cast; ring

theorem pcSummandTwo_nonneg {p : ℝ} (hp : p ≤ 1) (ℓ : ℕ) : 0 ≤ pcSummandTwo p ℓ := by
  unfold pcSummandTwo
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity


theorem summable_pcSummandTwo (p : ℝ) (hx : ‖pcRatio p‖ < 1) : Summable (pcSummandTwo p) := by
  have hbase : Summable (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ) := by
    have heq : (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (pcRatio p) ^ ℓ) := funext (pcSummand_eq p)
    rw [heq]
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hx
    simpa using this
  have h2 : Summable (fun ℓ : ℕ => 2 * ((ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)) := hbase.mul_left 2
  exact h2.congr (fun ℓ => (pcSummandTwo_eq p ℓ).symm)


theorem tsum_pcSummandTwo (p : ℝ) : ∑' ℓ : ℕ, pcSummandTwo p ℓ = 2 * pcUpperBound p := by
  unfold pcUpperBound
  rw [← tsum_mul_left]
  exact tsum_congr (fun ℓ => pcSummandTwo_eq p ℓ)


theorem ennSummand_eq_ofReal (p : ℝ≥0) (hp : p ≤ 1) (ℓ : ℕ) :
    ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ≥0∞) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ
      = ENNReal.ofReal (pcSummandTwo (p : ℝ) ℓ) := by
  have hpr : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hpow : ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ = ENNReal.ofReal ((1 - (p : ℝ)) ^ ℓ) := by
    rw [show ((1 - p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((1 - p : ℝ≥0) : ℝ) from
          (ENNReal.ofReal_coe_nnreal).symm]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [NNReal.coe_sub hp, NNReal.coe_one]
  unfold pcSummandTwo
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, hpow]


















def PcAnchoredEnclosure : Prop :=
  ∀ ω : ConfigSpace (Sym2 (Site 2)), (cluster 2 ω (origin 2)).Finite →
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧ u ∈ anchorFinset c.length


theorem mapLe_length (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) :
    (c.mapLe (faceBoundaryGraph_le S)).length = c.length :=
  Walk.length_map (Hom.ofLE (faceBoundaryGraph_le S)) c


theorem mapLe_edges (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) :
    (c.mapLe (faceBoundaryGraph_le S)).edges = c.edges := by
  show (c.map (Hom.ofLE (faceBoundaryGraph_le S))).edges = c.edges
  rw [SimpleGraph.Walk.edges_map]; simp [SimpleGraph.Hom.ofLE]


theorem mapLe_dart_faceAdj (S : Set (Site 2)) {u : Site 2}
    (c : (faceBoundaryGraph S).Walk u u) (D : (hypercubicLattice 2).Dart)
    (hD : D ∈ (c.mapLe (faceBoundaryGraph_le S)).darts) :
    (faceBoundaryGraph S).Adj D.fst D.snd := by
  have hedge : D.edge ∈ (c.mapLe (faceBoundaryGraph_le S)).edges := List.mem_map_of_mem hD
  rw [mapLe_edges S c] at hedge
  rw [show D.edge = s(D.fst, D.snd) from rfl] at hedge
  exact c.adj_of_mem_edges hedge




theorem sharedPrimalEdge_isClosed {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) {f g : Site 2}
    (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
    ω (sharedPrimalEdge f g) = false := by
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge h.1
  have hbd : bdEdge (cluster 2 ω o) (sharedPrimalEdge f g) := h.2
  rw [hpq, bdEdge_mk] at hbd
  have hpqbd : (p, q) ∈ edgeBoundary 2 (cluster 2 ω o) := ⟨hadj, hbd⟩
  rw [hpq]
  exact cluster_edgeBoundary_isClosed o hpqbd






theorem percolationEventCompl_subset (henc : PcAnchoredEnclosure) :
    (percolationEvent 2)ᶜ ⊆ ⋃ ℓ : ℕ, ⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2 := by
  classical
  intro ω hω
  
  rw [Set.mem_compl_iff, mem_percolationEvent, Set.not_infinite] at hω
  
  obtain ⟨u, c, hcyc, hu⟩ := henc ω hω
  
  set c' : (hypercubicLattice 2).Walk u u :=
    c.mapLe (faceBoundaryGraph_le (cluster 2 ω (origin 2))) with hc'
  have hc'cyc : c'.IsCycle :=
    Walk.IsCycle.mapLe (faceBoundaryGraph_le (cluster 2 ω (origin 2))) hcyc
  have hc'len : c'.length = c.length := mapLe_length (cluster 2 ω (origin 2)) c
  
  have hmem : ω ∈ closedCircuitEvent c' := by
    intro D hD
    have hadj : (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj D.fst D.snd :=
      mapLe_dart_faceAdj (cluster 2 ω (origin 2)) c D hD
    exact sharedPrimalEdge_isClosed (origin 2) hadj
  
  have hu' : u ∈ anchorFinset c'.length := by rw [hc'len]; exact hu
  
  refine Set.mem_iUnion.2 ⟨c'.length, ?_⟩
  refine Set.mem_iUnion.2 ⟨⟨u, c'⟩, ?_⟩
  refine Set.mem_iUnion.2 ⟨?_, hmem⟩
  unfold cyclesAtLen
  rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff]
  exact ⟨hu', rfl, hc'cyc⟩







theorem measure_compl_percolationEvent_le (henc : PcAnchoredEnclosure) (p : ℝ≥0) (hp : p ≤ 1)
    (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) ((percolationEvent 2)ᶜ)
      ≤ ENNReal.ofReal (2 * pcUpperBound (p : ℝ)) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp with hμ
  calc μ ((percolationEvent 2)ᶜ)
      ≤ μ (⋃ ℓ : ℕ, ⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2) :=
        measure_mono (percolationEventCompl_subset henc)
    _ ≤ ∑' ℓ : ℕ, μ (⋃ σ ∈ cyclesAtLen ℓ, closedCircuitEvent σ.2) := measure_iUnion_le _
    _ ≤ ∑' ℓ : ℕ, ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ≥0∞) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ :=
        ENNReal.tsum_le_tsum (fun ℓ => measure_cyclesAtLen_le p hp ℓ)
    _ = ∑' ℓ : ℕ, ENNReal.ofReal (pcSummandTwo (p : ℝ) ℓ) :=
        tsum_congr (fun ℓ => ennSummand_eq_ofReal p hp ℓ)
    _ = ENNReal.ofReal (∑' ℓ : ℕ, pcSummandTwo (p : ℝ) ℓ) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun ℓ => pcSummandTwo_nonneg (by exact_mod_cast hp) ℓ)
          (summable_pcSummandTwo (p : ℝ) hsum)).symm
    _ = ENNReal.ofReal (2 * pcUpperBound (p : ℝ)) := by rw [tsum_pcSummandTwo]







theorem one_sub_theta_le (henc : PcAnchoredEnclosure) (p : ℝ≥0) (hp : p ≤ 1)
    (hsum : ‖pcRatio (p : ℝ)‖ < 1) :
    1 - theta 2 p hp ≤ 2 * pcUpperBound (p : ℝ) := by
  set μ := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp with hμ
  
  have hsuper : 1 - theta 2 p hp ≤ μ.real ((percolationEvent 2)ᶜ) := by
    have hsub : μ Set.univ ≤ μ (percolationEvent 2) + μ ((percolationEvent 2)ᶜ) := by
      have huniv : (Set.univ : Set (ConfigSpace (Sym2 (Site 2))))
          = percolationEvent 2 ∪ (percolationEvent 2)ᶜ := by simp
      rw [huniv]; exact measure_union_le _ _
    rw [measure_univ] at hsub
    have hA : μ (percolationEvent 2) ≠ ⊤ := measure_ne_top _ _
    have hAc : μ ((percolationEvent 2)ᶜ) ≠ ⊤ := measure_ne_top _ _
    have hr := (ENNReal.toReal_le_toReal (by simp)
      (by simp [hA, hAc] : μ (percolationEvent 2) + μ ((percolationEvent 2)ᶜ) ≠ ⊤)).mpr hsub
    rw [ENNReal.toReal_add hA hAc, ENNReal.toReal_one] at hr
    simp only [theta, Measure.real, hμ]
    linarith
  
  have hb : (0 : ℝ) ≤ 2 * pcUpperBound (p : ℝ) := by
    have := pcUpperBound_nonneg (p := (p : ℝ)) (by exact_mod_cast hp); linarith
  have hle : μ.real ((percolationEvent 2)ᶜ) ≤ 2 * pcUpperBound (p : ℝ) := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal hb (measure_compl_percolationEvent_le henc p hp hsum)
  linarith









theorem pc_lt_one_of_enclosure (henc : PcAnchoredEnclosure) : pc 2 < 1 := by
  
  have htail := pcUpperBound_tendsto_one
  have hhalf : ∀ᶠ p in nhds (1 : ℝ), pcUpperBound p < 1 / 2 :=
    htail.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  
  have hbase : ∀ᶠ p in nhds (1 : ℝ), ‖pcRatio p‖ < 1 := by
    have hlt := (pcRatio_tendsto_one).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    have hgt := (pcRatio_tendsto_one).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
    filter_upwards [hlt, hgt] with p hp hp'
    rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hhalf.and hbase)
  
  set p₀ : ℝ := max (1 - ε / 2) 0 with hp₀
  have hp₀lt : p₀ < 1 := by rw [hp₀]; exact max_lt (by linarith) (by norm_num)
  have hp₀0 : (0 : ℝ) ≤ p₀ := le_max_right _ _
  have hp₀ge : 1 - ε / 2 ≤ p₀ := le_max_left _ _
  
  have hkey : ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 / 2 ∧ ‖pcRatio p‖ < 1 := by
    intro p hlo hhi
    apply hball
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  
  set s : ℝ := (p₀ + 1) / 2 with hs
  have hp₀s : p₀ < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) ≤ s := by rw [hs]; linarith
  set sN : ℝ≥0 := s.toNNReal with hsN
  have hsNcoe : (sN : ℝ) = s := by rw [hsN]; exact Real.coe_toNNReal s hs0
  have hsN1 : sN ≤ 1 := by
    rw [hsN, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hslt.le
  have hsNlt1 : sN < 1 := by
    rw [hsN, ← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff_of_nonneg hs0]; exact hslt
  have hub : ∀ q ∈ subcriticalSet 2, q ≤ sN := by
    intro q hq
    by_contra hcon
    push Not at hcon
    have hqreal : s < (q : ℝ) := by
      have hsq : (sN : ℝ) < (q : ℝ) := by exact_mod_cast hcon
      rwa [hsNcoe] at hsq
    have hq1 : q ≤ 1 := hq.1
    have hp₀q : p₀ < (q : ℝ) := lt_trans hp₀s hqreal
    have hq1r : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    obtain ⟨hbnd, hbase'⟩ := hkey (q : ℝ) hp₀q hq1r
    
    have hcb : 1 - theta 2 q hq1 ≤ 2 * pcUpperBound (q : ℝ) := one_sub_theta_le henc q hq1 hbase'
    have hθ : 0 < theta 2 q hq1 := by nlinarith [hbnd]
    
    obtain ⟨hq', hzero⟩ := hq
    rw [show hq' = hq1 from rfl] at hzero
    exact (ne_of_gt hθ) hzero
  calc pc 2 = sSup (subcriticalSet 2) := rfl
    _ ≤ sN := csSup_le' hub
    _ < 1 := hsNlt1




















end Percolation

end StatMech
