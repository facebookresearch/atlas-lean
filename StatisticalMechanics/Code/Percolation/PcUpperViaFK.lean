/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.IsingFK.PcUpperPeierls
import Code.FK.PcNontrivial
import Code.FK.TwoPointPositiveFull
import Code.FK.FreePercolationFull
import Code.FK.Ergodicity
import Code.Foundations.CylinderDeriv
import Code.Probability.InfiniteBK

open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice



theorem bernoulliProduct_map_injective_restrict
    {I E : Type*} [Countable I] [Countable E]
    (p : ℝ≥0) (hp : p ≤ 1) (f : I → E) (hf : Function.Injective f) :
    Measure.map (fun (omega : ConfigSpace E) (i : I) => omega (f i))
        (bernoulliProductMeasure (E := E) p hp) =
      bernoulliProductMeasure (E := I) p hp := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : I) (omega : ConfigSpace E) => omega (f i))
      (bernoulliProductMeasure (E := E) p hp) :=
    ProbabilityTheory.iIndepFun.precomp hf (bernoulli_iIndepFun p hp)
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_apply (f i))).mp hind
  rw [hmap]
  have hmarg : ∀ i : I,
      Measure.map (fun (omega : ConfigSpace E) => omega (f i))
          (bernoulliProductMeasure (E := E) p hp) = bernoulliMeasure p hp := by
    intro i
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_eval (fun _ : E => bernoulliMeasure p hp) (f i)
  simp_rw [hmarg]
  unfold bernoulliProductMeasure
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem fkProbOne_pattern (p : ℝ) (eta : ConfigSpace ↥G.edgeFinset) :
    ∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega = configWeight p eta := by
  classical
  let F := G.edgeFinset
  change ConfigSpace ↥F at eta
  let w : Sym2 V → Bool → ℝ := fun e b =>
    if he : e ∈ F then
      if b = eta ⟨e, he⟩ then (if b then p else 1 - p) else 0
    else 1
  have hnum :
      (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) =
        2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta := by
    have hpoint : ∀ omega : ConfigSpace (Sym2 V),
        (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega =
          ∏ e ∈ F, w e (omega e) := by
      intro omega
      by_cases hrest : F.restrict omega = eta
      · rw [if_pos hrest, one_mul]
        unfold edgeProduct
        apply Finset.prod_congr rfl
        intro e he
        change e ∈ F at he
        have hev : omega e = eta ⟨e, he⟩ := by
          have := congrFun hrest ⟨e, he⟩
          simpa [Finset.restrict] using this
        simp only [w, he, dite_true, hev, if_pos]
      · rw [if_neg hrest, zero_mul]
        have hex : ∃ e : ↥F, omega e ≠ eta e := by
          by_contra h
          simp only [not_exists, not_not] at h
          apply hrest
          funext e
          exact h e
        obtain ⟨e, he⟩ := hex
        symm
        apply Finset.prod_eq_zero (i := (e : Sym2 V)) e.2
        have hene : omega (e : Sym2 V) ≠ eta ⟨(e : Sym2 V), e.2⟩ := by
          simpa using he
        simp only [w, e.2, dite_true, hene, if_false]
    calc
      (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) =
          ∑ omega : ConfigSpace (Sym2 V), ∏ e ∈ F, w e (omega e) := by
            apply Finset.sum_congr rfl
            intro omega _
            exact hpoint omega
      _ = 2 ^ (Fintype.card (Sym2 V) - F.card) *
          ∏ e ∈ F, (∑ b : Bool, w e b) := sum_prod_factor F w
      _ = 2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta := by
        congr 1
        unfold configWeight edgeWeight
        rw [← Finset.prod_attach]
        apply Finset.prod_congr rfl
        intro e _
        have heF : (e : Sym2 V) ∈ F := e.2
        simp only [w, heF, dite_true]
        cases eta e <;> simp
  have hZ : fkZ G p 1 = 2 ^ (Fintype.card (Sym2 V) - F.card) := by
    rw [fkZ_one]
    change (∑ omega : ConfigSpace (Sym2 V),
      ∏ e ∈ F, (fun _ b => if b then p else 1 - p) e (omega e)) = _
    rw [sum_prod_factor F (fun _ b => if b then p else 1 - p)]
    simp
  have hpow : (0 : ℝ) < 2 ^ (Fintype.card (Sym2 V) - F.card) := by positivity
  simpa only [F] using (show
    (∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega) = configWeight p eta from by
   calc
    (∑ omega : ConfigSpace (Sym2 V),
        (if G.edgeFinset.restrict omega = eta then (1 : ℝ) else 0) *
          fkProb G p 1 omega) =
        (∑ omega : ConfigSpace (Sym2 V),
          (if F.restrict omega = eta then (1 : ℝ) else 0) * edgeProduct G p omega) /
            fkZ G p 1 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro omega _
      unfold fkProb
      rw [fkWeight_one]
      ring
    _ = (2 ^ (Fintype.card (Sym2 V) - F.card) * configWeight p eta) /
          2 ^ (Fintype.card (Sym2 V) - F.card) := by rw [hnum, hZ]
    _ = configWeight p eta := by field_simp)



theorem fkProbOne_event_eq_bernoulli {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V)))
    (hA : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V))) :
    ∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * fkProb G p 1 omega =
      (bernoulliProductMeasure (E := Sym2 V) ⟨p, hp.le⟩
        (by exact_mod_cast hp1.le)).real A := by
  classical
  let F := G.edgeFinset
  let B : Set (ConfigSpace ↥F) := F.restrict '' A
  have hmem : ∀ omega : ConfigSpace (Sym2 V),
      omega ∈ A ↔ F.restrict omega ∈ B := by
    intro omega
    rw [show A = cylinder F B from eq_cylinder_restrict_image A F hA]
    rfl
  rw [realProb_cylinder_eq_finsum ⟨p, hp.le⟩ (by exact_mod_cast hp1.le) A F hA]
  calc
    (∑ omega : ConfigSpace (Sym2 V),
        A.indicator (fun _ => (1 : ℝ)) omega * fkProb G p 1 omega) =
      ∑ omega : ConfigSpace (Sym2 V),
        ∑ eta : ConfigSpace ↥F,
          B.indicator (fun _ => (1 : ℝ)) eta *
            ((if F.restrict omega = eta then (1 : ℝ) else 0) * fkProb G p 1 omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hω : omega ∈ A
      · rw [Set.indicator_of_mem hω]
        have hr : F.restrict omega ∈ B := (hmem omega).1 hω
        simp only [Set.indicator_apply]
        simp [hr]
      · rw [Set.indicator_of_notMem hω]
        have hr : F.restrict omega ∉ B := fun h => hω ((hmem omega).2 h)
        simp only [Set.indicator_apply]
        simp [hr]
    _ = ∑ eta : ConfigSpace ↥F,
        B.indicator (fun _ => (1 : ℝ)) eta *
          ∑ omega : ConfigSpace (Sym2 V),
            (if F.restrict omega = eta then (1 : ℝ) else 0) * fkProb G p 1 omega := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro eta _
      rw [Finset.mul_sum]
    _ = ∑ eta : ConfigSpace ↥F,
        B.indicator (fun _ => (1 : ℝ)) eta * configWeight p eta := by
      apply Finset.sum_congr rfl
      intro eta _
      rw [fkProbOne_pattern G p eta]
    _ = ∑ eta : ConfigSpace ↥F,
        (F.restrict '' A).indicator (fun _ => (1 : ℝ)) eta *
          ∏ e : ↥F, (if eta e then p else 1 - p) := by
      rfl



theorem connToBdryEvent_dependsOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) (x : V) :
    _root_.DependsOn
      ({omega : ConfigSpace (Sym2 V) |
        IsingFK.ConnToBdry G bdry omega x}.indicator (fun _ => (1 : ℝ)))
      (G.edgeFinset : Set (Sym2 V)) := by
  classical
  intro omega omega' heq
  have hopen : openSub G omega = openSub G omega' := by
    ext u v
    simp only [openSub_adj]
    constructor
    · rintro ⟨huv, hopen⟩
      refine ⟨huv, ?_⟩
      rw [← heq s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)]
      exact hopen
    · rintro ⟨huv, hopen⟩
      refine ⟨huv, ?_⟩
      rw [heq s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)]
      exact hopen
  have hiff : IsingFK.ConnToBdry G bdry omega x ↔
      IsingFK.ConnToBdry G bdry omega' x := by
    unfold IsingFK.ConnToBdry Connected
    rw [hopen]
  by_cases h : IsingFK.ConnToBdry G bdry omega x
  · have hm : omega ∈ {omega | IsingFK.ConnToBdry G bdry omega x} := h
    have hm' : omega' ∈ {omega | IsingFK.ConnToBdry G bdry omega x} := hiff.mp h
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
  · have hm : omega ∉ {omega | IsingFK.ConnToBdry G bdry omega x} := h
    have hm' : omega' ∉ {omega | IsingFK.ConnToBdry G bdry omega x} :=
      fun h' => h (hiff.mpr h')
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']



variable {d : ℕ}



theorem bernoulliProduct_map_boxRestrict (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    Measure.map (boxRestrict d n)
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) =
      bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp := by
  simpa only [boxRestrict] using
    (bernoulliProduct_map_injective_restrict p hp (edgeIncl d n)
      (edgeIncl_injective d n))


theorem bernoulliProduct_boxRestrict_preimage (p : ℝ≥0) (hp : p ≤ 1)
    (n : ℕ) (A : Set (ConfigSpace (Sym2 (boxVerts d n)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (boxRestrict d n ⁻¹' A) =
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp).real A := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let nu := bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp
  have hpres : MeasurePreserving (boxRestrict d n) mu nu :=
    ⟨(continuous_boxRestrict d n).measurable,
      bernoulliProduct_map_boxRestrict p hp n⟩
  exact hpres.measureReal_preimage MeasurableSet.of_discrete.nullMeasurableSet



theorem wiredFinite_boxBdryConnEvent_le_bernoulli
    (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (wiredFiniteMeasure d n (by exact_mod_cast hp0) (by exact_mod_cast hp1)
        (by norm_num : (0 : ℝ) < 2) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1.le).real
        (boxBdryConnEvent d n) := by
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAinc : IsIncreasing A := isIncreasing_connToBdryEvent n
  have hAdep : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d n).edgeFinset : Set (Sym2 (boxVerts d n))) :=
    connToBdryEvent_dependsOn (boxGraph d n) (boxBoundary d n)
      (IsingFK.boxOrigin d n)
  have hHolley := wiredFkProb_le_fkProbOne_increasing
    (boxGraph d n) (boxBoundary d n) (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) (by norm_num : (1 : ℝ) ≤ 2) hAinc
  have hfinite :
      (∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        A.indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (boxGraph d n) (boxBoundary d n) (p : ℝ) 2 omega) ≤
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp1.le).real A := by
    exact hHolley.trans_eq
      (fkProbOne_event_eq_bernoulli (boxGraph d n)
        (by exact_mod_cast hp0) (by exact_mod_cast hp1) A hAdep)
  rw [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    wiredFiniteMeasure_real_boxRestrictEvent n (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) A
      ((continuous_boxRestrict d n).measurable MeasurableSet.of_discrete),
    bernoulliProduct_boxRestrict_preimage]
  exact hfinite



theorem fkTheta_two_le_bernoulliTheta
    (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1) :
    fkTheta d (by exact_mod_cast hp0) (by exact_mod_cast hp1)
        (by norm_num : (0 : ℝ) < 2) (q := 2) ≤
      Percolation.theta d p hp1.le := by
  have hfk := boxBdryConnEvent_diag_tendsto (d := d)
    (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hbern := boxBdryConnEvent_real_tendsto_percolation (d := d)
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1.le)
  apply le_of_tendsto_of_tendsto hfk
    (by simpa only [Percolation.theta] using hbern)
  exact Filter.Eventually.of_forall
    (wiredFinite_boxBdryConnEvent_le_bernoulli p hp0 hp1)

end FK

namespace Percolation

open StatMech.Lattice StatMech.FK

variable {d : ℕ}


def pcv_siteEmbed (k : ℕ) (x : Site 2) : Site (2 + k) :=
  Fin.addCases x (fun _ => 0)

@[simp] theorem pcv_siteEmbed_castAdd (k : ℕ) (x : Site 2) (i : Fin 2) :
    pcv_siteEmbed k x (Fin.castAdd k i) = x i := by
  simp [pcv_siteEmbed]

@[simp] theorem pcv_siteEmbed_natAdd (k : ℕ) (x : Site 2) (i : Fin k) :
    pcv_siteEmbed k x (Fin.natAdd 2 i) = 0 := by
  simp [pcv_siteEmbed]

theorem pcv_siteEmbed_injective (k : ℕ) : Function.Injective (pcv_siteEmbed k) := by
  intro x y hxy
  funext i
  have := congrFun hxy (Fin.castAdd k i)
  simpa using this


theorem pcv_siteEmbed_adj_iff (k : ℕ) (x y : Site 2) :
    (hypercubicLattice (2 + k)).Adj (pcv_siteEmbed k x) (pcv_siteEmbed k y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_add]
  simp


def pcv_edgeEmbed (k : ℕ) : Sym2 (Site 2) → Sym2 (Site (2 + k)) :=
  Sym2.map (pcv_siteEmbed k)

theorem pcv_edgeEmbed_injective (k : ℕ) : Function.Injective (pcv_edgeEmbed k) :=
  Sym2.map.injective (pcv_siteEmbed_injective k)


def pcv_planeRestrict (k : ℕ)
    (omega : ConfigSpace (Sym2 (Site (2 + k)))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => omega (pcv_edgeEmbed k e)


theorem bernoulliProduct_map_planeRestrict (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (pcv_planeRestrict k)
        (bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp) =
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp := by
  exact bernoulliProduct_map_injective_restrict p hp (pcv_edgeEmbed k)
    (pcv_edgeEmbed_injective k)

@[simp] theorem pcv_siteEmbed_origin (k : ℕ) :
    pcv_siteEmbed k (origin 2) = origin (2 + k) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [origin]


theorem pcv_connected_of_planeRestrict (k : ℕ)
    (omega : ConfigSpace (Sym2 (Site (2 + k)))) {x y : Site 2}
    (h : Lattice.Connected 2 (pcv_planeRestrict k omega) x y) :
    Lattice.Connected (2 + k) omega (pcv_siteEmbed k x) (pcv_siteEmbed k y) := by
  let f : openSubgraph 2 (pcv_planeRestrict k omega) →g openSubgraph (2 + k) omega :=
    { toFun := pcv_siteEmbed k
      map_rel' := by
        intro u v huv
        simp only [openSubgraph_adj] at huv ⊢
        refine ⟨(pcv_siteEmbed_adj_iff k u v).2 huv.1, ?_⟩
        simpa [pcv_planeRestrict, pcv_edgeEmbed] using huv.2 }
  exact h.map f



theorem pcv_plane_percolation_subset (k : ℕ) :
    pcv_planeRestrict k ⁻¹' percolationEvent 2 ⊆ percolationEvent (2 + k) := by
  intro omega hperco
  change pcv_planeRestrict k omega ∈ percolationEvent 2 at hperco
  rw [mem_percolationEvent] at hperco ⊢
  have himg : (pcv_siteEmbed k '' cluster 2 (pcv_planeRestrict k omega) (origin 2)).Infinite :=
    hperco.image (pcv_siteEmbed_injective k).injOn
  apply himg.mono
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_cluster] at hx ⊢
  simpa using pcv_connected_of_planeRestrict k omega hx


theorem theta_two_le_theta_add (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    theta 2 p hp ≤ theta (2 + k) p hp := by
  let mud := bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp
  let mu2 := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpres : MeasurePreserving (pcv_planeRestrict k) mud mu2 :=
    ⟨measurable_pi_lambda _ fun _ => measurable_pi_apply _,
      bernoulliProduct_map_planeRestrict k p hp⟩
  have hpre := hpres.measureReal_preimage
    (frp_measurableSet_percolationEvent 2).nullMeasurableSet
  unfold theta
  rw [← hpre]
  exact measureReal_mono (pcv_plane_percolation_subset k)


theorem theta_mono_parameter {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) : theta d p hp ≤ theta d q hq := by
  let mup := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let muq := bernoulliProductMeasure (E := Sym2 (Site d)) q hq
  have hplim := boxBdryConnEvent_real_tendsto_percolation (d := d) mup
  have hqlim := boxBdryConnEvent_real_tendsto_percolation (d := d) muq
  apply le_of_tendsto_of_tendsto
    (by simpa only [theta, mup] using hplim)
    (by simpa only [theta, muq] using hqlim)
  apply Filter.Eventually.of_forall
  intro n
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAdep : StatMech.DependsOn A
      ((Finset.univ : Finset (Sym2 (boxVerts d n))) : Set _) := by
    intro omega omega' heq
    have homega : omega = omega' := by
      funext e
      exact (heq e (by simp)).symm
    subst omega'
    rfl
  have hmono := ibk_measure_mono_parameter hp hq hpq Finset.univ hAdep
    (isIncreasing_connToBdryEvent n)
  change (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
      (boxBdryConnEvent d n) ≤
    (bernoulliProductMeasure (E := Sym2 (Site d)) q hq).real
      (boxBdryConnEvent d n)
  simpa only [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    bernoulliProduct_boxRestrict_preimage] using hmono



theorem pc_le_of_theta_pos (p : ℝ≥0) (hp : p ≤ 1)
    (hpos : 0 < theta d p hp) : pc d ≤ p := by
  unfold pc
  apply csSup_le'
  intro q hq
  obtain ⟨hq1, hqzero⟩ := hq
  by_contra hnot
  have hpq : p ≤ q := le_of_not_ge hnot
  have hmono := theta_mono_parameter (d := d) hp hq1 hpq
  rw [hqzero] at hmono
  exact (not_lt_of_ge hmono) hpos



theorem exists_theta_two_pos_below_one :
    ∃ (p : ℝ≥0) (hp1 : p < 1), 0 < theta 2 p hp1.le := by
  obtain ⟨beta, hbeta, hmag⟩ := IsingFK.pup_exists_positive_magnetization
  have hp0r : 0 < IsingFK.pOfBeta beta := Ising.pOfBeta_pos hbeta
  have hp1r : IsingFK.pOfBeta beta < 1 := Ising.pOfBeta_lt_one beta
  let p : ℝ≥0 := ⟨IsingFK.pOfBeta beta, hp0r.le⟩
  have hp0 : 0 < p := by exact_mod_cast hp0r
  have hp1 : p < 1 := by exact_mod_cast hp1r
  have hid : Ising.magnetization 2 beta =
      fkTheta 2 hp0r hp1r (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    Ising.mfc_magPercoId 2 (by norm_num) (IsingFK.hbx_hisingBox 2)
      beta hbeta hp0r hp1r
  have hfk : 0 < fkTheta 2 hp0r hp1r (by norm_num : (0 : ℝ) < 2) (q := 2) := by
    rwa [← hid]
  have htheta : 0 < theta 2 p hp1.le :=
    lt_of_lt_of_le hfk (fkTheta_two_le_bernoulliTheta p hp0 hp1)
  exact ⟨p, hp1, htheta⟩




theorem pc_two_lt_one_via_fk : pc 2 < 1 := by
  obtain ⟨p, hp1, htheta⟩ := exists_theta_two_pos_below_one
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1


theorem pc_two_nontrivial : 0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_two_lt_one_via_fk⟩



theorem pc_lt_one_of_two_le_via_fk {d : ℕ} (hd : 2 ≤ d) : pc d < 1 := by
  obtain ⟨p, hp1, htheta2⟩ := exists_theta_two_pos_below_one
  have htheta : 0 < theta (2 + (d - 2)) p hp1.le :=
    lt_of_lt_of_le htheta2 (theta_two_le_theta_add (d - 2) p hp1.le)
  rw [Nat.add_sub_of_le hd] at htheta
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1



theorem pc_nontrivial_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    0 < pc d ∧ pc d < 1 :=
  ⟨pc_pos (by omega), pc_lt_one_of_two_le_via_fk hd⟩

end Percolation

end StatMech
