/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointConnectivity
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreePercolationAbovePc
public import PhyslibExt.StatisticalMechanics.RandomCluster.Ergodicity
public import MathlibExt.Probability.Configuration.CylinderDeriv
public import MathlibExt.Probability.CorrelationInequalities.InfiniteBK
/-!
# Non-triviality of the Bernoulli critical point via the Ising model

For `d ≥ 2`, the critical probability of Bernoulli bond percolation on `ℤ^d` satisfies
`0 < p_c(d) < 1`. The upper bound is derived from spontaneous magnetization of the Ising model.

## i. Overview

The FK representation identifies the spontaneous magnetization of the `d`-dimensional Ising model
at inverse temperature `β` with the wired `q = 2` random-cluster percolation probability
`θ¹(p, 2)`, where `p = 1 - e^{-2β}`. On `ℤ²` the Peierls argument gives a `β` with positive
magnetization, hence `θ¹(p, 2) > 0` for some `p < 1`. For `q ≥ 1` the wired random-cluster
measure is dominated by Bernoulli percolation on increasing events (Holley), so the Bernoulli
percolation probability satisfies `θ(p) ≥ θ¹(p, 2) > 0` and `p_c(2) ≤ p < 1`.
Embedding `ℤ²` as a plane in `ℤ^d` gives `θ_2(p) ≤ θ_d(p)`, so `p_c(d) < 1` for every `d ≥ 2`.
The lower bound `0 < p_c(d)` is the path-counting bound.

The result is unconditional.

## ii. Key results

- `bernoulliProduct_map_injective_restrict` : precomposing a Bernoulli product configuration with
  an injective map of index sets gives the Bernoulli product measure.
- `fkProbOne_event_eq_bernoulli` : the finite random-cluster measure with `q = 1` agrees with the
  Bernoulli product measure on events depending on the graph edges.
- `fkTheta_two_le_bernoulliTheta` : `θ¹(p, 2) ≤ θ(p)` on `ℤ^d`.
- `theta_two_le_theta_add` : `θ_2(p) ≤ θ_{2+k}(p)`.
- `theta_mono_parameter` : `θ_d(p)` is monotone in `p`.
- `pc_nontrivial_of_two_le` : `0 < p_c(d) < 1` for `d ≥ 2`.

## iii. Table of contents

- A. Bernoulli percolation as the `q = 1` random-cluster measure
- B. Comparison of wired `q = 2` and Bernoulli percolation probabilities
- C. Embedding the plane in `ℤ^d`
- D. Non-triviality of the critical point

## iv. References

- S. R. Broadbent and J. M. Hammersley, *Percolation processes I. Crystals and mazes*,
  Proc. Cambridge Philos. Soc. 53 (1957).
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Theorem 1.10.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.21.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice

/-! ## A. Bernoulli percolation as the `q = 1` random-cluster measure -/

/-- Pulling a Bernoulli product configuration back along an injective map `f : I → E` gives the
Bernoulli product measure on `I`. See also `MeasureTheory.Measure.infinitePi_map_restrict'` for
the case of a subset. -/
lemma bernoulliProduct_map_injective_restrict
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

/-- The `q = 1` random-cluster probability of a given pattern on the graph edges is its Bernoulli
weight. -/
lemma fkProbOne_pattern (p : ℝ) (eta : ConfigSpace ↥G.edgeFinset) :
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
      · rw [ite_eq_left hrest, one_mul]
        unfold edgeProduct
        apply Finset.prod_congr rfl
        intro e he
        change e ∈ F at he
        have hev : omega e = eta ⟨e, he⟩ := by
          have := congrFun hrest ⟨e, he⟩
          simpa [Finset.restrict] using this
        simp only [w, he, dite_true, hev, ite_eq_left]
      · rw [ite_eq_right hrest, zero_mul]
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
        simp only [w, e.2, dite_true, hene, ite_false]
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

/-- The `q = 1` random-cluster measure on a finite graph agrees with Bernoulli percolation on events
that depend only on the graph edges. -/
lemma fkProbOne_event_eq_bernoulli {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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

omit [DecidableEq V] in
/-- The event that `x` is connected to the boundary depends only on the graph edges. -/
lemma connToBdryEvent_dependsOn (G : SimpleGraph V) [DecidableRel G.Adj]
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

/-! ## B. Comparison of wired `q = 2` and Bernoulli percolation probabilities -/

/-- Restricting Bernoulli percolation on `ℤ^d` to the box gives Bernoulli percolation on the box. -/
lemma bernoulliProduct_map_boxRestrict (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    Measure.map (boxRestrict d n)
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) =
      bernoulliProductMeasure (E := Sym2 (boxVerts d n)) p hp := by
  exact
    (bernoulliProduct_map_injective_restrict p hp (edgeIncl d n)
      (edgeIncl_injective d n))

/-- The Bernoulli probability of a box cylinder event equals its probability on the box. -/
lemma bernoulliProduct_boxRestrict_preimage (p : ℝ≥0) (hp : p ≤ 1)
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

/-- The wired `q = 2` box measure of "the origin is connected to the box boundary" is at most its
Bernoulli probability. -/
lemma wiredFinite_boxBdryConnEvent_le_bernoulli
    (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (wiredFiniteMeasure d n (p := (p : ℝ)) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
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

/-- The wired `q = 2` percolation probability is at most the Bernoulli one: `θ¹(p, 2) ≤ θ(p)`. -/
lemma fkTheta_two_le_bernoulliTheta
    (p : ℝ≥0) (hp0 : 0 < p) (hp1 : p < 1) :
    fkTheta d (p := (p : ℝ)) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
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

/-! ## C. Embedding the plane in `ℤ^d` -/

/-- The embedding of `ℤ²` into `ℤ^{2+k}` as the plane of the first two coordinates. -/
def pcv_siteEmbed (k : ℕ) (x : Site 2) : Site (2 + k) :=
  Fin.addCases x (fun _ => 0)

/-- The first two coordinates of an embedded site. -/
@[simp] lemma pcv_siteEmbed_castAdd (k : ℕ) (x : Site 2) (i : Fin 2) :
    pcv_siteEmbed k x (Fin.castAdd k i) = x i := by
  simp [pcv_siteEmbed]

/-- The last `k` coordinates of an embedded site vanish. -/
@[simp] lemma pcv_siteEmbed_natAdd (k : ℕ) (x : Site 2) (i : Fin k) :
    pcv_siteEmbed k x (Fin.natAdd 2 i) = 0 := by
  simp [pcv_siteEmbed]

/-- The plane embedding is injective. -/
lemma pcv_siteEmbed_injective (k : ℕ) : Function.Injective (pcv_siteEmbed k) := by
  intro x y hxy
  funext i
  have := congrFun hxy (Fin.castAdd k i)
  simpa using this

/-- The plane embedding preserves and reflects lattice adjacency. -/
lemma pcv_siteEmbed_adj_iff (k : ℕ) (x y : Site 2) :
    (hypercubicLattice (2 + k)).Adj (pcv_siteEmbed k x) (pcv_siteEmbed k y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_add]
  simp

/-- The plane embedding on edges. -/
def pcv_edgeEmbed (k : ℕ) : Sym2 (Site 2) → Sym2 (Site (2 + k)) :=
  Sym2.map (pcv_siteEmbed k)

/-- The plane embedding on edges is injective. -/
lemma pcv_edgeEmbed_injective (k : ℕ) : Function.Injective (pcv_edgeEmbed k) :=
  Sym2.map.injective (pcv_siteEmbed_injective k)

/-- Restrict a configuration on `ℤ^{2+k}` to the embedded plane. -/
def pcv_planeRestrict (k : ℕ)
    (omega : ConfigSpace (Sym2 (Site (2 + k)))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => omega (pcv_edgeEmbed k e)

/-- Restricting Bernoulli percolation on `ℤ^{2+k}` to the plane gives Bernoulli percolation on `ℤ²`.
-/
lemma bernoulliProduct_map_planeRestrict (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (pcv_planeRestrict k)
        (bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp) =
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp := by
  exact bernoulliProduct_map_injective_restrict p hp (pcv_edgeEmbed k)
    (pcv_edgeEmbed_injective k)

/-- The plane embedding sends the origin to the origin. -/
@[simp] lemma pcv_siteEmbed_origin (k : ℕ) :
    pcv_siteEmbed k (origin 2) = origin (2 + k) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [origin]

/-- Open connections in the restricted plane configuration are open connections in `ℤ^{2+k}`. -/
lemma pcv_connected_of_planeRestrict (k : ℕ)
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

/-- Percolation in the plane implies percolation in `ℤ^{2+k}`. -/
lemma pcv_plane_percolation_subset (k : ℕ) :
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

/-- The Bernoulli percolation probability does not decrease with the dimension: `θ_2(p) ≤
θ_{2+k}(p)`. -/
lemma theta_two_le_theta_add (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    theta 2 p hp ≤ theta (2 + k) p hp := by
  let mud := bernoulliProductMeasure (E := Sym2 (Site (2 + k))) p hp
  let mu2 := bernoulliProductMeasure (E := Sym2 (Site 2)) p hp
  have hpres : MeasurePreserving (pcv_planeRestrict k) mud mu2 :=
    ⟨measurable_pi_iff.mpr fun _ => measurable_pi_apply _,
      bernoulliProduct_map_planeRestrict k p hp⟩
  have hpre := hpres.measureReal_preimage
    (frp_measurableSet_percolationEvent 2).nullMeasurableSet
  unfold theta
  rw [← hpre]
  exact measureReal_mono (pcv_plane_percolation_subset k)

/-! ## D. Non-triviality of the critical point -/

/-- The Bernoulli percolation probability `θ_d(p)` is monotone in `p`. -/
lemma theta_mono_parameter {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
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

/-- Positive percolation probability at `p` gives `p_c(d) ≤ p`. -/
lemma pc_le_of_theta_pos (p : ℝ≥0) (hp : p ≤ 1)
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

/-- There is `p < 1` with `θ_2(p) > 0`, from spontaneous magnetization of the two-dimensional Ising
model. -/
lemma exists_theta_two_pos_below_one :
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

/-- The Bernoulli critical probability on `ℤ²` is below `1`. -/
lemma pc_two_lt_one_via_fk : pc 2 < 1 := by
  obtain ⟨p, hp1, htheta⟩ := exists_theta_two_pos_below_one
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1

/-- `0 < p_c(2) < 1`. -/
lemma pc_two_nontrivial : 0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_two_lt_one_via_fk⟩

/-- The Bernoulli critical probability on `ℤ^d` is below `1` for `d ≥ 2`. -/
lemma pc_lt_one_of_two_le_via_fk {d : ℕ} (hd : 2 ≤ d) : pc d < 1 := by
  obtain ⟨p, hp1, htheta2⟩ := exists_theta_two_pos_below_one
  have htheta : 0 < theta (2 + (d - 2)) p hp1.le :=
    lt_of_lt_of_le htheta2 (theta_two_le_theta_add (d - 2) p hp1.le)
  rw [Nat.add_sub_of_le hd] at htheta
  exact lt_of_le_of_lt (pc_le_of_theta_pos p hp1.le htheta) hp1

/-- **Non-triviality of the percolation critical probability.** For Bernoulli bond percolation
on `ℤ^d` with `d ≥ 2`, `0 < p_c(d) < 1`.

Reference: S. R. Broadbent and J. M. Hammersley, *Percolation processes I*, Proc. Cambridge
Philos. Soc. 53 (1957); G. Grimmett, *Percolation*, 2nd ed. (1999), Theorem 1.10. -/
theorem pc_nontrivial_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    0 < pc d ∧ pc d < 1 :=
  ⟨pc_pos (by omega), pc_lt_one_of_two_le_via_fk hd⟩

end Percolation

end StatMech
