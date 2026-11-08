/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity
public import MathlibExt.Probability.Percolation.PcUpper
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial
/-!
# The random-cluster critical point on `ℤ²` is below one, given a Peierls bound

On `ℤ²`, `p_c(q) < 1` for `q ≥ 1` follows from a Peierls-type bound on the probability that the
open cluster of the origin is finite.

## i. Overview

If the open cluster of the origin in `ℤ²` is finite, a closed circuit of lattice edges
(dual to the edge boundary of the cluster) separates the origin from infinity. Counting circuits
of length `ℓ` by `ℓ · 4^ℓ` and bounding the probability that a circuit of length `ℓ` is closed by
`(1 - p)^ℓ` gives `1 - θ¹(p, q) ≤ Σ_ℓ ℓ (2d)^ℓ (1 - p)^ℓ`; the right side tends to `0` as
`p → 1`.

This file proves the geometric step (a finite cluster is surrounded by a closed circuit) and the
analytic step (the series is below `1` near `p = 1`) unconditionally. The probabilistic step, the
bound `1 - θ¹(p, q) ≤ Σ_ℓ ℓ 4^ℓ (1 - p)^ℓ` for the random-cluster measure, is **not** proved here:
it enters `fkPc_lt_one` as the hypothesis `hGeom`, stated through `FkNonPercolationBound`, for
all `p` in some interval `(p₀, 1)`. For Bernoulli percolation (`q = 1`) the circuit bound is the
classical Peierls argument; for `q > 1` the probability that `ℓ` given edges are closed is only
bounded by `(q(1 - p) / (p + q(1 - p)))^ℓ`, so `hGeom` must be checked separately.

## ii. Key results

- `exists_closed_latticeCircuit_of_finite_cluster` : a finite open cluster of the origin in `ℤ²`
  is surrounded by a lattice cycle all of whose dual edges are closed.
- `fkPcUpperBound_tendsto_one` : `Σ_ℓ ℓ (2d)^ℓ (1 - p)^ℓ → 0` as `p → 1`.
- `fkPc_lt_one` : `p_c(q) < 1` on `ℤ²`, assuming the Peierls bound `hGeom`.
- `fkPc_pos_and_lt_one` : `0 < p_c(q) < 1` on `ℤ²`, assuming `hGeom`.

## iii. Table of contents

- A. Walks to the exterior of a finite cluster
- B. Closed circuits around a finite cluster
- C. The Peierls series
- D. The critical point is below one

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 5.1.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

/-! ## A. Walks to the exterior of a finite cluster -/

/-- The horizontal lattice walk of `k` steps from `(a, c)` to `(a + k, c)` in `ℤ²`. -/
noncomputable def horizWalk (c : ℤ) :
    (k : ℕ) → (a : ℤ) → (hypercubicLattice 2).Walk ![a, c] ![a + (k : ℤ), c]
  | 0, a => by
      simpa using (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk ![a, c] ![a, c])
  | k + 1, a => by
      have step : (hypercubicLattice 2).Adj ![a, c] ![a + 1, c] := latAdj_right a c
      have rest := horizWalk c k (a + 1)
      have he : (![a + 1 + (k : ℤ), c] : Site 2) = ![a + ((k + 1 : ℕ) : ℤ), c] := by
        funext i; fin_cases i <;> (simp; try ring)
      rw [he] at rest
      exact SimpleGraph.Walk.cons step rest

/-- A finite set of `ℤ²` misses some point `(N, c)` with `N ≥ a₀` on every horizontal line. -/
lemma exists_far_not_mem (S : Set (Site 2)) (hfin : S.Finite) (c a0 : ℤ) :
    ∃ N : ℤ, a0 ≤ N ∧ (![N, c] : Site 2) ∉ S := by
  by_contra h
  push Not at h
  have hsub : (fun N : ℤ => (![N, c] : Site 2)) '' (Set.Ici a0) ⊆ S := by
    rintro _ ⟨N, hN, rfl⟩; exact h N hN
  have hinj : Set.InjOn (fun N : ℤ => (![N, c] : Site 2)) (Set.Ici a0) := by
    intro x _ y _ hxy; have := congrFun hxy 0; simpa using this
  exact ((Set.Ici_infinite a0).image hinj) (hfin.subset hsub)

/-- A finite cluster of `o` has a lattice-reachable point outside it. -/
lemma exists_walk_exterior {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2, (hypercubicLattice 2).Reachable o z ∧ z ∉ cluster 2 ω o := by
  obtain ⟨N, hNge, hNout⟩ := exists_far_not_mem (cluster 2 ω o) hfin (o 1) (o 0)
  set k := (N - o 0).toNat with hk
  have hofun : o = ![o 0, o 1] := by funext i; fin_cases i <;> rfl
  have hkeq : (k : ℤ) = N - o 0 := by rw [hk]; omega
  refine ⟨![N, o 1], ?_, hNout⟩
  have w := horizWalk (o 1) k (o 0)
  have he : (![o 0 + (k : ℤ), o 1] : Site 2) = ![N, o 1] := by
    funext i; fin_cases i <;> simp [hkeq]
  rw [he] at w
  rw [hofun]
  exact ⟨w⟩

/-! ## B. Closed circuits around a finite cluster -/

/-- The event that every primal edge crossed by the dual circuit `c` is closed. -/
def closedCircuitEvent {u : Site 2} (c : (hypercubicLattice 2).Walk u u) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | ∀ f g : Site 2, s(f, g) ∈ c.edges → ω (sharedPrimalEdge f g) = false}

/-- A finite open cluster of `o` in `ℤ²` is surrounded by a lattice cycle whose crossed primal edges
are all closed. -/
lemma exists_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧
      ω ∈ closedCircuitEvent c := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨u, c0, hc0cyc⟩ := exists_dualCircuit_of_finite_cluster o hfin w hzout
  refine ⟨u, c0.mapLe (faceBoundaryGraph_le _), hc0cyc.mapLe _, ?_⟩
  intro f g hfg
  rw [Walk.edges_mapLe_eq_edges] at hfg
  have hadj : (faceBoundaryGraph (cluster 2 ω o)).Adj f g := c0.adj_of_mem_edges hfg
  have hbd : bdEdge (cluster 2 ω o) (sharedPrimalEdge f g) := hadj.2
  obtain ⟨p, q, hpq, hadjpq⟩ := sharedPrimalEdge_isLatticeEdge hadj.1
  rw [hpq] at hbd ⊢
  rw [bdEdge_mk] at hbd
  exact cluster_edgeBoundary_isClosed o ((mem_edgeBoundary).mpr ⟨hadjpq, hbd⟩)

/-- The closed circuit of `exists_closed_latticeCircuit_of_finite_cluster`, together with a point
that the cluster boundary separates from `o` and an odd crossing number for every walk to it. -/
lemma exists_enclosing_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2,
      (∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧ ω ∈ closedCircuitEvent c)
        ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z
        ∧ ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨_, hsep, hwind⟩ := cluster_enclosed_with_winding o hfin w hzout
  exact ⟨z, exists_closed_latticeCircuit_of_finite_cluster o hfin, hsep, hwind⟩

/-- The event that the cluster of `o` is finite is covered by the closed-circuit events. -/
lemma finiteCluster_subset_iUnion_closedCircuit (o : Site 2) :
    {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω o).Finite}
      ⊆ ⋃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u) (_ : c.IsCycle),
          closedCircuitEvent c := by
  intro ω hω
  obtain ⟨u, c, hcyc, hmem⟩ := exists_closed_latticeCircuit_of_finite_cluster o hω
  exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcyc, hmem⟩⟩⟩

/-- No percolation from the origin means the cluster of the origin is finite. -/
lemma compl_percolationEvent_eq_finiteCluster :
    (percolationEvent 2)ᶜ
      = {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω (origin 2)).Finite} := by
  ext ω
  rw [Set.mem_compl_iff, mem_percolationEvent, Set.mem_ofPred_eq, Set.not_infinite]

/-! ## C. The Peierls series -/

/-- The Peierls series `Σ_ℓ ℓ (2d)^ℓ (1 - p)^ℓ` bounding the probability of a finite cluster. -/
noncomputable def fkPcUpperBound (d : ℕ) (p : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ

/-- The ratio `2d (1 - p)` of the Peierls series. -/
noncomputable def fkPcRatio (d : ℕ) (p : ℝ) : ℝ := (2 * d : ℝ) * (1 - p)

/-- Unfolding `fkPcRatio`. -/
@[simp] lemma fkPcRatio_def (d : ℕ) (p : ℝ) : fkPcRatio d p = (2 * d : ℝ) * (1 - p) := rfl

/-- The Peierls summand in terms of `fkPcRatio`. -/
lemma fkPcSummand_eq (d : ℕ) (p : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ := by
  rw [fkPcRatio_def, mul_assoc, ← mul_pow]

/-- Closed form `x / (1 - x)²` of the Peierls series for `|x| < 1`, where `x = 2d (1 - p)`. -/
lemma fkPcUpperBound_eq_closedForm (d : ℕ) (p : ℝ) (hx : ‖fkPcRatio d p‖ < 1) :
    fkPcUpperBound d p = (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2 := by
  unfold fkPcUpperBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (fkPcRatio d p) ^ ℓ) from funext (fkPcSummand_eq d p)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx

/-- `2d (1 - p) → 0` as `p → 1`. -/
lemma fkPcRatio_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds 0) := by
  have h : Tendsto (fun p : ℝ => fkPcRatio d p) (nhds 1) (nhds ((2 * d : ℝ) * (1 - 1))) := by
    unfold fkPcRatio
    exact (((tendsto_id).const_sub 1).const_mul (2 * d : ℝ))
  simpa using h

/-- `x / (1 - x)² → 0` as `x → 0`. -/
lemma fkPcClosedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this

/-- The Peierls series tends to `0` as `p → 1`. -/
lemma fkPcUpperBound_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ => fkPcUpperBound d p) (nhds 1) (nhds 0) := by
  have hev : (fun p : ℝ => fkPcUpperBound d p) =ᶠ[nhds 1]
      (fun p : ℝ => (fkPcRatio d p) / (1 - fkPcRatio d p) ^ 2) := by
    have hlt : ∀ᶠ p in nhds 1, ‖fkPcRatio d p‖ < 1 := by
      have hsmall := (fkPcRatio_tendsto_one d).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      have hgt : ∀ᶠ p in nhds 1, (-1 : ℝ) < fkPcRatio d p :=
        (fkPcRatio_tendsto_one d).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
      filter_upwards [hsmall, hgt] with p hp hp'
      rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
    filter_upwards [hlt] with p hp
    exact fkPcUpperBound_eq_closedForm d p hp
  rw [tendsto_congr' hev]
  exact fkPcClosedForm_tendsto_zero.comp (fkPcRatio_tendsto_one d)

/-- The Peierls series is below `1` on an interval `(p₀, 1]`. -/
lemma exists_p_lt_one_fkPcUpperBound_lt_one (d : ℕ) :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → fkPcUpperBound d p < 1 := by
  have h : ∀ᶠ p in nhds 1, fkPcUpperBound d p < 1 :=
    (fkPcUpperBound_tendsto_one d).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hfn⟩ := h
  refine ⟨1 - ε / 2, by linarith, fun p hp1 _ => ?_⟩
  apply hfn
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-- The Peierls series is nonnegative for `p ≤ 1`. -/
lemma fkPcUpperBound_nonneg (d : ℕ) {p : ℝ} (hp : p ≤ 1) : 0 ≤ fkPcUpperBound d p := by
  unfold fkPcUpperBound
  apply tsum_nonneg
  intro ℓ
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

/-! ## D. The critical point is below one -/

/-- The Peierls bound for the wired random-cluster measure on `ℤ²` at `(p, q)`:
`1 - θ¹(p, q) ≤ Σ_ℓ ℓ 4^ℓ (1 - p)^ℓ`. It is a hypothesis of `fkPc_lt_one`, not proved here. -/
def FkNonPercolationBound (q : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p

/-- The Peierls bound with a series below `1` gives percolation: `0 < θ¹(p, q)`. -/
lemma fkTheta_pos_of_nonPercolationBound {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hBound : FkNonPercolationBound q hp hp1 hq)
    (hsum : fkPcUpperBound 2 p < 1) :
    0 < fkTheta 2 hp hp1 hq (q := q) := by
  have h : 1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p := hBound
  linarith

/-- For `q ≥ 1` the subcritical set on `ℤ²` is nonempty (it contains `1/8`). -/
lemma fkSubcriticalSet_nonempty {q : ℝ} (hq : 1 ≤ q) : (fkSubcriticalSet 2 q).Nonempty := by
  set p : ℝ := 1 / (4 * 2) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; norm_num
  have hp1 : p < 1 := by rw [hp_def]; norm_num
  have hsmall : (2 * (2 : ℕ) : ℝ) * p < 1 := by rw [hp_def]; norm_num
  exact ⟨p, hp_pos, hp1, zero_lt_one.trans_le hq,
    fkTheta_eq_zero_of_lt (by norm_num) hp_pos hp1 hq hsmall⟩

/-- A parameter with positive percolation probability is not subcritical. -/
lemma not_mem_fkSubcriticalSet_of_fkTheta_pos {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hθ : 0 < fkTheta 2 hp hp1 hq (q := q)) : p ∉ fkSubcriticalSet 2 q := by
  intro hmem
  obtain ⟨hp', hp1', hq', hzero⟩ := hmem
  rw [show hp' = hp from rfl, show hp1' = hp1 from rfl, show hq' = hq from rfl] at hzero
  exact (ne_of_gt hθ) hzero

/-- For `q ≥ 1`, the random-cluster critical point on `ℤ²` satisfies `p_c(q) < 1`, assuming the
Peierls bound `FkNonPercolationBound` for all `p` in some interval `(p₀, 1)`. -/
lemma fkPc_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    fkPc 2 q < 1 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨p₁, hp₁lt, hp₁bound⟩ := exists_p_lt_one_fkPcUpperBound_lt_one 2
  obtain ⟨p₂, hp₂lt, hp₂geom⟩ := hGeom
  set t : ℝ := max (max p₁ p₂) 0 with ht
  have htlt : t < 1 := max_lt (max_lt hp₁lt hp₂lt) (by norm_num)
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have hp₁t : p₁ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have hp₂t : p₂ ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  set s : ℝ := (t + 1) / 2 with hs
  have hts : t < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; linarith
  have hub : ∀ r ∈ fkSubcriticalSet 2 q, r ≤ s := by
    intro r hr
    by_contra hcon
    push Not at hcon
    obtain ⟨hr0, hr1, _, hzero⟩ := hr
    have hp₁r : p₁ < r := lt_of_le_of_lt (le_trans hp₁t hts.le) hcon
    have hp₂r : p₂ < r := lt_of_le_of_lt (le_trans hp₂t hts.le) hcon
    have hbnd : fkPcUpperBound 2 r < 1 := hp₁bound r hp₁r hr1.le
    have hcb : FkNonPercolationBound q hr0 hr1 hq0 := hp₂geom r hr0 hr1 hp₂r
    have hθ : 0 < fkTheta 2 hr0 hr1 hq0 (q := q) :=
      fkTheta_pos_of_nonPercolationBound hr0 hr1 hq0 hcb hbnd
    exact not_mem_fkSubcriticalSet_of_fkTheta_pos hr0 hr1 hq0 hθ
      ⟨hr0, hr1, hq0, hzero⟩
  calc fkPc 2 q = sSup (fkSubcriticalSet 2 q) := rfl
    _ ≤ s := csSup_le (fkSubcriticalSet_nonempty hq) hub
    _ < 1 := hslt

/-- For `q ≥ 1`, `0 < p_c(q) < 1` on `ℤ²`, assuming the Peierls bound as in `fkPc_lt_one`. -/
lemma fkPc_pos_and_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    0 < fkPc 2 q ∧ fkPc 2 q < 1 :=
  ⟨fkPc_pos_of_two_le (le_refl 2) hq, fkPc_lt_one hq hGeom⟩

/-- The Peierls series for `d = 2` is the Bernoulli Peierls series
`StatMech.Percolation.pcUpperBound`. -/
lemma fkPcUpperBound_two_eq_pcUpperBound (p : ℝ) :
    fkPcUpperBound 2 p = Percolation.pcUpperBound p := by
  unfold fkPcUpperBound Percolation.pcUpperBound
  norm_num

end FK

end StatMech
