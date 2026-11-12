/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.AvgDensityCollapse
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeWiredClusterCount
/-!
# The wired FK ambient tilted log normalizer and its derivative

With `q > 0` and at least one edge, the wired ambient tilted log normalizer is convex in `t`
and has the average wired density as derivative. For `q ≥ 1`, its difference from the free
ambient tilted log normalizer is bounded by a boundary term.

The sum defining `wiredFkZ` includes unused non-edge coordinates, just as `fkZ` does.
Thus this is an ambient log normalizer, not the edge-restricted physical free energy.
The ambient offset is independent of `t` and cancels in derivatives and in the free-minus-wired
difference on the same graph. The final density-collapse predicate is a hypothesis, not a
convergence theorem for either raw normalizer.

## i. Overview

For a finite graph `G` with wired boundary `∂` and `p = e^t / (1 + e^t)`, the wired per-edge
ambient tilted log normalizer is `f^w_G(t) = |E|⁻¹ log Z^w_G(p, q) + log(1 + e^t)`. Up to the factor
  `|E|⁻¹` it
is the cumulant generating function of the number of open edges under the tilted cluster
weight `q^{k^w(ω)}`, so it is convex and its derivative is `|E|⁻¹ E^w[|ω|]`, the average wired
edge density.

For `q ≥ 1` the wired and free weights differ by a factor in `[1, q^{|∂|}]`, so the wired and
free ambient tilted log normalizers differ by at most `|∂| log q / |E|`; on boxes the
  surface-to-volume ratio
tends to zero, so this difference vanishes in the limit.

## ii. Key results

- `wpd_wiredAmbientTiltLogZ_convexOn` : convexity of the wired ambient tilted log normalizer in `t`.
- `wpd_wiredAmbientTiltLogZ_hasDerivAt` : its derivative is the average wired density.
- `wpd_ambientTiltLogZ_sub_le` : wired and free ambient tilted log normalizers differ by at most
  `|∂| log q / |E|`.

## iii. Table of contents

- A. The wired ambient tilted log normalizer
  - A.1. Cumulant generating function form
  - A.2. Derivative and average wired density
- B. Comparison with the free ambient tilted log normalizer
- C. Box density-collapse hypothesis

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.4 (pressure and its derivative)
  and Thm. 4.63.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-!
## A. The wired ambient tilted log normalizer

### A.1. Cumulant generating function form
-/

/-- The wired per-edge ambient tilted log normalizer `|E|⁻¹ log Z^w(p, q) + log(1 + e^t)` at `p =
  e^t / (1 + e^t)`. -/
noncomputable def wpd_wiredAmbientTiltLogZ (q : ℝ) (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ)) * Real.log (wiredFkZ G bdry (fsc_logistic t) q)
    + Real.log (1 + Real.exp t)

/-- The wired partition function at `p = e^t / (1 + e^t)` as a tilted sum over configurations
divided by `(1 + e^t)^{|E|}`. -/
lemma wpd_wiredFkZ_logistic (t q : ℝ) :
    wiredFkZ G bdry (fsc_logistic t) q
      = ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold wiredFkZ ivp2_Ssum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  unfold wiredFkWeight
  rw [ivp2_edgeProduct_logistic G t ω]
  ring

/-- The wired ambient tilted log normalizer is `|E|⁻¹` times the cumulant generating function of the
  number of open
edges under the weight `q^{k^w}`. -/
lemma wpd_wiredAmbientTiltLogZ_eq_Kcgf (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    wpd_wiredAmbientTiltLogZ G bdry q t
      = (1 / (G.edgeFinset.card : ℝ))
          * ivp2_Kcgf (fun ω => q ^ numClustersWired G bdry ω)
              (fun ω => (openCount G ω : ℝ)) t := by
  unfold wpd_wiredAmbientTiltLogZ ivp2_Kcgf
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hSpos : 0 < ivp2_Ssum w a t := ivp2_Ssum_pos w a hwnn hwpos t
  have hElt : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  have hZ : wiredFkZ G bdry (fsc_logistic t) q
      = ivp2_Ssum w a t / (1 + Real.exp t) ^ G.edgeFinset.card := wpd_wiredFkZ_logistic G bdry t q
  rw [hZ, Real.log_div hSpos.ne' hElt.ne', Real.log_pow]
  have hEne : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring

/-- The wired ambient tilted log normalizer is convex in `t`. -/
lemma wpd_wiredAmbientTiltLogZ_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (wpd_wiredAmbientTiltLogZ G bdry q) := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf w a) := ivp2_Kcgf_convexOn w a hwnn hwpos
  have hsmul : ConvexOn ℝ univ (fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t) :=
    hconv.smul (by positivity)
  have heq : wpd_wiredAmbientTiltLogZ G bdry q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact wpd_wiredAmbientTiltLogZ_eq_Kcgf G bdry q hq hE t
  rw [heq]; exact hsmul

/-!
### A.2. Derivative and average wired density
-/

/-- The expectation of an observable under the wired FK measure. -/
noncomputable def wpd_wiredFkExpect (p q : ℝ) (X : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω * X ω

/-- The tilted mean of the number of open edges is its wired FK expectation. -/
lemma wpd_wiredCgfMean_eq_openCount_expect (q : ℝ) (hq : 0 < q) (t : ℝ) :
    wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))
      = ivp2_S1 (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t
          / ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω)
              (fun ω => (openCount G ω : ℝ)) t := by
  have hSpos : (0:ℝ) < ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω)
      (fun ω => (openCount G ω : ℝ)) t :=
    ivp2_Ssum_pos _ _ (fun ω => pow_nonneg hq.le _) ⟨Classical.arbitrary _, pow_pos hq _⟩ t
  unfold ivp2_Ssum at hSpos
  have hEpos : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  unfold wpd_wiredFkExpect ivp2_S1 ivp2_Ssum wiredFkProb wiredFkWeight
  rw [wpd_wiredFkZ_logistic G bdry t q, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_edgeProduct_logistic G t ω]
  unfold ivp2_Ssum
  simp only []
  rw [eq_div_iff hSpos.ne']
  field_simp

/-- The derivative in `t` of the wired ambient tilted log normalizer is `|E|⁻¹` times the expected
  number of open
edges under the wired FK measure. -/
lemma wpd_wiredAmbientTiltLogZ_hasDerivAt (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    HasDerivAt (wpd_wiredAmbientTiltLogZ G bdry q)
      ((1 / (G.edgeFinset.card : ℝ))
        * wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))) t := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have heq : wpd_wiredAmbientTiltLogZ G bdry q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext s; exact wpd_wiredAmbientTiltLogZ_eq_Kcgf G bdry q hq hE s
  rw [heq, wpd_wiredCgfMean_eq_openCount_expect G bdry q hq t]
  exact (ivp2_Kcgf_hasDerivAt w a hwnn hwpos t).const_mul _

/-- The average wired edge density `|E|⁻¹ E^w[|ω|]` at `p = e^t / (1 + e^t)`. -/
noncomputable def wpd_avgWiredDensity (q : ℝ) (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ))
    * wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))

/-- The expected number of open edges is the sum of the edge marginals. -/
lemma wpd_wiredFkExpect_openCount_eq_sum (p q : ℝ) :
    wpd_wiredFkExpect G bdry p q (fun ω => (openCount G ω : ℝ))
      = ∑ e ∈ G.edgeFinset, edgeMargProb (wiredFkProb G bdry p q) e := by
  unfold wpd_wiredFkExpect
  rw [show (fun ω => wiredFkProb G bdry p q ω * (openCount G ω : ℝ))
        = (fun ω => dfi_openEdgeCount G.edgeFinset ω * wiredFkProb G bdry p q ω) from ?_]
  · exact dfi_openEdgeCount_expect G.edgeFinset (wiredFkProb G bdry p q)
  · funext ω; rw [adc_openCount_eq_sum]; ring

/-- The average wired edge density is the mean of the wired edge marginals. -/
lemma wpd_avgWiredDensity_eq_sum_edgeMarg (q : ℝ) (t : ℝ) :
    wpd_avgWiredDensity G bdry q t
      = (1 / (G.edgeFinset.card : ℝ))
          * ∑ e ∈ G.edgeFinset, edgeMargProb (wiredFkProb G bdry (fsc_logistic t) q) e := by
  unfold wpd_avgWiredDensity
  rw [wpd_wiredFkExpect_openCount_eq_sum]

/-!
## B. Comparison with the free ambient tilted log normalizer
-/

/-- For `q ≥ 1`, the wired FK weight is at most the free one, and the free one is at most
`q^{|∂|}` times the wired one. -/
lemma wpd_wiredFkWeight_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q ω ≤ fkWeight G p q ω
      ∧ fkWeight G p q ω
          ≤ q ^ (Finset.univ.filter bdry).card * wiredFkWeight G bdry p q ω := by
  have hsand := numClusters_wired_sandwich G bdry ω
  have hep : 0 < edgeProduct G p ω := edgeProduct_pos G hp hp1 ω
  unfold wiredFkWeight fkWeight
  refine ⟨mul_le_mul_of_nonneg_left ?_ hep.le, ?_⟩
  · refine pow_le_pow_right₀ hq ?_
    rw [numClusters_eq_numClustersFree]; exact hsand.1
  · rw [show q ^ (Finset.univ.filter bdry).card
            * (edgeProduct G p ω * q ^ numClustersWired G bdry ω)
          = edgeProduct G p ω
              * q ^ (numClustersWired G bdry ω + (Finset.univ.filter bdry).card) by
        rw [pow_add]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hep.le
    refine pow_le_pow_right₀ hq ?_
    rw [numClusters_eq_numClustersFree]; exact hsand.2

/-- For `q ≥ 1`, `Z^w ≤ Z ≤ q^{|∂|} Z^w`. -/
lemma wpd_wiredFkZ_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredFkZ G bdry p q ≤ fkZ G p q
      ∧ fkZ G p q ≤ q ^ (Finset.univ.filter bdry).card * wiredFkZ G bdry p q := by
  refine ⟨?_, ?_⟩
  · unfold wiredFkZ fkZ
    exact Finset.sum_le_sum (fun ω _ => (wpd_wiredFkWeight_le G bdry hp hp1 hq ω).1)
  · unfold wiredFkZ fkZ
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun ω _ => (wpd_wiredFkWeight_le G bdry hp hp1 hq ω).2)

/-- For `q ≥ 1`, the free and wired per-edge ambient tilted log normalizers differ by at most `|∂|
  log q / |E|`. -/
lemma wpd_ambientTiltLogZ_sub_le {q : ℝ} (hq : 1 ≤ q) (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    |ivp2_ambientTiltLogZ G q t - wpd_wiredAmbientTiltLogZ G bdry q t|
      ≤ ((Finset.univ.filter bdry).card : ℝ) / (G.edgeFinset.card : ℝ) * Real.log q := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hwZpos : 0 < wiredFkZ G bdry (fsc_logistic t) q := wiredFkZ_pos G bdry hp hp1 hq0
  have hfZpos : 0 < fkZ G (fsc_logistic t) q := fkZ_pos G hp hp1 hq0
  obtain ⟨hle1, hle2⟩ := wpd_wiredFkZ_le G bdry hp hp1 hq
  have hEpos : (0:ℝ) < (G.edgeFinset.card : ℝ) := by exact_mod_cast hE
  set B : ℝ := ((Finset.univ.filter bdry).card : ℝ) with hB
  have hloglower : Real.log (wiredFkZ G bdry (fsc_logistic t) q)
      ≤ Real.log (fkZ G (fsc_logistic t) q) := Real.log_le_log hwZpos hle1
  have hlogupper : Real.log (fkZ G (fsc_logistic t) q)
      ≤ Real.log (wiredFkZ G bdry (fsc_logistic t) q) + B * Real.log q := by
    have h2 : Real.log (fkZ G (fsc_logistic t) q)
        ≤ Real.log (q ^ (Finset.univ.filter bdry).card * wiredFkZ G bdry (fsc_logistic t) q) :=
      Real.log_le_log hfZpos hle2
    rw [Real.log_mul (by positivity) hwZpos.ne', Real.log_pow] at h2
    rw [← hB] at h2; linarith
  unfold ivp2_ambientTiltLogZ wpd_wiredAmbientTiltLogZ
  have heq : (1 / (G.edgeFinset.card : ℝ)) * Real.log (fkZ G (fsc_logistic t) q)
        + Real.log (1 + Real.exp t)
      - ((1 / (G.edgeFinset.card : ℝ)) * Real.log (wiredFkZ G bdry (fsc_logistic t) q)
        + Real.log (1 + Real.exp t))
      = (1 / (G.edgeFinset.card : ℝ))
          * (Real.log (fkZ G (fsc_logistic t) q)
            - Real.log (wiredFkZ G bdry (fsc_logistic t) q)) := by ring
  rw [heq, abs_of_nonneg (by apply mul_nonneg (by positivity); linarith)]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  calc (1 / (G.edgeFinset.card : ℝ))
          * (Real.log (fkZ G (fsc_logistic t) q)
            - Real.log (wiredFkZ G bdry (fsc_logistic t) q))
      ≤ (1 / (G.edgeFinset.card : ℝ)) * (B * Real.log q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = B / (G.edgeFinset.card : ℝ) * Real.log q := by ring

variable {d : ℕ}

/-!
## C. Box density-collapse hypothesis
-/

/-- Average wired density collapse: for every edge `e'` of `Λ_N` and every `t`, the average wired
edge density of `Λ_n` converges to the wired infinite-volume density of `e'`. -/
def wpd_AvgWiredDensityCollapse (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))

end FK

end StatMech
