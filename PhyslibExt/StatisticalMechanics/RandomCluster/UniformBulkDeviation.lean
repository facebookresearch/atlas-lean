/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredPressureDeriv
/-!
# Uniform bulk deviation and growing-box collapse

Predicates expressing uniform bulk control of box marginals, and elementary facts about free and
wired edge densities.

## i. Overview

Fix `q = 2` and `p = e^t / (1 + e^t)`. A *uniform bulk deviation* bound says that, for each box
`Λ_n`, a bulk set of edges has marginals uniformly close to the infinite-volume density, with a
vanishing boundary fraction (`ubd_FreeUniformBulkDeviation`, `ubd_WiredUniformBulkDeviation`).
*Growing-box collapse* says that the average free edge density of `Λ_n` converges to the free
infinite-volume density (`ubd_FreeGrowingBoxCollapse`). The file also records that edge marginals
and edge densities lie in `[0, 1]` and that the average wired density is the average of the wired
edge marginals.

## ii. Key results

- `ubd_FreeUniformBulkDeviation`, `ubd_WiredUniformBulkDeviation` : uniform bulk deviation bounds.
- `ubd_FreeGrowingBoxCollapse` : growing-box collapse of the free density.
- `ubd_freeEdgeDensity_mem_Icc`, `ubd_wiredEdgeDensity_mem_Icc` : the edge densities lie in
  `[0, 1]`.
- `ubd_avgWiredDensity_eq_sum` : the average wired density as an average of edge marginals.

## iii. Table of contents

- A. Growing-box collapse
- B. Bounds on edge densities
- C. Uniform bulk deviation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4.6.
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

variable {d : ℕ}

/-!
## A. Growing-box collapse
-/

/-- Free growing-box collapse: for every edge `e'` of `Λ_N` and every `t`, the average free edge
density of `Λ_n` converges to the free infinite-volume density of `e'`. -/
def ubd_FreeGrowingBoxCollapse (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))

/-!
## B. Bounds on edge densities
-/

/-- The free infinite-volume `q = 2` edge density lies in `[0, 1]`. -/
lemma ubd_freeEdgeDensity_mem_Icc (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (N + k)) hp hp1 (by norm_num) _)
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (N + k)) hp hp1 (by norm_num) _)

/-- Edge marginals of a wired FK measure are nonnegative. -/
lemma ubd_edgeMargProb_wiredFkProb_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (e : Sym2 V) :
    0 ≤ edgeMargProb (wiredFkProb G bdry p q) e := by
  unfold edgeMargProb
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg _ (wiredFkProb_nonneg G bdry hp hp1 hq ω)
  split <;> norm_num

/-- Edge marginals of a wired FK measure are at most `1`. -/
lemma ubd_edgeMargProb_wiredFkProb_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (e : Sym2 V) :
    edgeMargProb (wiredFkProb G bdry p q) e ≤ 1 := by
  unfold edgeMargProb
  calc ∑ ω : ConfigSpace (Sym2 V), (if ω e then (1:ℝ) else 0) * wiredFkProb G bdry p q ω
      ≤ ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω := by
        apply Finset.sum_le_sum
        intro ω _
        have hb : (if ω e then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
        calc (if ω e then (1:ℝ) else 0) * wiredFkProb G bdry p q ω
            ≤ 1 * wiredFkProb G bdry p q ω :=
              mul_le_mul_of_nonneg_right hb (wiredFkProb_nonneg G bdry hp hp1 hq ω)
          _ = wiredFkProb G bdry p q ω := one_mul _
    _ = 1 := wiredFkProb_sum_eq_one G bdry hp hp1 hq

/-- The wired infinite-volume `q = 2` edge density lies in `[0, 1]`. -/
lemma ubd_wiredEdgeDensity_mem_Icc (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hlim := dfi_wired_density_eq_limit N e' hp hp1
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (by norm_num) _)
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (by norm_num) _)

/-!
## C. Uniform bulk deviation
-/

/-- The average wired edge density of `Λ_n` is the mean of the wired edge marginals. -/
lemma ubd_avgWiredDensity_eq_sum (n : ℕ) (t : ℝ) :
    wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t
      = (1 / ((boxGraph d n).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d n).edgeFinset,
              edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e :=
  wpd_avgWiredDensity_eq_sum_edgeMarg (boxGraph d n) (boxBoundary d n) 2 t

/-- Free uniform bulk deviation: for every edge `e'` and `t`, each box `Λ_n` has a bulk edge set
with free marginals within `δ_n → 0` of the free density of `e'`, and the non-bulk edge
fraction tends to zero. -/
def ubd_FreeUniformBulkDeviation (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e
          - freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)

/-- Wired uniform bulk deviation: for every edge `e'` and `t`, each box `Λ_n` has a bulk edge set
with wired marginals within `δ_n → 0` of the wired density of `e'`, and the non-bulk edge
fraction tends to zero. -/
def ubd_WiredUniformBulkDeviation (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    ∃ (In : (n : ℕ) → Finset (Sym2 (boxVerts d n))) (δ : ℕ → ℝ),
      (∀ n, In n ⊆ (boxGraph d n).edgeFinset) ∧
      (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ∀ e ∈ In n,
        |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e
          - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)| ≤ δ n) ∧
      Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
        atTop (𝓝 0)

end FK

end StatMech
