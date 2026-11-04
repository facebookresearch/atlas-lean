/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeDensityQ2
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeWeakLimit

/-!
# Edge densities in finite and infinite volume for `q = 2`

The infinite-volume `q = 2` edge densities are limits of finite-volume edge marginals, the wired
ones from above and the free ones from below, and these bounds sum over finite edge sets.

## i. Overview

Restricting the finite-volume measures on `Λ_m` to `Λ_N` identifies probabilities of box edge
events with edge marginals of `fkProb` and `wiredFkProb` on the larger box. Monotonicity of the
wired measures (decreasing in the volume) and the free measures (increasing) gives
`φ^0_{Λ_n}(e) ≤ φ^0(e)` and `φ^1(e) ≤ φ^1_{Λ_n}(e)`. Summing over a finite set of edges bounds the
expected number of open edges.

## ii. Key results

- `dfi_wired_density_eq_limit`, `dfi_free_density_eq_limit` : densities as limits of finite-volume
  marginals.
- `dfi_wired_per_edge_ge`, `dfi_free_per_edge_le` : one-sided finite-volume bounds.
- `dfi_box_density_bound_wired`, `dfi_box_density_bound_free` : summed bounds via open-edge counts.

## iii. Table of contents

- A. Finite-volume masses as edge marginals
- B. Densities as limits
- C. One-sided bounds
- D. Open-edge counts

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §4.3.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}

/-! ## A. Finite-volume masses as edge marginals -/

lemma dfi_indicator_boxEdgeOpenEvent (m : ℕ) (e : Sym2 (boxVerts d m))
    (ω : ConfigSpace (Sym2 (boxVerts d m))) :
    (boxEdgeOpenEvent d m e).indicator (fun _ => (1 : ℝ)) ω = (if ω e then (1 : ℝ) else 0) := by
  unfold boxEdgeOpenEvent
  by_cases h : ω e <;> simp [Set.indicator, h]

lemma dfi_wired_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (innerEdgeLE d hNm eb) := by
  set T := boxRestrictLE d hNm ⁻¹' (boxEdgeOpenEvent d N eb) with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm eb) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_ofPred_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent]

lemma dfi_free_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))
      = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) := by
  set T := boxRestrictLE d hNm ⁻¹' (boxEdgeOpenEvent d N eb) with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm eb) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_ofPred_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent]

/-! ## B. Densities as limits -/

lemma dfi_tendsto_add_left (N : ℕ) : Tendsto (fun k => N + k) atTop atTop :=
  tendsto_atTop_mono (fun k => Nat.le_add_left k N) tendsto_id

lemma dfi_wired_density_eq_limit (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
  have hbase :
      Tendsto (fun k => (wiredFiniteMeasure d (N + k) hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) atTop
        (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) :=
    (wiredEdgeDensity_q2_tendsto d N eb hp hp1).comp (dfi_tendsto_add_left N)
  refine hbase.congr (fun k => ?_)
  rw [dfi_wired_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) eb hp hp1]

lemma dfi_free_density_eq_limit (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N + k)) p 2)
          (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N eb) p)) := by
  have hmass :
      Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) atTop
        (𝓝 (freeEdgeDensity d 2 (edgeIncl d N eb) p)) := by
    rw [freeEdgeDensity_q2_eq_real d N eb hp hp1]
    exact fk_free_infinite_measure N hp hp1 (boxEdgeOpenEvent_isIncreasing d N eb)
  have hbase :
      Tendsto (fun k => (freeFiniteMeasure d (N + k) hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) atTop
        (𝓝 (freeEdgeDensity d 2 (edgeIncl d N eb) p)) :=
    hmass.comp (dfi_tendsto_add_left N)
  refine hbase.congr (fun k => ?_)
  rw [dfi_free_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) eb hp hp1]

/-! ## C. One-sided bounds -/

lemma dfi_wired_per_edge_ge (N n : ℕ) (hNn : N ≤ n) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2)
          (innerEdgeLE d hNn eb) := by
  rw [← dfi_wired_finite_mass_eq_edgeMarg N n hNn eb hp hp1,
    wiredEdgeDensity_q2_eq_fkWiredLimitValue d N eb hp hp1]
  exact fk_wired_limit_le N n hNn hp hp1 (boxEdgeOpenEvent d N eb)

lemma dfi_freeEdgeDensity_eq_fkFreeLimitValue (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = fkFreeLimitValue N hp hp1 (boxEdgeOpenEvent d N eb) := by
  rw [freeEdgeDensity_q2_eq_real d N eb hp hp1]
  exact fkFreeLimit_freeInfiniteVolume_eq N hp hp1 (boxEdgeOpenEvent_isIncreasing d N eb)

lemma dfi_free_per_edge_le (N n : ℕ) (hNn : N ≤ n) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    edgeMargProb (fkProb (boxGraph d n) p 2) (innerEdgeLE d hNn eb)
      ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  rw [← dfi_free_finite_mass_eq_edgeMarg N n hNn eb hp hp1,
    dfi_freeEdgeDensity_eq_fkFreeLimitValue N eb hp hp1]
  exact fk_free_le_limit N n hNn hp hp1 (boxEdgeOpenEvent d N eb)

/-! ## D. Open-edge counts -/

/-- The number of open edges of `ω` in the finite set `E`, as a real number. -/
noncomputable def dfi_openEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ E, (if ω e then (1 : ℝ) else 0)

lemma dfi_openEdgeCount_expect {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (μ : ConfigSpace (Sym2 V) → ℝ) :
    (∑ ω : ConfigSpace (Sym2 V), dfi_openEdgeCount E ω * μ ω)
      = ∑ e ∈ E, edgeMargProb μ e := by
  unfold dfi_openEdgeCount edgeMargProb
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_mul]

lemma dfi_boxVertInclLE_injective (d : ℕ) {N n : ℕ} (hNn : N ≤ n) :
    Function.Injective (boxVertInclLE d hNn) := by
  intro x y h
  apply Subtype.ext
  have : (boxVertInclLE d hNn x : Site d) = (boxVertInclLE d hNn y : Site d) :=
    congrArg Subtype.val h
  exact this

lemma dfi_innerEdgeLE_injective (d : ℕ) {N n : ℕ} (hNn : N ≤ n) :
    Function.Injective (innerEdgeLE d hNn) :=
  Sym2.map.injective (dfi_boxVertInclLE_injective d hNn)

lemma dfi_box_density_bound_wired (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [dfi_openEdgeCount_expect]
  rw [Finset.sum_image (fun a _ b _ h => dfi_innerEdgeLE_injective d hNn h)]
  exact Finset.sum_le_sum fun eb _ => dfi_wired_per_edge_ge N n hNn eb hp hp1

lemma dfi_box_density_bound_free (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ ∑ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  rw [dfi_openEdgeCount_expect]
  rw [Finset.sum_image (fun a _ b _ h => dfi_innerEdgeLE_injective d hNn h)]
  exact Finset.sum_le_sum fun eb _ => dfi_free_per_edge_le N n hNn eb hp hp1

end FK

end StatMech
