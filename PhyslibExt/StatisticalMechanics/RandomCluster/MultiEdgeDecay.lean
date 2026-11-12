/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvarianceFromHomogeneity
public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreCarrier
/-!
# Multi-edge events and translation invariance of `q = 2` FK measures

Probabilities that all edges of a finite set are open, under finite-volume and infinite-volume
FK measures, and their behaviour under translation of boxes.

## i. Overview

For a finite edge set `t`, let `A_t` be the event that every edge of `t` is open. Under the free
or wired `q = 2` box measure on `Λ_m`, the probability of `A_t` is the finite sum
`med_multiMassProb`; it equals the probability of the corresponding event of `ℤ^d` under the box
measure pushed to the configuration space of `ℤ^d`, and converges to the infinite-volume
probability as `m → ∞`. Translation covariance of finite-volume measures says that the mass of
`t` in `Λ_m` equals the mass of `t + v` in the translated box `v + Λ_m`.

The events `A_s` generate the cylinder σ-algebra, so an infinite-volume measure is translation
invariant once `A_s` and `A_{s - g}` have the same probability for every finite `s` and shift
`g`. A *placement* of `s` for `g` writes `s` and `s - g` as images of box edge sets `t`, `t'` of a
common box with eventually equal translated and centered masses; placements for every `g` give
translation invariance of the free and wired infinite-volume measures. The identity shift has a
placement unconditionally.

## ii. Key results

- `med_genericMultiOpenEvent`, `med_multiMassProb` : the event `A_t` and its finite-volume mass.
- `med_centred_eq_translated_wired`, `med_centred_eq_translated_free` : translation covariance of
  multi-edge masses.
- `med_wiredMultiHomogeneous_of_cofinal` : equal infinite-volume probabilities of `A_t` and
  `A_{t'}` from eventually equal translated masses.
- `med_wiredPlacement`, `med_freePlacement` : the placement hypothesis.
- `med_wiredIV_isTranslationInvariant_of_placement`,
  `med_freeIV_isTranslationInvariant_of_placement` : translation invariance from placements.

## iii. Table of contents

- A. Multi-edge events
- B. Finite-volume masses
- C. Translation covariance
- D. Limits along boxes
- E. The off-centre multi-edge carrier
- F. Homogeneity from translated masses
- G. Placements and translation invariance

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}

/-!
## A. Multi-edge events
-/

/-- The event `A_t` that every edge of the finite set `t` is open. On box configurations it is
`cdc_boxMultiOpenEvent` (`med_boxMultiOpenEvent_eq`). -/
def med_genericMultiOpenEvent {V : Type*} (t : Finset (Sym2 V)) :
    Set (ConfigSpace (Sym2 V)) :=
  {ω | ∀ e ∈ t, ω e = true}

lemma med_boxMultiOpenEvent_eq (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t := rfl

lemma med_genericMultiOpenEvent_increasing {V : Type*} (t : Finset (Sym2 V)) :
    IsIncreasing (med_genericMultiOpenEvent t) := by
  intro a b hab ha e he
  have hle := hab e
  rw [ha e he] at hle
  exact le_antisymm (by simp) hle

lemma med_reCfgIso_preimage {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (σ : V ≃ W) (t : Finset (Sym2 V)) :
    reCfgIso σ ⁻¹' (med_genericMultiOpenEvent t)
      = med_genericMultiOpenEvent (t.image (Sym2.map σ)) := by
  ext ω
  simp only [Set.mem_preimage, med_genericMultiOpenEvent, Set.mem_ofPred_eq, reCfgIso,
    Finset.forall_mem_image]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## B. Finite-volume masses
-/

/-- The mass `∑_ω 1_{A_t}(ω) μ(ω)` of the event that every edge of `t` is open, for a weight
function `μ` on a finite configuration space; it is `eventMassProb μ A_t`
(`med_multiMassProb_eq_eventMassProb`). -/
noncomputable def med_multiMassProb (μ : ConfigSpace (Sym2 V) → ℝ) (t : Finset (Sym2 V)) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V),
    (med_genericMultiOpenEvent t).indicator (fun _ => (1 : ℝ)) ω * μ ω

lemma med_multiMassProb_eq_eventMassProb (μ : ConfigSpace (Sym2 V) → ℝ) (t : Finset (Sym2 V)) :
    med_multiMassProb μ t = eventMassProb μ (med_genericMultiOpenEvent t) := rfl

/-- The wired box measure on `Λ_m`, pushed to `ℤ^d`, gives `A_t` the box mass of `t`. -/
lemma med_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (cdc_boxMultiOpenEvent m t) hmeas]
  rfl

/-- The free box measure on `Λ_m`, pushed to `ℤ^d`, gives `A_t` the box mass of `t`. -/
lemma med_free_centred_mass_eq (m : ℕ) (t : Finset (Sym2 (boxVerts d m))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d m)))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) t := by
  rw [cdc_multiOpenEvent_image_eq_boxRestrict m t]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' (cdc_boxMultiOpenEvent m t)) :=
    (continuous_boxRestrict d m).measurable (MeasurableSet.of_discrete)
  rw [freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (by norm_num) (cdc_boxMultiOpenEvent m t)
    hmeas]
  rfl

/-!
## C. Translation covariance
-/

/-- The wired mass of `t` in `Λ_m` equals the wired mass of `t + v` in `v + Λ_m`. -/
lemma med_centred_eq_translated_wired (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) t
      = med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
    (fun ω => fvs_wiredFkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
      (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]

/-- The free mass of `t` in `Λ_m` equals the free mass of `t + v` in `v + Λ_m`. -/
lemma med_centred_eq_translated_free (m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m)))
    {p : ℝ} :
    med_multiMassProb (fkProb (boxGraph d m) p 2) t
      = med_multiMassProb
          (fkProb (fvs_transBoxGraph d m v) p 2)
          (t.image (Sym2.map (fvs_transEquiv d m v))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (fvs_transEquiv d m v)
    (fkProb (boxGraph d m) p 2)
    (fkProb (fvs_transBoxGraph d m v) p 2)
    (fun ω => fvs_fkProb_reCfgIso (boxGraph d m) (fvs_transBoxGraph d m v)
      (fvs_transEquiv d m v) (fvs_transEquiv_adj d m v) p 2 ω)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [med_reCfgIso_preimage (fvs_transEquiv d m v) t]

/-!
## D. Limits along boxes
-/

/-- Restatement of `cdc_wired_multiOpenEvent_tendsto`: the wired box probabilities of `A_t`
converge to the wired infinite-volume probability. -/
lemma med_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_wired_multiOpenEvent_tendsto N t hp hp1

/-- Restatement of `cdc_free_multiOpenEvent_tendsto`: the free box probabilities of `A_t`
converge to the free infinite-volume probability. -/
lemma med_free_centred_tendsto_iv (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) :=
  cdc_free_multiOpenEvent_tendsto N t hp hp1

lemma med_multiEvent_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N))) :
    cdc_multiOpenEvent ((t.image (innerEdgeLE d hNm)).image (edgeIncl d m))
      = cdc_multiOpenEvent (t.image (edgeIncl d N)) := by
  congr 1
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact edgeIncl_innerEdgeLE d hNm eb

lemma med_centred_mass_lift (N m : ℕ) (hNm : N ≤ m) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t.image (innerEdgeLE d hNm)) := by
  rw [← med_multiEvent_lift N m hNm t, med_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1]

/-!
## E. The off-centre multi-edge carrier
-/

/-- The difference between the wired mass of `t` in `Λ_m` and the wired mass of `t + v` in
`v + Λ_m`; it vanishes by translation covariance. -/
noncomputable def med_offCentreMultiCarrier (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
      (t.image (innerEdgeLE d hNm))
    - med_multiMassProb
        (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
        ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))

lemma med_offCentreMultiCarrier_eq_zero (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) :
    med_offCentreMultiCarrier v N t p m hNm = 0 := by
  unfold med_offCentreMultiCarrier
  rw [← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm)), sub_self]

lemma med_offCentreMultiCarrier_squeeze (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) :
    Tendsto (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 0) := by
  have hzero : (fun m : ℕ => med_offCentreMultiCarrier v N t p (N + m) (Nat.le_add_right N m))
      = fun _ => (0 : ℝ) := by
    funext m; exact med_offCentreMultiCarrier_eq_zero v N t p (N + m) (Nat.le_add_right N m)
  rw [hzero]
  exact tendsto_const_nhds

/-!
## F. Homogeneity from translated masses
-/

/-- If the wired mass of `t + v` in `v + Λ_m` eventually equals the wired mass of `t'` in `Λ_m`,
the wired infinite-volume measure gives `A_t` and `A_{t'}` the same probability. -/
lemma med_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb
            (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
              (t'.image (innerEdgeLE d hNm))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  have hCs := med_centred_tendsto_iv N t hp hp1
  have hCs' := med_centred_tendsto_iv N t' hp hp1
  have heqradius : ∀ᶠ m in atTop,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    rw [med_centred_mass_lift N m hNm t hp hp1, med_centred_mass_lift N m hNm t' hp hp1]
    rw [med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]
    exact htr hNm
  have hCs_to_s' : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'

/-- If the free mass of `t + v` in `v + Λ_m` eventually equals the free mass of `t'` in `Λ_m`,
the free infinite-volume measure gives `A_t` and `A_{t'}` the same probability. -/
lemma med_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htrans : ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
        med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
            ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
  have hCs := med_free_centred_tendsto_iv N t hp hp1
  have hCs' := med_free_centred_tendsto_iv N t' hp hp1
  have heqradius : ∀ᶠ m in atTop,
      (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N)))
        = (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent (t'.image (edgeIncl d N))) := by
    filter_upwards [htrans, eventually_ge_atTop N] with m htr hNm
    rw [← med_multiEvent_lift N m hNm t, med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm))
        hp hp1,
      ← med_multiEvent_lift N m hNm t', med_free_centred_mass_eq m (t'.image (innerEdgeLE d hNm))
        hp hp1,
      med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]
    exact htr hNm
  have hCs_to_s' : Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N))))) :=
    hCs'.congr' (heqradius.mono fun m h => h.symm)
  exact tendsto_nhds_unique hCs hCs_to_s'

/-!
## G. Placements and translation invariance
-/

/-- A wired placement for the shift `g`: every finite edge set `s` and its shift `g⁻¹ s` are
images of box edge sets `t`, `t'` of a common box `Λ_N` such that the wired mass of `t + g` in
`g + Λ_m` eventually equals the wired mass of `t'` in `Λ_m`. See also `lmc_wiredPlacement`. -/
def med_wiredPlacement {p : ℝ} (_hp : 0 < p) (_hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb
                (wiredFkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g))
                  (fvs_transBoxBoundary d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
                  (t'.image (innerEdgeLE d hNm)))

/-- A free placement for the shift `g`, defined as `med_wiredPlacement` with free masses. -/
def med_freePlacement {p : ℝ} (_hp : 0 < p) (_hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ (∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
            med_multiMassProb (fkProb (fvs_transBoxGraph d m (Multiplicative.toAdd g)) p 2)
                ((t.image (innerEdgeLE d hNm)).image
                  (Sym2.map (fvs_transEquiv d m (Multiplicative.toAdd g))))
              = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))

lemma med_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans

lemma med_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : med_freePlacement hp hp1 g) :
    cdc_freeMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', htrans⟩ := hplace s
  rw [show s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) from hst', hst]
  exact med_freeMultiHomogeneous_of_cofinal (Multiplicative.toAdd g) N t t' hp hp1 htrans

lemma med_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_wired m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm

lemma med_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, ?_⟩
  · rw [hst, Finset.image_image]
    refine Finset.image_congr fun e _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  · refine Filter.Eventually.of_forall fun m hNm => ?_
    exact (med_centred_eq_translated_free m (Multiplicative.toAdd (1 : Multiplicative (Site d)))
      (t.image (innerEdgeLE d hNm))).symm

/-- The wired infinite-volume `q = 2` measure is translation invariant if every shift has a wired
placement. See also `flc_wiredIV_isTranslationInvariant`, which proves invariance without
hypotheses. -/
lemma med_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_wiredMultiHomogeneous hp hp1 g (hplace g))

/-- The free infinite-volume `q = 2` measure is translation invariant if every shift has a free
placement. See also `bdp_freeIV_isTranslationInvariant`, which proves invariance without
hypotheses. -/
lemma med_freeIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), med_freePlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => med_freeMultiHomogeneous hp hp1 g (hplace g))

end FK

end StatMech
