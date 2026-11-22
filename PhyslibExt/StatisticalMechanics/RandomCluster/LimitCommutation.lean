/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MultiEdgeDecay
/-!
# Translation invariance of the infinite-volume FK measures from box limits

Translated box marginals reduce translation invariance of the `q = 2` FK limits to one limit.

## i. Overview

Fix `p ∈ (0, 1)` and `q = 2`. The wired and free infinite-volume FK measures on `ℤ^d` are weak
limits of the finite-volume measures on the centered boxes `Λ_m = [-m, m]^d`. For a finite edge set
`t` in a box `Λ_N` and a shift `v ∈ ℤ^d`, this file compares the probability that all edges of
`t` are open under the finite-volume measure on the translated box `v + Λ_m` with the same
probability on the centered box. The two agree by translation covariance of the finite-volume
measures, so the translated box masses converge to the infinite-volume probability of `t`.

Uniqueness of limits then turns translation invariance into a statement about one limit: if the
translated box masses also converge to the infinite-volume probability of the shifted set
`v + t` (the *placement* hypothesis), the infinite-volume measure gives `t` and `v + t` the same
probability. Since the events "all edges of `s` are open" generate the cylinder σ-algebra, a
placement hypothesis for every shift gives translation invariance of the infinite-volume
measure. The identity shift satisfies the placement hypothesis unconditionally.

## ii. Key results

- `lmc_transBoxMass_tendsto_centred_iv` : translated wired box masses converge to the wired
  infinite-volume probability of the unshifted event.
- `lmc_wiredMultiHomogeneous_of_cofinal`, `lmc_wiredMultiHomogeneous_of_decay` : equality of
  the probabilities of `t` and `v + t` from a cofinal limit or from a vanishing difference.
- `lmc_wiredIV_isTranslationInvariant_of_placement` : the wired infinite-volume measure is
  translation invariant when every shift satisfies the placement hypothesis.
- `lmc_freeIV_isTranslationInvariant_of_placement` : the same for the free measure.

## iii. Table of contents

- A. Translated box edges
- B. Wired boundary condition
  - B.1. Translated box masses
  - B.2. Homogeneity from placement
- C. Free boundary condition

## iv. References

- H.-O. Georgii, O. Häggström, C. Maes, *The random geometry of equilibrium phases*, in Phase
  Transitions and Critical Phenomena 18, 2001, §4.
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

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}

/-!
## A. Translated box edges
-/

/-- The inclusion of edges of the translated box `v + Λ_m` into the edges of `ℤ^d`. -/
noncomputable def lmc_transEdgeIncl (d m : ℕ) (v : Site d) :
    Sym2 (fvs_transBoxVerts d m v) → Sym2 (Site d) :=
  Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d)

/-- Including a translated box edge equals shifting the included centered box edge by `v`. -/
lemma lmc_transEdgeIncl_sigma_eq_smul (d m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m)) :
    lmc_transEdgeIncl d m v (Sym2.map (fvs_transEquiv d m v) eb)
      = (Multiplicative.ofAdd v) • (edgeIncl d m eb) := by
  unfold lmc_transEdgeIncl edgeIncl
  change Sym2.map _ (Sym2.map _ eb) = Sym2.map _ (Sym2.map _ eb)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1
  funext x
  change (fvs_transEquiv d m v x : Site d) = Multiplicative.ofAdd v • (x : Site d)
  rw [fvs_transEquiv_val]
  change (x : Site d) + v = v + (x : Site d)
  rw [add_comm]

/-- The image of a translated edge set in `ℤ^d` is the shift by `v` of the image of the centered
set. -/
lemma lmc_transImage_eq_smulImage (d m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m))) :
    (t.image (Sym2.map (fvs_transEquiv d m v))).image (lmc_transEdgeIncl d m v)
      = (t.image (edgeIncl d m)).image (fun e => (Multiplicative.ofAdd v) • e) := by
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  simp only [Function.comp_apply]
  exact lmc_transEdgeIncl_sigma_eq_smul d m v eb

/-!
## B. Wired boundary condition

### B.1. Translated box masses
-/

/-- The probability, under the wired `q = 2` FK measure on the translated box `v + Λ_m`, that all
edges of the translated copy of `t ⊆ E(Λ_N)` are open. -/
noncomputable def lmc_transBoxMass (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
    ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))

/-- The translated wired box mass equals the probability of the unshifted event under the wired
finite-volume measure on the centered box `Λ_m`. -/
lemma lmc_transBoxMass_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMass v N t p m hNm
      = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMass, med_centred_mass_lift N m hNm t hp hp1,
    ← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]

/-- The translated wired box masses converge to the wired infinite-volume probability that all
edges of `t` are open. -/
lemma lmc_transBoxMass_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hcentred := (med_centred_tendsto_iv N t hp hp1).comp (tendsto_add_atTop_nat N)
  refine hcentred.congr (fun m => ?_)
  simp only [Function.comp_apply]
  rw [show m + N = N + m from Nat.add_comm m N]
  exact (lmc_transBoxMass_eq_centred v N t hp hp1 (N + m) (Nat.le_add_right N m)).symm

/-- If the translated wired box masses also converge to the wired infinite-volume probability of
the shifted set `v + t`, the wired infinite-volume measure gives `t` and `v + t` the same
probability. -/
lemma lmc_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m))
        atTop
        (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent
                ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) :=
  tendsto_nhds_unique (lmc_transBoxMass_tendsto_centred_iv v N t hp hp1) hcofinal

/-- If the translated wired box masses differ from the centered box masses of a set `t'` with `v +
t = t'` by a sequence tending to zero, the wired infinite-volume measure gives `t` and `v + t`
the same probability. -/
lemma lmc_wiredMultiHomogeneous_of_decay (v : Site d) (N N' : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) (t' : Finset (Sym2 (boxVerts d N')))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hst' : (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)
        = t'.image (edgeIncl d N'))
    (hdecay : Tendsto
        (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)
          - (wiredFiniteMeasure d (N' + m) hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real
                (cdc_multiOpenEvent (t'.image (edgeIncl d N')))) atTop (𝓝 0)) :
    (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
  rw [hst']
  have hC := lmc_transBoxMass_tendsto_centred_iv v N t hp hp1
  have hC' := (med_centred_tendsto_iv N' t' hp hp1).comp (tendsto_add_atTop_nat N')
  have hsum : Tendsto (fun m : ℕ => lmc_transBoxMass v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t'.image (edgeIncl d N'))))) := by
    have hcomb := hdecay.add hC'
    simp only [zero_add] at hcomb
    refine hcomb.congr (fun m => ?_)
    simp only [Function.comp_apply]
    rw [show m + N' = N' + m from Nat.add_comm m N', sub_add_cancel]
  exact tendsto_nhds_unique hC hsum

/-!
### B.2. Homogeneity from placement
-/

/-- The placement hypothesis for the shift `g`: every finite edge set lies in a box whose
translated wired box masses converge to the wired infinite-volume probability of the set
shifted by `g⁻¹`. -/
def lmc_wiredPlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ Tendsto
            (fun m : ℕ => lmc_transBoxMass (Multiplicative.toAdd g⁻¹) N t p (N + m)
              (Nat.le_add_right N m)) atTop
            (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))))

/-- The placement hypothesis for `g` gives `g`-homogeneity of the wired infinite-volume measure on
all events "every edge of `s` is open". -/
lemma lmc_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : lmc_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, hst, hcofinal⟩ := hplace s
  subst hst
  exact lmc_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g⁻¹) N t hp hp1 hcofinal

/-- The identity shift satisfies the wired placement hypothesis. -/
lemma lmc_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lmc_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, hst, ?_⟩
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t.image (edgeIncl d N) := by
    rw [hst, Finset.image_image]
    refine Finset.image_congr fun eb _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  rw [hs]
  exact lmc_transBoxMass_tendsto_centred_iv (Multiplicative.toAdd (1 : Multiplicative (Site d))⁻¹)
    N t hp hp1

/-- The wired infinite-volume measure is homogeneous under the identity shift. -/
lemma lmc_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  lmc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (lmc_wiredPlacement_one hp hp1)

/-- The wired `q = 2` infinite-volume FK measure on `ℤ^d` is translation invariant if every shift
satisfies the wired placement hypothesis. -/
lemma lmc_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => lmc_wiredMultiHomogeneous hp hp1 g (hplace g))

/-!
## C. Free boundary condition
-/

/-- The probability, under the free `q = 2` FK measure on the translated box `v + Λ_m`, that all
edges of the translated copy of `t ⊆ E(Λ_N)` are open. -/
noncomputable def lmc_transBoxMassFree (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
    ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))

/-- The translated free box mass equals the probability of the unshifted event under the free
finite-volume measure on the centered box `Λ_m`. -/
lemma lmc_transBoxMassFree_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMassFree v N t p m hNm
      = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMassFree, ← med_multiEvent_lift N m hNm t,
    med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1,
    ← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]

/-- The translated free box masses converge to the free infinite-volume probability that all edges
of `t` are open. -/
lemma lmc_transBoxMassFree_tendsto_centred_iv (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m)) atTop
      (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
  have hcentred := (med_free_centred_tendsto_iv N t hp hp1).comp (tendsto_add_atTop_nat N)
  refine hcentred.congr (fun m => ?_)
  simp only [Function.comp_apply]
  rw [show m + N = N + m from Nat.add_comm m N]
  exact (lmc_transBoxMassFree_eq_centred v N t hp hp1 (N + m) (Nat.le_add_right N m)).symm

/-- If the translated free box masses also converge to the free infinite-volume probability of the
shifted set `v + t`, the free infinite-volume measure gives `t` and `v + t` the same
probability. -/
lemma lmc_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofinal : Tendsto (fun m : ℕ => lmc_transBoxMassFree v N t p (N + m) (Nat.le_add_right N m))
        atTop
        (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (cdc_multiOpenEvent
                ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)))))) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (cdc_multiOpenEvent (t.image (edgeIncl d N)))
      = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent
              ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) :=
  tendsto_nhds_unique (lmc_transBoxMassFree_tendsto_centred_iv v N t hp hp1) hcofinal

/-- The placement hypothesis for the shift `g` and the free measure: every finite edge set lies in
a box whose translated free box masses converge to the free infinite-volume probability of the
set shifted by `g⁻¹`. -/
def lmc_freePlacement {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : Multiplicative (Site d)) : Prop :=
  ∀ s : Finset (Sym2 (Site d)),
    ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ Tendsto
            (fun m : ℕ => lmc_transBoxMassFree (Multiplicative.toAdd g⁻¹) N t p (N + m)
              (Nat.le_add_right N m)) atTop
            (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real
                  (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))))

/-- The free placement hypothesis for `g` gives `g`-homogeneity of the free infinite-volume
measure on all events "every edge of `s` is open". -/
lemma lmc_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : lmc_freePlacement hp hp1 g) :
    cdc_freeMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, hst, hcofinal⟩ := hplace s
  subst hst
  exact lmc_freeMultiHomogeneous_of_cofinal (Multiplicative.toAdd g⁻¹) N t hp hp1 hcofinal

/-- The identity shift satisfies the free placement hypothesis. -/
lemma lmc_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    lmc_freePlacement hp hp1 (1 : Multiplicative (Site d)) := by
  intro s
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, hst, ?_⟩
  have hs : s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t.image (edgeIncl d N) := by
    rw [hst, Finset.image_image]
    refine Finset.image_congr fun eb _ => ?_
    simp only [Function.comp_apply, inv_one, one_smul]
  rw [hs]
  exact lmc_transBoxMassFree_tendsto_centred_iv
    (Multiplicative.toAdd (1 : Multiplicative (Site d))⁻¹) N t hp hp1

/-- The free infinite-volume measure is homogeneous under the identity shift. -/
lemma lmc_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  lmc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (lmc_freePlacement_one hp hp1)

/-- The free `q = 2` infinite-volume FK measure on `ℤ^d` is translation invariant if every shift
satisfies the free placement hypothesis. -/
lemma lmc_freeIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), lmc_freePlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => lmc_freeMultiHomogeneous hp hp1 g (hplace g))

end FK

end StatMech
