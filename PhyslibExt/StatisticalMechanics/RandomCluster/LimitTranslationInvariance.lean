/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MultiEdgeDecay

/-!
# Translation invariance of the infinite-volume limits from centred-box shift identities

The `q = 2` free and wired infinite-volume random-cluster measures on `ℤᵈ` are translation
invariant, provided the multi-edge open probabilities of every edge set and its translate agree in
all large centred boxes.

## i. Overview

A finite edge set and its translate by `g` both fit in a common box `Λ_N`. The finite-volume measure
on a translated box is the push-forward of the centred-box measure, so the placement identity for
the infinite-volume limit reduces to an equality of multi-edge open probabilities in large centred
boxes, the "centred shift decay" premise. Both headlines are conditional: they take as hypothesis
`hdecay`, which asks that `plc_WiredCentredShiftDecay` (resp. `plc_FreeCentredShiftDecay`) hold for
every translation `g` and every finite edge set. This premise is an exact equality in finite boxes
and is not proved here. The trivial translation `g = 1` is handled unconditionally.

## ii. Key results

- `plc_wiredIV_isTranslationInvariant_of_decay` : the wired `q = 2` limit is translation invariant,
  assuming the wired centred-shift identities `hdecay`.
- `plc_freeIV_isTranslationInvariant_of_decay` : the free `q = 2` limit is translation invariant,
  assuming the free centred-shift identities `hdecay`.
- The placement identity for the identity translation is `med_wiredPlacement_one` /
  `med_freePlacement_one` (`MultiEdgeDecay`).

## iii. Table of contents

- A. Common boxes and translated boxes
- B. Centred-shift identities
- C. Translation invariance of the limits

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}

/-! ## A. Common boxes and translated boxes -/

lemma plc_relift_image (N₀ N : ℕ) (h : N₀ ≤ N) (t₀ : Finset (Sym2 (boxVerts d N₀))) :
    (t₀.image (innerEdgeLE d h)).image (edgeIncl d N) = t₀.image (edgeIncl d N₀) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact edgeIncl_innerEdgeLE d h eb

lemma plc_common_box (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) := by
  classical
  obtain ⟨N₁, t₁, hst₁⟩ := cdc_finset_in_box s
  obtain ⟨N₂, t₂, hst₂⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  refine ⟨max N₁ N₂,
    t₁.image (innerEdgeLE d (le_max_left N₁ N₂)),
    t₂.image (innerEdgeLE d (le_max_right N₁ N₂)), ?_, ?_⟩
  · rw [hst₁, plc_relift_image N₁ (max N₁ N₂) (le_max_left N₁ N₂) t₁]
  · rw [hst₂, plc_relift_image N₂ (max N₁ N₂) (le_max_right N₁ N₂) t₂]

lemma plc_htrans_iff_centred_shift_wired (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} :
    (med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
        = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
            (t'.image (innerEdgeLE d hNm)))
      ↔ (med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
            (t.image (innerEdgeLE d hNm))
          = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
              (t'.image (innerEdgeLE d hNm))) := by
  rw [← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]

lemma plc_htrans_iff_centred_shift_free (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} :
    (med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
          ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
        = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))
      ↔ (med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) := by
  rw [← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]

/-! ## B. Centred-shift identities -/

/-- For all large centred boxes `Λₘ`, the wired `q = 2` probabilities that all edges of `t` are
open and that all edges of `t'` are open coincide. -/
def plc_WiredCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
        (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t'.image (innerEdgeLE d hNm))

/-- For all large centred boxes `Λₘ`, the free `q = 2` probabilities that all edges of `t` are
open and that all edges of `t'` are open coincide. -/
def plc_FreeCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))

lemma plc_wiredPlacement_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d))
    (hdecay : ∀ s : Finset (Sym2 (Site d)),
      ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
        s = t.image (edgeIncl d N)
          ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
          ∧ plc_WiredCentredShiftDecay hp hp1 N t t') :
    med_wiredPlacement hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', hres⟩ := hdecay s
  refine ⟨N, t, t', hst, hst', ?_⟩
  filter_upwards [hres] with m hm hNm
  rw [plc_htrans_iff_centred_shift_wired m (Multiplicative.toAdd g) N hNm t t']
  exact hm hNm

lemma plc_freePlacement_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d))
    (hdecay : ∀ s : Finset (Sym2 (Site d)),
      ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
        s = t.image (edgeIncl d N)
          ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
          ∧ plc_FreeCentredShiftDecay hp hp1 N t t') :
    med_freePlacement hp hp1 g := by
  intro s
  obtain ⟨N, t, t', hst, hst', hres⟩ := hdecay s
  refine ⟨N, t, t', hst, hst', ?_⟩
  filter_upwards [hres] with m hm hNm
  rw [plc_htrans_iff_centred_shift_free m (Multiplicative.toAdd g) N hNm t t']
  exact hm hNm

lemma plc_wiredCentredShiftDecay_refl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) :
    plc_WiredCentredShiftDecay hp hp1 N t t :=
  Filter.Eventually.of_forall fun _ _ => rfl

lemma plc_freeCentredShiftDecay_refl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) :
    plc_FreeCentredShiftDecay hp hp1 N t t :=
  Filter.Eventually.of_forall fun _ _ => rfl

lemma plc_wiredCentredShiftDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ plc_WiredCentredShiftDecay hp hp1 N t t' := by
  classical
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, plc_wiredCentredShiftDecay_refl hp hp1 N t⟩
  rw [hst, Finset.image_image]
  refine Finset.image_congr fun e _ => ?_
  simp only [Function.comp_apply, inv_one, one_smul]

lemma plc_freeCentredShiftDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => (1 : Multiplicative (Site d))⁻¹ • e) = t'.image (edgeIncl d N)
        ∧ plc_FreeCentredShiftDecay hp hp1 N t t' := by
  classical
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box s
  refine ⟨N, t, t, hst, ?_, plc_freeCentredShiftDecay_refl hp hp1 N t⟩
  rw [hst, Finset.image_image]
  refine Finset.image_congr fun e _ => ?_
  simp only [Function.comp_apply, inv_one, one_smul]

/-! ## C. Translation invariance of the limits -/

/-- The wired `q = 2` infinite-volume measure is translation invariant, assuming that for every
translation and every finite edge set the wired centred-shift identity `hdecay` holds. -/
theorem plc_wiredIV_isTranslationInvariant_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : ∀ (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))),
      ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
        s = t.image (edgeIncl d N)
          ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
          ∧ plc_WiredCentredShiftDecay hp hp1 N t t') :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  med_wiredIV_isTranslationInvariant_of_placement hp hp1
    (fun g => plc_wiredPlacement_of_decay hp hp1 g (hdecay g))

/-- The free `q = 2` infinite-volume measure is translation invariant, assuming that for every
translation and every finite edge set the free centred-shift identity `hdecay` holds. -/
theorem plc_freeIV_isTranslationInvariant_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : ∀ (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))),
      ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
        s = t.image (edgeIncl d N)
          ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N)
          ∧ plc_FreeCentredShiftDecay hp hp1 N t t') :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  med_freeIV_isTranslationInvariant_of_placement hp hp1
    (fun g => plc_freePlacement_of_decay hp hp1 g (hdecay g))

end FK

end StatMech
