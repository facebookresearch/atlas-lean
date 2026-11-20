/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.FK.MultiEdgeDecay

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












theorem plc_relift_image (N₀ N : ℕ) (h : N₀ ≤ N) (t₀ : Finset (Sym2 (boxVerts d N₀))) :
    (t₀.image (innerEdgeLE d h)).image (edgeIncl d N) = t₀.image (edgeIncl d N₀) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N₀ N h eb






theorem plc_common_box (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))) :
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















theorem plc_htrans_iff_centred_shift_wired (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
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



theorem plc_htrans_iff_centred_shift_free (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} :
    (med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
          ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
        = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))
      ↔ (med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) := by
  rw [← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]














def plc_WiredCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
        (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
          (t'.image (innerEdgeLE d hNm))



def plc_FreeCentredShiftDecay {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t t' : Finset (Sym2 (boxVerts d N))) : Prop :=
  ∀ᶠ m in atTop, ∀ (hNm : N ≤ m),
    med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
      = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))











theorem plc_wiredPlacement_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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



theorem plc_freePlacement_of_decay {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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










theorem plc_wiredCentredShiftDecay_refl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) :
    plc_WiredCentredShiftDecay hp hp1 N t t :=
  Filter.Eventually.of_forall fun _ _ => rfl



theorem plc_freeCentredShiftDecay_refl {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N : ℕ)
    (t : Finset (Sym2 (boxVerts d N))) :
    plc_FreeCentredShiftDecay hp hp1 N t t :=
  Filter.Eventually.of_forall fun _ _ => rfl




theorem plc_wiredCentredShiftDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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



theorem plc_freeCentredShiftDecay_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
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




theorem plc_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_wiredPlacement hp hp1 (1 : Multiplicative (Site d)) :=
  plc_wiredPlacement_of_decay hp hp1 (1 : Multiplicative (Site d))
    (fun s => plc_wiredCentredShiftDecay_one hp hp1 s)



theorem plc_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    med_freePlacement hp hp1 (1 : Multiplicative (Site d)) :=
  plc_freePlacement_of_decay hp hp1 (1 : Multiplicative (Site d))
    (fun s => plc_freeCentredShiftDecay_one hp hp1 s)













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
