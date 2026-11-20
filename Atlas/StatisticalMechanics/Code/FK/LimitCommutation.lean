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

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}












noncomputable def lmc_transEdgeIncl (d m : ℕ) (v : Site d) :
    Sym2 (fvs_transBoxVerts d m v) → Sym2 (Site d) :=
  Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d)








theorem lmc_transEdgeIncl_sigma_eq_smul (d m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m)) :
    lmc_transEdgeIncl d m v (Sym2.map (fvs_transEquiv d m v) eb)
      = (Multiplicative.ofAdd v) • (edgeIncl d m eb) := by
  unfold lmc_transEdgeIncl edgeIncl
  show Sym2.map _ (Sym2.map _ eb) = Sym2.map _ (Sym2.map _ eb)
  rw [Sym2.map_map, Sym2.map_map]
  congr 1
  funext x
  show (fvs_transEquiv d m v x : Site d) = Multiplicative.ofAdd v • (x : Site d)
  rw [fvs_transEquiv_val]
  show (x : Site d) + v = v + (x : Site d)
  rw [add_comm]








theorem lmc_transImage_eq_smulImage (d m : ℕ) (v : Site d) (t : Finset (Sym2 (boxVerts d m))) :
    (t.image (Sym2.map (fvs_transEquiv d m v))).image (lmc_transEdgeIncl d m v)
      = (t.image (edgeIncl d m)).image (fun e => (Multiplicative.ofAdd v) • e) := by
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  simp only [Function.comp_apply]
  exact lmc_transEdgeIncl_sigma_eq_smul d m v eb












noncomputable def lmc_transBoxMass (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb
    (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
    ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))












theorem lmc_transBoxMass_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMass v N t p m hNm
      = (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMass, med_centred_mass_lift N m hNm t hp hp1,
    ← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]







theorem lmc_transBoxMass_tendsto_centred_iv (v : Site d) (N : ℕ)
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






























theorem lmc_wiredMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
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





























theorem lmc_wiredMultiHomogeneous_of_decay (v : Site d) (N N' : ℕ)
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







theorem lmc_wiredMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : lmc_wiredPlacement hp hp1 g) :
    cdc_wiredMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, hst, hcofinal⟩ := hplace s
  subst hst
  
  exact lmc_wiredMultiHomogeneous_of_cofinal (Multiplicative.toAdd g⁻¹) N t hp hp1 hcofinal












theorem lmc_wiredPlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
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




theorem lmc_wiredMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  lmc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (lmc_wiredPlacement_one hp hp1)














theorem lmc_wiredIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), lmc_wiredPlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => lmc_wiredMultiHomogeneous hp hp1 g (hplace g))










noncomputable def lmc_transBoxMassFree (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
    ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))





theorem lmc_transBoxMassFree_eq_centred (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hNm : N ≤ m) :
    lmc_transBoxMassFree v N t p m hNm
      = (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (t.image (edgeIncl d N))) := by
  rw [lmc_transBoxMassFree, ← med_multiEvent_lift N m hNm t,
    med_free_centred_mass_eq m (t.image (innerEdgeLE d hNm)) hp hp1,
    ← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]



theorem lmc_transBoxMassFree_tendsto_centred_iv (v : Site d) (N : ℕ)
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



theorem lmc_freeMultiHomogeneous_of_cofinal (v : Site d) (N : ℕ)
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



theorem lmc_freeMultiHomogeneous {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : Multiplicative (Site d)) (hplace : lmc_freePlacement hp hp1 g) :
    cdc_freeMultiHomogeneous hp hp1 g := by
  intro s
  obtain ⟨N, t, hst, hcofinal⟩ := hplace s
  subst hst
  exact lmc_freeMultiHomogeneous_of_cofinal (Multiplicative.toAdd g⁻¹) N t hp hp1 hcofinal



theorem lmc_freePlacement_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
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



theorem lmc_freeMultiHomogeneous_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) :=
  lmc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) (lmc_freePlacement_one hp hp1)



theorem lmc_freeIV_isTranslationInvariant_of_placement {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hplace : ∀ g : Multiplicative (Site d), lmc_freePlacement hp hp1 g) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1
    (fun g _ _ _ => lmc_freeMultiHomogeneous hp hp1 g (hplace g))

end FK

end StatMech
