/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.IsingPlusTIFromPlacement
import Code.FK.FKGeneralQTranslation

open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal

namespace StatMech.Ising

open ConfigSpace FK Lattice Percolation

variable {d : ℕ}


noncomputable def gvMinusMeasure (S : Finset (Site d)) (beta h : ℝ) :
    Measure (ConfigSpace (Site d)) :=
  gvMeasure (minusField d) S beta h

instance gvMinusMeasure_isProbabilityMeasure
    (S : Finset (Site d)) (beta h : ℝ) :
    IsProbabilityMeasure (gvMinusMeasure S beta h) :=
  gvMeasure_isProbabilityMeasure _ S beta h


theorem gv_minusField_le (eta : ConfigSpace (Site d)) :
    minusField d ≤ eta := by
  intro x
  simp [minusField]


theorem gvMeasure_minusField_le
    (S : Finset (Site d)) {beta : ℝ} (hbeta : 0 ≤ beta)
    {h : ℝ} (hh : 0 ≤ h) (eta : ConfigSpace (Site d))
    {A : Set (ConfigSpace (Site d))} (hA : MeasurableSet A)
    (hAinc : IsIncreasing A) :
    (gvMeasure (minusField d) S beta h).real A ≤
      (gvMeasure eta S beta h).real A :=
  gvMeasure_dominated S hbeta hh (minusField d) eta
    (gv_minusField_le eta) hA hAinc


theorem iptm_gv_crossbox_dom
    {Sin Sout : Finset (Site d)} (hsub : Sin ⊆ Sout)
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A)
    (hAinc : IsIncreasing A) :
    (gvMinusMeasure Sin beta h).real A ≤
      (gvMinusMeasure Sout beta h).real A := by
  let g0 : ConfigSpace (Site d) → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hcds := gv_consistency_double_sum hsub (minusField d) beta h g0
  have hpm : (gvMinusMeasure Sout beta h).real A =
      ∑ sigma : {x // x ∈ Sout} → Bool,
        gvProb (minusField d) Sout beta h sigma *
          g0 (gvGlue (minusField d) Sout sigma) := by
    rw [gvMinusMeasure,
      gvMeasure_real_eq (minusField d) Sout beta h hAmeas]
  rw [hpm, ← hcds]
  have hterm : ∀ sigma : {x // x ∈ Sout} → Bool,
      gvProb (minusField d) Sout beta h sigma *
          (gvMinusMeasure Sin beta h).real A ≤
        gvProb (minusField d) Sout beta h sigma *
          ∑ tau : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (minusField d) Sout sigma) Sin beta h tau *
              g0 (gvGlue (gvGlue (minusField d) Sout sigma) Sin tau) := by
    intro sigma
    apply mul_le_mul_of_nonneg_left _
      (gvProb_nonneg (minusField d) Sout beta h sigma)
    have hinner :
        (∑ tau : {x // x ∈ Sin} → Bool,
          gvProb (gvGlue (minusField d) Sout sigma) Sin beta h tau *
            g0 (gvGlue (gvGlue (minusField d) Sout sigma) Sin tau)) =
          (gvMeasure (gvGlue (minusField d) Sout sigma) Sin beta h).real A :=
      (gvMeasure_real_eq (gvGlue (minusField d) Sout sigma)
        Sin beta h hAmeas).symm
    rw [hinner]
    exact gvMeasure_minusField_le Sin hbeta hh
      (gvGlue (minusField d) Sout sigma) hAmeas hAinc
  calc
    (gvMinusMeasure Sin beta h).real A =
        ∑ sigma : {x // x ∈ Sout} → Bool,
          gvProb (minusField d) Sout beta h sigma *
            (gvMinusMeasure Sin beta h).real A := by
      rw [← Finset.sum_mul,
        gvProb_sum_eq_one (minusField d) Sout beta h, one_mul]
    _ ≤ ∑ sigma : {x // x ∈ Sout} → Bool,
        gvProb (minusField d) Sout beta h sigma *
          ∑ tau : {x // x ∈ Sin} → Bool,
            gvProb (gvGlue (minusField d) Sout sigma) Sin beta h tau *
              g0 (gvGlue (gvGlue (minusField d) Sout sigma) Sin tau) :=
      Finset.sum_le_sum (fun sigma _ => hterm sigma)


theorem iptm_gvMinusMeasure_eq_minusMeasure (n : ℕ) (beta h : ℝ) :
    gvMinusMeasure (boxFinset d n) beta h =
      (minusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
  rw [gvMinusMeasure, iptp_gvMeasure_eq_fvMeasure]
  rfl


theorem iptm_gvGlue_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (tau : {x // x ∈ S} → Bool) :
    shift g (gvGlue (minusField d) S tau) =
      gvGlue (minusField d) (S.image (fun x => g • x))
        (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) := by
  funext x
  rw [shift_apply]
  by_cases hx : x ∈ S.image (fun x => g • x)
  · have hinv : g⁻¹ • x ∈ S := by
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp hx
      rw [← hzeq, inv_smul_smul]
      exact hz
    rw [gvGlue_mem _ _ _ hx, gvGlue_mem _ _ _ hinv]
    congr 1
  · have hinv : g⁻¹ • x ∉ S := by
      intro hc
      apply hx
      rw [← smul_inv_smul g x]
      exact Finset.mem_image_of_mem _ hc
    rw [gvGlue_not_mem _ _ _ hx, gvGlue_not_mem _ _ _ hinv]
    simp [minusField]


theorem iptm_gvEnergy_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (h : ℝ)
    (tau : {x // x ∈ S} → Bool) :
    gvEnergy (minusField d) (S.image (fun x => g • x)) h
        (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) =
      gvEnergy (minusField d) S h tau := by
  unfold gvEnergy
  rw [← iptm_gvGlue_shift g S tau]
  congr 1
  · rw [iptp_gvBondTouch_image,
      Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    congr 1
    exact Finset.sum_congr rfl
      (fun e _ => iptp_bond_shift g (gvGlue (minusField d) S tau) e)
  · congr 1
    rw [Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)]
    exact Finset.sum_congr rfl
      (fun x _ => iptp_spin_shift g (gvGlue (minusField d) S tau) x)

theorem iptm_gvWeight_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (beta h : ℝ)
    (tau : {x // x ∈ S} → Bool) :
    gvWeight (minusField d) (S.image (fun x => g • x)) beta h
        (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) =
      gvWeight (minusField d) S beta h tau := by
  unfold gvWeight
  rw [iptm_gvEnergy_shift]

theorem iptm_gvZ_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (beta h : ℝ) :
    gvZ (minusField d) (S.image (fun x => g • x)) beta h =
      gvZ (minusField d) S beta h := by
  unfold gvZ
  rw [← Equiv.sum_comp
    (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun tau => gvWeight (minusField d)
      (S.image (fun x => g • x)) beta h tau)]
  refine Finset.sum_congr rfl (fun tau _ => ?_)
  rw [← iptm_gvWeight_shift g S beta h tau]
  rfl

theorem iptm_gvProb_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (beta h : ℝ)
    (tau : {x // x ∈ S} → Bool) :
    gvProb (minusField d) (S.image (fun x => g • x)) beta h
        (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) =
      gvProb (minusField d) S beta h tau := by
  unfold gvProb
  rw [iptm_gvWeight_shift, iptm_gvZ_shift]


theorem iptm_gvMeasure_map_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (beta h : ℝ) :
    Measure.map (shift g) (gvMinusMeasure S beta h) =
      gvMinusMeasure (S.image (fun x => g • x)) beta h := by
  unfold gvMinusMeasure gvMeasure
  rw [iptp_map_sum_aux _ (measurable_shift g)]
  rw [← Equiv.sum_comp
    (Equiv.arrowCongr (iptp_transInteriorEquiv g S) (Equiv.refl Bool))
    (fun tau => ENNReal.ofReal
      (gvProb (minusField d) (S.image (fun x => g • x)) beta h tau) •
        Measure.dirac
          (gvGlue (minusField d) (S.image (fun x => g • x)) tau))]
  refine Finset.sum_congr rfl (fun tau _ => ?_)
  rw [Measure.map_smul,
    Measure.map_dirac (gvGlue (minusField d) S tau)]
  rw [show gvProb (minusField d) (S.image (fun x => g • x)) beta h
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S)
          (Equiv.refl Bool)) tau) =
      gvProb (minusField d) S beta h tau from
        iptm_gvProb_shift g S beta h tau,
    show gvGlue (minusField d) (S.image (fun x => g • x))
        ((Equiv.arrowCongr (iptp_transInteriorEquiv g S)
          (Equiv.refl Bool)) tau) =
      shift g (gvGlue (minusField d) S tau) from
        (iptm_gvGlue_shift g S tau).symm]


theorem iptm_gvMinus_real_shift
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (beta h : ℝ)
    (T : Finset (Site d)) :
    (gvMinusMeasure (S.image (fun x => g • x)) beta h).real
        (fmu_multiOpen T) =
      (gvMinusMeasure S beta h).real
        (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
  rw [← iptm_gvMeasure_map_shift g S beta h, Measure.real,
    Measure.map_apply (measurable_shift g) (fmu_multiOpen_measurable T),
    ← fmu_shift_multiOpen g T]
  rfl


theorem iptm_minus_multiOpen_monotone
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    (T : Finset (Site d)) {n m : ℕ} (hnm : n ≤ m) :
    (minusMeasure d n beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T) ≤
      (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T) := by
  rw [← iptm_gvMinusMeasure_eq_minusMeasure n beta h,
    ← iptm_gvMinusMeasure_eq_minusMeasure m beta h]
  exact iptm_gv_crossbox_dom (fun x hx =>
      mem_boxFinset.mpr (box_mono d hnm (mem_boxFinset.mp hx))) hbeta hh
    (fmu_multiOpen_measurable T) (fmu_multiOpen_isIncreasing T)


theorem iptm_minus_multiOpen_full_tendsto
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    (T : Finset (Site d)) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => minusMeasure d (phi n) beta h) (minusState d beta h)) :
    Tendsto
      (fun m => (minusMeasure d m beta h :
        Measure (ConfigSpace (Site d))).real (fmu_multiOpen T))
      atTop
      (nhds ((minusState d beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T))) := by
  let a : ℕ → ℝ := fun m =>
    (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real
      (fmu_multiOpen T)
  have hmono : Monotone a := fun n m hnm =>
    iptm_minus_multiOpen_monotone hbeta hh T hnm
  have hbdd : BddAbove (Set.range a) :=
    ⟨1, by rintro _ ⟨m, rfl⟩; exact measureReal_le_one⟩
  have hfull : Tendsto a atTop (nhds (⨆ n, a n)) :=
    tendsto_atTop_ciSup hmono hbdd
  have hsub : Tendsto (a ∘ phi) atTop
      (nhds ((minusState d beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T))) := by
    simpa only [a, Function.comp_apply] using
      hconv.tendsto_real_of_isClopen (ipe_multiOpen_isClopen T)
  have hsub2 : Tendsto (a ∘ phi) atTop (nhds (⨆ n, a n)) :=
    hfull.comp hphi.tendsto_atTop
  rw [tendsto_nhds_unique hsub hsub2]
  exact hfull


theorem iptm_squeeze_lower
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d))
    {a m : ℕ} (hcond : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
    (minusMeasure d a beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T) ≤
      (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
  rw [← iptm_gvMinusMeasure_eq_minusMeasure a beta h,
    ← iptm_gvMinusMeasure_eq_minusMeasure m beta h,
    ← iptm_gvMinus_real_shift g (boxFinset d m) beta h T]
  exact iptm_gv_crossbox_dom (iptp_box_subset_transBox g hcond) hbeta hh
    (fmu_multiOpen_measurable T) (fmu_multiOpen_isIncreasing T)


theorem iptm_squeeze_upper
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) (m : ℕ) :
    (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) ≤
      (minusMeasure d (m + flc_vrad (Multiplicative.toAdd g)) beta h :
        Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) := by
  rw [← iptm_gvMinusMeasure_eq_minusMeasure m beta h,
    ← iptm_gvMinus_real_shift g (boxFinset d m) beta h T,
    ← iptm_gvMinusMeasure_eq_minusMeasure
      (m + flc_vrad (Multiplicative.toAdd g)) beta h]
  exact iptm_gv_crossbox_dom (iptp_transBox_subset_box g m) hbeta hh
    (fmu_multiOpen_measurable T) (fmu_multiOpen_isIncreasing T)


theorem iptm_minusMultiHomogeneous
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h)
    (g : Multiplicative (Site d)) (T : Finset (Site d)) :
    (minusState d beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen T) =
      (minusState d beta h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
  obtain ⟨phi, hphi, hconv⟩ := minusState_isInfiniteVolumeState d beta h
  let c := flc_vrad (Multiplicative.toAdd g)
  let ivT := (minusState d beta h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen T)
  let ivT' := (minusState d beta h : Measure (ConfigSpace (Site d))).real
    (fmu_multiOpen (T.image (fun x => g⁻¹ • x)))
  have hmid : Tendsto
      (fun m => (minusMeasure d m beta h : Measure _).real
        (fmu_multiOpen (T.image (fun x => g⁻¹ • x))))
      atTop (nhds ivT') :=
    iptm_minus_multiOpen_full_tendsto hbeta hh
      (T.image (fun x => g⁻¹ • x)) hphi hconv
  have hfull : Tendsto
      (fun m => (minusMeasure d m beta h : Measure _).real
        (fmu_multiOpen T)) atTop (nhds ivT) :=
    iptm_minus_multiOpen_full_tendsto hbeta hh T hphi hconv
  have hup : Tendsto
      (fun m => (minusMeasure d (m + c) beta h : Measure _).real
        (fmu_multiOpen T)) atTop (nhds ivT) :=
    hfull.comp (tendsto_add_atTop_nat c)
  have hlow : Tendsto
      (fun m => (minusMeasure d (m - c) beta h : Measure _).real
        (fmu_multiOpen T)) atTop (nhds ivT) :=
    hfull.comp (tendsto_sub_atTop_nat c)
  have hle : ivT ≤ ivT' := by
    refine le_of_tendsto_of_tendsto hlow hmid ?_
    filter_upwards [Filter.eventually_ge_atTop c] with m hm
    exact iptm_squeeze_lower hbeta hh g T
      (by dsimp [c]; omega : (m - c) + c ≤ m)
  have hge : ivT' ≤ ivT :=
    le_of_tendsto_of_tendsto hmid hup
      (Filter.Eventually.of_forall fun m =>
        iptm_squeeze_upper hbeta hh g T m)
  exact le_antisymm hle hge


theorem iptm_minusState_isTranslationInvariant
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℝ} (hh : 0 ≤ h) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  intro g
  let mu : Measure (ConfigSpace (Site d)) := minusState d beta h
  haveI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map (shift g) mu) :=
    Measure.isProbabilityMeasure_map (measurable_shift g).aemeasurable
  refine ⟨measurable_shift g, ?_⟩
  apply StatMech.FK.fkgqt_measure_eq_of_multiOpen_eq
  intro T
  rw [Measure.map_apply (measurable_shift g)
    (fmu_multiOpen_measurable T), fmu_shift_multiOpen]
  have hr := (iptm_minusMultiHomogeneous
    (d := d) hbeta hh g T).symm
  unfold Measure.real at hr
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top mu _) (measure_ne_top mu _)).mp hr

end StatMech.Ising
