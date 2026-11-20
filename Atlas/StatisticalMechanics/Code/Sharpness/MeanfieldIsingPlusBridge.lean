/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.MeanfieldIsingIntegrated
import Code.Ising.IsingPlusTIClose
import Code.Ising.PressureBCIndep

open MeasureTheory Real Set Filter Topology
open scoped BigOperators

namespace StatMech
namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

theorem sct_boundaryBond_mono
    {d n : ℕ} {e : Sym2 (Site d)}
    (heT : e ∈ bondFinsetTouch d n) (heI : e ∉ bondFinsetInternal d n)
    {a b : {x // x ∈ box d n} → Bool} (hab : a ≤ b) :
    bond (glue (plusField d) a) e ≤ bond (glue (plusField d) b) e := by
  unfold bondFinsetTouch bondPairsTouch at heT
  rw [Finset.mem_image] at heT
  obtain ⟨p, hp, rfl⟩ := heT
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hxp, hyp⟩, _hadj, hxory⟩ := hp
  rw [Ising.mem_boxFinset] at hxp hyp
  have hnotboth : ¬ (p.1 ∈ box d n ∧ p.2 ∈ box d n) := by
    rintro ⟨hx, hy⟩
    apply heI
    unfold bondFinsetInternal bondPairsInternal
    rw [Finset.mem_image]
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Ising.mem_boxFinset.mpr hx, Ising.mem_boxFinset.mpr hy⟩, _hadj⟩
  rcases hxory with hx | hy
  · have hyn : p.2 ∉ box d n := fun hy => hnotboth ⟨hx, hy⟩
    rw [bond_mk, bond_mk]
    simp only [spin, glue_mem _ _ hx, glue_not_mem _ _ hyn, plusField, ite_true,
      mul_one]
    exact spinB_mono _ _ (hab ⟨p.1, hx⟩)
  · have hxn : p.1 ∉ box d n := fun hx => hnotboth ⟨hx, hy⟩
    rw [bond_mk, bond_mk]
    simp only [spin, glue_mem _ _ hy, glue_not_mem _ _ hxn, plusField, ite_true,
      one_mul]
    exact spinB_mono _ _ (hab ⟨p.2, hy⟩)

theorem sct_fvEnergy_internal_touch_cross
    {d n : ℕ} (h : ℝ) (a b : {x // x ∈ box d n} → Bool) :
    fvEnergy (plusField d) n (bondFinsetInternal d n) h (a ⊓ b) +
        fvEnergy (plusField d) n (bondFinsetTouch d n) h (a ⊔ b) ≤
      fvEnergy (plusField d) n (bondFinsetInternal d n) h a +
        fvEnergy (plusField d) n (bondFinsetTouch d n) h b := by
  let BI := bondFinsetInternal d n
  let BT := bondFinsetTouch d n
  let D := BT \ BI
  have hsub : BI ⊆ BT := bondFinsetInternal_subset_touch n
  have hE (tau : {x // x ∈ box d n} → Bool) :
      fvEnergy (plusField d) n BT h tau =
        fvEnergy (plusField d) n BI h tau -
          ∑ e ∈ D, bond (glue (plusField d) tau) e := by
    unfold fvEnergy
    have hs := Finset.sum_sdiff (f := fun e => bond (glue (plusField d) tau) e) hsub
    dsimp [D] at hs
    dsimp [BI, BT]
    rw [← hs]
    ring
  have hmono :
      (∑ e ∈ D, bond (glue (plusField d) b) e) ≤
        ∑ e ∈ D, bond (glue (plusField d) (a ⊔ b)) e := by
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_sdiff] at he
    exact sct_boundaryBond_mono he.1 he.2 le_sup_right
  have hsm := ifk_fvEnergy_submodular (plusField d) n BI h a b
  rw [hE (a ⊔ b), hE b]
  linarith

theorem sct_fvWeight_internal_touch_cross
    {d n : ℕ} {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (a b : {x // x ∈ box d n} → Bool) :
    fvWeight (plusField d) n (bondFinsetInternal d n) β h a *
        fvWeight (plusField d) n (bondFinsetTouch d n) β h b ≤
      fvWeight (plusField d) n (bondFinsetInternal d n) β h (a ⊓ b) *
        fvWeight (plusField d) n (bondFinsetTouch d n) β h (a ⊔ b) := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := sct_fvEnergy_internal_touch_cross h a b
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hc)]

theorem sct_fvProb_internal_touch_cross
    {d n : ℕ} {β : ℝ} (hβ : 0 ≤ β) (h : ℝ)
    (a b : {x // x ∈ box d n} → Bool) :
    fvProb (plusField d) n (bondFinsetInternal d n) β h a *
        fvProb (plusField d) n (bondFinsetTouch d n) β h b ≤
      fvProb (plusField d) n (bondFinsetInternal d n) β h (a ⊓ b) *
        fvProb (plusField d) n (bondFinsetTouch d n) β h (a ⊔ b) := by
  simp only [fvProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (fvZ_pos (plusField d) n (bondFinsetInternal d n) β h)
      (fvZ_pos (plusField d) n (bondFinsetTouch d n) β h))).mpr
    (sct_fvWeight_internal_touch_cross hβ h a b)

theorem sct_fvEnergy_internal_boundary_indep
    {d n : ℕ} (eta eta' : ConfigSpace (Site d)) (h : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    fvEnergy eta n (bondFinsetInternal d n) h tau =
      fvEnergy eta' n (bondFinsetInternal d n) h tau := by
  unfold fvEnergy
  have hb : (∑ e ∈ bondFinsetInternal d n, bond (glue eta tau) e) =
      ∑ e ∈ bondFinsetInternal d n, bond (glue eta' tau) e := by
    apply Finset.sum_congr rfl
    intro e he
    exact bond_internal_indep eta eta' n tau he
  rw [hb, fieldSum_indep eta eta' n tau]

theorem sct_fvProb_internal_boundary_indep
    {d n : ℕ} (eta eta' : ConfigSpace (Site d)) (beta h : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    fvProb eta n (bondFinsetInternal d n) beta h tau =
      fvProb eta' n (bondFinsetInternal d n) beta h tau := by
  have hw (sigma : {x // x ∈ box d n} → Bool) :
      fvWeight eta n (bondFinsetInternal d n) beta h sigma =
        fvWeight eta' n (bondFinsetInternal d n) beta h sigma := by
    unfold fvWeight
    rw [sct_fvEnergy_internal_boundary_indep eta eta' h sigma]
  have hZ : fvZ eta n (bondFinsetInternal d n) beta h =
      fvZ eta' n (bondFinsetInternal d n) beta h := by
    unfold fvZ
    exact Finset.sum_congr rfl (fun sigma _ => hw sigma)
  unfold fvProb
  rw [hw, hZ]

theorem sct_fvProb_free_le_plus
    {d n : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) (h : ℝ)
    {A : Set (ConfigSpace {x // x ∈ box d n})} (hA : IsIncreasing A) :
    (∑ tau, A.indicator (fun _ => (1 : ℝ)) tau *
        fvProb (minusField d) n (bondFinsetInternal d n) beta h tau) ≤
      ∑ tau, A.indicator (fun _ => (1 : ℝ)) tau *
        fvProb (plusField d) n (bondFinsetTouch d n) beta h tau := by
  refine holley_dominates
    (fun tau => fvProb_nonneg (minusField d) n (bondFinsetInternal d n) beta h tau)
    (fun tau => fvProb_nonneg (plusField d) n (bondFinsetTouch d n) beta h tau)
    ?_ ?_ hA
  · rw [fvProb_sum_eq_one, fvProb_sum_eq_one]
  · intro a b
    simpa only [sct_fvProb_internal_boundary_indep
      (minusField d) (plusField d) beta h] using
      sct_fvProb_internal_touch_cross hbeta h a b

theorem sct_fvMeasure_free_le_plus
    {d n : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) (h : ℝ) :
    (fvMeasure (minusField d) n (bondFinsetInternal d n) beta h) ≼
      fvMeasure (plusField d) n (bondFinsetTouch d n) beta h := by
  intro A hA hAinc
  rw [fvMeasure_real_eq (minusField d) n (bondFinsetInternal d n) beta h hA,
    fvMeasure_real_eq (plusField d) n (bondFinsetTouch d n) beta h hA]
  set A1 : Set (ConfigSpace {x // x ∈ box d n}) :=
    (fun tau => glue (minusField d) tau) ⁻¹' A
  set A2 : Set (ConfigSpace {x // x ∈ box d n}) :=
    (fun tau => glue (plusField d) tau) ⁻¹' A
  have hre1 : ∀ tau : {x // x ∈ box d n} → Bool,
      A.indicator (fun _ => (1 : ℝ)) (glue (minusField d) tau) =
        A1.indicator (fun _ => (1 : ℝ)) tau := by
    intro tau
    by_cases hm : glue (minusField d) tau ∈ A
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (show tau ∈ A1 from hm)]
    · rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show tau ∉ A1 from hm)]
  have hre2 : ∀ tau : {x // x ∈ box d n} → Bool,
      A.indicator (fun _ => (1 : ℝ)) (glue (plusField d) tau) =
        A2.indicator (fun _ => (1 : ℝ)) tau := by
    intro tau
    by_cases hm : glue (plusField d) tau ∈ A
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (show tau ∈ A2 from hm)]
    · rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show tau ∉ A2 from hm)]
  simp_rw [hre1, hre2]
  have hA1inc : IsIncreasing A1 := fun a b hab ha =>
    hAinc (glue_mono_interior (minusField d) a b hab) ha
  have hsub : A1 ⊆ A2 := by
    intro tau htau
    exact hAinc (glue_mono_boundary (minusField d) (plusField d)
      (minusField_le (plusField d)) tau) htau
  calc
    ∑ tau, fvProb (minusField d) n (bondFinsetInternal d n) beta h tau *
          A1.indicator (fun _ => (1 : ℝ)) tau =
        ∑ tau, A1.indicator (fun _ => (1 : ℝ)) tau *
          fvProb (minusField d) n (bondFinsetInternal d n) beta h tau := by
            apply Finset.sum_congr rfl
            intro tau _
            ring
    _ ≤ ∑ tau, A1.indicator (fun _ => (1 : ℝ)) tau *
          fvProb (plusField d) n (bondFinsetTouch d n) beta h tau :=
      sct_fvProb_free_le_plus hbeta h hA1inc
    _ ≤ ∑ tau, A2.indicator (fun _ => (1 : ℝ)) tau *
          fvProb (plusField d) n (bondFinsetTouch d n) beta h tau := by
      apply Finset.sum_le_sum
      intro tau _
      apply mul_le_mul_of_nonneg_right _
        (fvProb_nonneg (plusField d) n (bondFinsetTouch d n) beta h tau)
      by_cases h1 : tau ∈ A1
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hsub h1)]
      · rw [Set.indicator_of_notMem h1]
        by_cases h2 : tau ∈ A2
        · rw [Set.indicator_of_mem h2]
          norm_num
        · rw [Set.indicator_of_notMem h2]
    _ = ∑ tau, fvProb (plusField d) n (bondFinsetTouch d n) beta h tau *
          A2.indicator (fun _ => (1 : ℝ)) tau := by
      apply Finset.sum_congr rfl
      intro tau _
      ring

theorem sct_isIncreasing_spinUp {d : ℕ} (x : Site d) :
    IsIncreasing {omega : ConfigSpace (Site d) | omega x = true} := by
  intro a b hab ha
  exact Bool.le_iff_imp.mp (hab x) ha

theorem sct_integral_spin_eq_two_siteProb_sub_one
    {d : ℕ} (x : Site d)
    (mu : ProbabilityMeasure (ConfigSpace (Site d))) :
    (∫ omega, spin omega x ∂(mu : Measure (ConfigSpace (Site d)))) =
      2 * (mu : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} - 1 := by
  have hfun : (fun omega : ConfigSpace (Site d) => spin omega x) =
      fun omega => 2 * pstc_coordBcf x omega - 1 := by
    funext omega
    cases hx : omega x <;> norm_num [spin, pstc_coordBcf_apply, hx]
  rw [hfun, integral_sub
    ((BoundedContinuousFunction.integrable _ _).const_mul 2) (integrable_const 1),
    integral_const_mul, ibs_integral_coordBcf, integral_const]
  simp

theorem sct_freeMeasure_real_le_plusMeasure
    {d n : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) (h : ℝ)
    {A : Set (ConfigSpace (Site d))} (hAmeas : MeasurableSet A)
    (hAinc : IsIncreasing A) :
    (freeMeasure d n beta h : Measure (ConfigSpace (Site d))).real A ≤
      (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A := by
  change (fvMeasure (minusField d) n (bondFinsetInternal d n) beta h).real A ≤
    (fvMeasure (plusField d) n (bondFinsetTouch d n) beta h).real A
  exact sct_fvMeasure_free_le_plus hbeta h A hAmeas hAinc

theorem sct_continuous_fvEnergy_field
    {d n : ℕ} (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d)))
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun h => fvEnergy eta n B h tau) := by
  unfold fvEnergy
  exact continuous_const.sub (continuous_id.mul continuous_const)

theorem sct_continuous_fvWeight_field
    {d n : ℕ} (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (beta : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun h => fvWeight eta n B beta h tau) := by
  unfold fvWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul (sct_continuous_fvEnergy_field eta B tau))

theorem sct_continuous_fvZ_field
    {d n : ℕ} (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (beta : ℝ) :
    Continuous (fun h => fvZ eta n B beta h) := by
  unfold fvZ
  exact continuous_finsetSum _
    (fun tau _ => sct_continuous_fvWeight_field eta B beta tau)

theorem sct_continuous_fvProb_field
    {d n : ℕ} (eta : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (beta : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    Continuous (fun h => fvProb eta n B beta h tau) := by
  unfold fvProb
  exact (sct_continuous_fvWeight_field eta B beta tau).div
    (sct_continuous_fvZ_field eta B beta)
    (fun h => (fvZ_ne_zero eta n B beta h))

theorem sct_continuous_plusMeasure_real
    {d n : ℕ} (beta : ℝ) {A : Set (ConfigSpace (Site d))}
    (hA : MeasurableSet A) :
    Continuous (fun h =>
      (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A) := by
  have heq : (fun h =>
      (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A) =
      fun h => ∑ tau : {x // x ∈ box d n} → Bool,
        fvProb (plusField d) n (bondFinsetTouch d n) beta h tau *
          A.indicator (fun _ => (1 : ℝ)) (glue (plusField d) tau) := by
    funext h
    rw [plusMeasure_coe]
    exact fvMeasure_real_eq (plusField d) n (bondFinsetTouch d n) beta h hA
  rw [heq]
  exact continuous_finsetSum _ (fun tau _ =>
    (sct_continuous_fvProb_field (plusField d)
      (bondFinsetTouch d n) beta tau).mul continuous_const)

theorem sct_continuous_plusMeasure_spin
    {d n : ℕ} (beta : ℝ) (x : Site d) :
    Continuous (fun h => ∫ omega, spin omega x
      ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d)))) := by
  have heq : (fun h => ∫ omega, spin omega x
      ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d)))) =
      fun h => 2 *
        (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} - 1 := by
    funext h
    exact sct_integral_spin_eq_two_siteProb_sub_one x (plusMeasure d n beta h)
  rw [heq]
  exact (continuous_const.mul
    (sct_continuous_plusMeasure_real beta (ibs_measurableSet_spinUp x))).sub
      continuous_const

theorem sctFieldToZero_tendsto_zero :
    Tendsto sctFieldToZero atTop (nhds 0) := by
  simpa only [sctFieldToZero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem sctOriginMag_le_plusMeasure_spin
    {d n m : ℕ} (hnm : n ≤ m) {beta h : ℝ}
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    sctOriginMag d beta h m ≤
      ∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
  let A : Set (ConfigSpace (Site d)) :=
    {omega | omega (Percolation.origin d) = true}
  have hfree :
      (freeMeasure d m beta h : Measure (ConfigSpace (Site d))).real A ≤
        (plusMeasure d m beta h : Measure (ConfigSpace (Site d))).real A :=
    sct_freeMeasure_real_le_plusMeasure hbeta h
      (ibs_measurableSet_spinUp (Percolation.origin d))
      (sct_isIncreasing_spinUp (Percolation.origin d))
  have hplus :
      (plusMeasure d m beta h : Measure (ConfigSpace (Site d))).real A ≤
        (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A :=
    iti_crossbox_dom n m hnm hbeta hh
      (ibs_measurableSet_spinUp (Percolation.origin d))
      (sct_isIncreasing_spinUp (Percolation.origin d))
  have hprob := hfree.trans hplus
  have hspin :
      (∫ omega, spin omega (Percolation.origin d)
        ∂(freeMeasure d m beta h : Measure (ConfigSpace (Site d)))) ≤
      ∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
    rw [sct_integral_spin_eq_two_siteProb_sub_one,
      sct_integral_spin_eq_two_siteProb_sub_one]
    linarith
  rwa [sct_integral_freeMeasure_eq_originMag] at hspin

theorem sctInfiniteFieldMag_le_plusMeasure_spin
    {d n : ℕ} {beta h : ℝ} (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    sctInfiniteFieldMag d beta h ≤
      ∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
  have hlim : Tendsto (fun m => sctOriginMag d beta h m) atTop
      (nhds (sctInfiniteFieldMag d beta h)) := by
    simpa only [sctInfiniteFieldMag] using
      sctOriginMag_tendsto_iSup d beta h hbeta hh
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    (eventually_atTop.2 ⟨n, fun m hnm =>
      sctOriginMag_le_plusMeasure_spin hnm hbeta hh⟩)

theorem sctZeroPlusMag_le_plusMeasure_spin
    {d n : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta) :
    sctZeroPlusMag d beta ≤
      ∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  have hleft := sctInfiniteFieldMag_tendsto_zeroPlus d beta hbeta
  have hright : Tendsto
      (fun k => ∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta (sctFieldToZero k) :
          Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spin omega (Percolation.origin d)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))) :=
    (sct_continuous_plusMeasure_spin beta (Percolation.origin d)).continuousAt.tendsto.comp
      sctFieldToZero_tendsto_zero
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall (fun k =>
      sctInfiniteFieldMag_le_plusMeasure_spin hbeta
        (sctFieldToZero_pos k).le))

theorem sctZeroPlusMag_le_magnetization
    (d : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) :
    sctZeroPlusMag d beta ≤ magnetization d beta := by
  obtain ⟨phi, _hphi, hweak⟩ := plusState_isInfiniteVolumeState d beta 0
  have hright := hweak.tendsto_integral (spinBCF (Percolation.origin d))
  have hle : sctZeroPlusMag d beta ≤
      ∫ omega, spinBCF (Percolation.origin d) omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hright
      (Filter.Eventually.of_forall (fun k => by
        simpa only [Function.comp_apply, spinBCF_apply] using
          sctZeroPlusMag_le_plusMeasure_spin
            (d := d) (n := phi k) hbeta))
  simpa only [spinBCF_apply, magnetization] using hle

theorem sct_magnetization_meanfield_lower_bound_integrated
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d) {beta : ℝ}
    (hbeta : tildeBetaCIsing d ≤ beta) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      magnetization d beta :=
  (sctZeroPlus_meanfield_lower_bound_integrated d hbdd hcrit hbeta).trans
    (sctZeroPlusMag_le_magnetization d (hcrit.le.trans hbeta))

end Sharpness
end StatMech

