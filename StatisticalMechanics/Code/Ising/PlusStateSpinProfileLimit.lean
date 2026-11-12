/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.IsingPlusTIFromPlacement
import Code.Ising.MagNonneg

open MeasureTheory Filter Topology

namespace StatMech.Ising

open StatMech.Lattice StatMech.Percolation StatMech.FK

noncomputable section

variable {d : Nat}



theorem plusState_spin_eq_magnetization
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    (∫ omega, spin omega x
      ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      magnetization d beta := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta 0
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hti := iptp_plusState_isTranslationInvariant (d := d) hbeta
    (by norm_num : (0 : Real) <= 0)
  calc
    (∫ omega, spin omega x ∂mu) =
        ∫ omega, spin omega x ∂Measure.map (ConfigSpace.shift g) mu := by
          rw [hti.map_eq g]
    _ = ∫ omega, spin (ConfigSpace.shift g omega) x ∂mu := by
      change (∫ omega, spinBCF x omega
          ∂Measure.map (ConfigSpace.shift g) mu) = _
      rw [integral_map (StatMech.ConfigSpace.continuous_shift g).measurable.aemeasurable
        (spinBCF x).continuous.aestronglyMeasurable]
      simp only [spinBCF_apply]
    _ = ∫ omega, spin omega (origin d) ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      have hxg : g • origin d = x := by
        ext i
        simp [g, origin]
      rw [← hxg, iptp_spin_shift]
    _ = magnetization d beta := rfl




theorem exists_plusMeasure_spin_profile_tendsto_magnetization
    (d : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ∃ phi : Nat -> Nat, StrictMono phi ∧ forall x : Site d,
      Tendsto
        (fun n => ∫ omega, spin omega x
          ∂(plusMeasure d (phi n) beta 0 :
            Measure (ConfigSpace (Site d))))
        atTop (nhds (magnetization d beta)) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  refine ⟨phi, hphi, ?_⟩
  intro x
  have hlim := hconv.tendsto_integral (spinBCF x)
  have hmean : (∫ omega, (spinBCF x) omega
      ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      magnetization d beta := by
    simpa only [spinBCF_apply] using
      plusState_spin_eq_magnetization beta hbeta x
  rw [hmean] at hlim
  simpa only [Function.comp_apply, spinBCF_apply] using hlim


theorem integral_spin_eq_two_mul_real_spinUp_sub_one
    (mu : ProbabilityMeasure (ConfigSpace (Site d))) (x : Site d) :
    (∫ omega, spin omega x ∂(mu : Measure (ConfigSpace (Site d)))) =
      2 * (mu : Measure (ConfigSpace (Site d))).real {omega | omega x = true} - 1 := by
  have hpoint : forall omega : ConfigSpace (Site d),
      spin omega x = 2 * pstc_coordBcf x omega - 1 := by
    intro omega
    cases h : omega x <;> norm_num [spin, pstc_coordBcf_apply, h]
  calc
    (∫ omega, spin omega x ∂(mu : Measure (ConfigSpace (Site d)))) =
        ∫ omega, (2 * pstc_coordBcf x omega - 1)
          ∂(mu : Measure (ConfigSpace (Site d))) := by
      apply integral_congr_ae
      filter_upwards with omega
      exact hpoint omega
    _ = 2 * (∫ omega, pstc_coordBcf x omega
          ∂(mu : Measure (ConfigSpace (Site d)))) - 1 := by
      rw [integral_sub
        (((pstc_coordBcf x).integrable _).const_mul 2)
        (integrable_const 1), integral_const_mul, integral_const]
      simp
    _ = _ := by rw [ibs_integral_coordBcf]




theorem plusMeasure_spin_full_tendsto_magnetization
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    Tendsto
      (fun n => ∫ omega, spin omega x
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (magnetization d beta)) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hup := itb_plus_multiOpen_full_tendsto hbeta
    (by norm_num : (0 : Real) <= 0) ({x} : Finset (Site d)) hphi hconv
  have hset : fmu_multiOpen (E := Site d) ({x} : Finset (Site d)) =
      {omega | omega x = true} := by
    ext omega
    simp [fmu_multiOpen]
  rw [hset] at hup
  have hmean := plusState_spin_eq_magnetization beta hbeta x
  have hstate :
      2 * (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} - 1 = magnetization d beta := by
    rw [← integral_spin_eq_two_mul_real_spinUp_sub_one, hmean]
  have hscaled := hup.const_mul 2 |>.sub_const 1
  rw [hstate] at hscaled
  simpa only [integral_spin_eq_two_mul_real_spinUp_sub_one] using hscaled



theorem magnetization_le_plusMeasure_spin
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (x : Site d) :
    magnetization d beta <=
      ∫ omega, spin omega x
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  have hup := itb_plus_multiOpen_full_tendsto hbeta
    (by norm_num : (0 : Real) <= 0) ({x} : Finset (Site d)) hphi hconv
  have hset : fmu_multiOpen (E := Site d) ({x} : Finset (Site d)) =
      {omega | omega x = true} := by
    ext omega
    simp [fmu_multiOpen]
  rw [hset] at hup
  have hanti : Antitone (fun k =>
      (plusMeasure d k beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true}) := by
    intro a b hab
    simpa only [← hset] using iti_plus_multiOpen_antitone hbeta
      (by norm_num : (0 : Real) <= 0) ({x} : Finset (Site d)) hab
  have hprob :
      (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} <=
        (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} := by
    apply le_of_tendsto hup
    filter_upwards [eventually_ge_atTop n] with k hk
    exact hanti hk
  rw [integral_spin_eq_two_mul_real_spinUp_sub_one]
  have hmean := plusState_spin_eq_magnetization beta hbeta x
  rw [integral_spin_eq_two_mul_real_spinUp_sub_one] at hmean
  linarith

end

end StatMech.Ising
