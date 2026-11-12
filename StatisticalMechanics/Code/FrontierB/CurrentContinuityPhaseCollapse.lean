/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.EdgeMarginalInfinite
import Code.Ising.IsingPlusTIFromPlacement
import Code.Ising.FVConsistencyProve
import Code.Ising.Peierls
import Code.FrontierB.CurrentContinuityReduction
import Code.FrontierB.GenMixingCofinite

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation

variable {d : Nat}



theorem measure_eq_of_clopenDom_coordinate_eq
    {E : Type*} [Countable E]
    (mu nu : Measure (ConfigSpace E))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hdom : mu ≼c nu)
    (hmarg : ∀ e : E,
      mu.real {omega | omega e = true} =
        nu.real {omega | omega e = true}) :
    mu = nu := by
  classical
  apply gsi_clopen_antisymm hdom
  intro A hAcl hAinc
  obtain ⟨F, hF⟩ := isClopen_dependsOn_finset A hAcl
  let r : ConfigSpace E → ConfigSpace F := Finset.restrict F
  let muF : ConfigSpace F → Real := fun eta => mu.real (r ⁻¹' {eta})
  let nuF : ConfigSpace F → Real := fun eta => nu.real (r ⁻¹' {eta})
  have hr : Measurable r :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i : E))
  have hmuF : 0 ≤ muF := fun _ => measureReal_nonneg
  have hnuF : 0 ≤ nuF := fun _ => measureReal_nonneg
  have hsumMu : ∑ eta, muF eta = 1 := fuc_sum_real_preimage_eq_one mu r hr
  have hsumNu : ∑ eta, nuF eta = 1 := fuc_sum_real_preimage_eq_one nu r hr
  have hrealMu : ∀ B : Set (ConfigSpace F),
      (measOfMass muF).real B = mu.real (r ⁻¹' B) := by
    intro B
    rw [measOfMass_real_eq_indicator_sum muF hmuF]
    exact (fuc_real_preimage_eq_indicator_sum mu r hr B).symm
  have hrealNu : ∀ B : Set (ConfigSpace F),
      (measOfMass nuF).real B = nu.real (r ⁻¹' B) := by
    intro B
    rw [measOfMass_real_eq_indicator_sum nuF hnuF]
    exact (fuc_real_preimage_eq_indicator_sum nu r hr B).symm
  have hdomF : measOfMass muF ≼ measOfMass nuF := by
    intro B _hB hBinc
    rw [hrealMu B, hrealNu B]
    apply hdom (r ⁻¹' B)
    · change IsClopen (MeasureTheory.cylinder (α := fun _ : E => Bool) F B)
      exact isClopen_cylinderEvent F B
    · intro omega omega' hle homega
      exact hBinc (fun i => hle i.1) homega
  obtain ⟨P, hP⟩ := fuc_isMonotoneCouplingFun_of_dominated
    hmuF hnuF hsumMu hsumNu hdomF
  have hmargF : ∀ e : F, edgeMargProb muF e = edgeMargProb nuF e := by
    intro e
    let B : Set (ConfigSpace F) := {eta | eta e = true}
    have hmuEdge : edgeMargProb muF e = mu.real (r ⁻¹' B) := by
      calc
        edgeMargProb muF e = eventMassProb muF B := by
          unfold edgeMargProb eventMassProb B
          apply Finset.sum_congr rfl
          intro eta _
          by_cases heta : eta e = true <;> simp [Set.indicator, heta]
        _ = mu.real (r ⁻¹' B) :=
          (fuc_real_preimage_eq_indicator_sum mu r hr B).symm
    have hnuEdge : edgeMargProb nuF e = nu.real (r ⁻¹' B) := by
      calc
        edgeMargProb nuF e = eventMassProb nuF B := by
          unfold edgeMargProb eventMassProb B
          apply Finset.sum_congr rfl
          intro eta _
          by_cases heta : eta e = true <;> simp [Set.indicator, heta]
        _ = nu.real (r ⁻¹' B) :=
          (fuc_real_preimage_eq_indicator_sum nu r hr B).symm
    rw [hmuEdge, hnuEdge]
    have hpre : r ⁻¹' B = {omega : ConfigSpace E | omega e.1 = true} := by
      ext omega
      rfl
    rw [hpre, hmarg e.1]
  let S := ih_section A F
  have hAcyl : A = MeasureTheory.cylinder F S :=
    ih_eq_cylinder_of_dependsOn F hF
  have hmass := fk_unique_of_edgeMarg_eq hP hmargF
    (ih_section_isIncreasing hAinc F)
  have hmuMass : eventMassProb muF S = mu.real A := by
    rw [hAcyl]
    exact (fuc_real_preimage_eq_indicator_sum mu r hr S).symm
  have hnuMass : eventMassProb nuF S = nu.real A := by
    rw [hAcyl]
    exact (fuc_real_preimage_eq_indicator_sum nu r hr S).symm
  rw [hmuMass, hnuMass] at hmass
  exact hmass.ge


theorem integral_spin_eq_two_mul_spinUp_sub_one
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (x : Site d) :
    (∫ omega, spin omega x ∂mu) =
      2 * mu.real {omega | omega x = true} - 1 := by
  let A : Set (ConfigSpace (Site d)) := {omega | omega x = true}
  have hA : MeasurableSet A := upTrue_measurableSet x
  have hpoint : (fun omega : ConfigSpace (Site d) => spin omega x) =
      fun omega => 2 * (A.indicator (fun _ => (1 : Real))) omega - 1 := by
    funext omega
    by_cases h : omega x = true <;> norm_num [spin, A, Set.indicator, h]
  have hInd : Integrable (A.indicator (fun _ => (1 : Real))) mu :=
    (integrable_const (1 : Real)).indicator hA
  rw [hpoint, integral_sub (hInd.const_mul 2) (integrable_const (1 : Real)),
    integral_const, integral_const_mul,
    integral_indicator_const (1 : Real) hA]
  simp [Measure.real, A]


theorem minusMeasure_spinUp_eq_one_sub_plusMeasure_spinUp
    (n : Nat) (beta : Real) (x : Site d) :
    (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} =
      1 - (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} := by
  let A : Set (ConfigSpace (Site d)) := {omega | omega x = true}
  have hA : MeasurableSet A := upTrue_measurableSet x
  have hmap := congrArg (fun mu : Measure (ConfigSpace (Site d)) => mu.real A)
    (map_minusMeasure_eq_plusMeasure (d := d) n beta)
  have hpre : flipConfig ⁻¹' A = Aᶜ := by
    ext omega
    simp [A, flipConfig]
  unfold Measure.real at hmap
  change ((Measure.map flipConfig
      (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) A).toReal =
    ((plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) A).toReal at hmap
  rw [Measure.map_apply measurable_flipConfig hA, hpre] at hmap
  have hmap' :
      (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real Aᶜ =
        (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real A := by
    exact hmap
  have hcomp :
      (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real Aᶜ =
        1 - (minusMeasure d n beta 0 : Measure (ConfigSpace (Site d))).real A := by
    rw [measureReal_compl hA, probReal_univ]
  dsimp [A] at hmap' hcomp ⊢
  linarith



theorem minusState_spinUp_eq_one_sub_plusState_spinUp
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    (minusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} =
      1 - (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} := by
  obtain ⟨phiMinus, hphiMinus, hminus⟩ :=
    minusState_isInfiniteVolumeState d beta 0
  obtain ⟨phiPlus, hphiPlus, hplus⟩ :=
    plusState_isInfiniteVolumeState d beta 0
  have hminusLim := StatMech.WeakConvergesTo.tendsto_real_of_isClopen hminus
    (upTrue_isClopen x)
  have hplusFull := itb_plus_multiOpen_full_tendsto hbeta le_rfl ({x} : Finset (Site d))
    hphiPlus hplus
  have hplusEvent : fmu_multiOpen (E := Site d) ({x} : Finset (Site d)) =
      {omega | omega x = true} := by
    ext omega
    simp [fmu_multiOpen]
  rw [hplusEvent] at hplusFull
  have hplusSub := hplusFull.comp hphiMinus.tendsto_atTop
  have hrhs : Tendsto (fun n =>
      1 - (plusMeasure d (phiMinus n) beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true}) atTop
      (nhds (1 - (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true})) := tendsto_const_nhds.sub hplusSub
  have heq : (fun n =>
      (minusMeasure d (phiMinus n) beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true}) =
      fun n => 1 - (plusMeasure d (phiMinus n) beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} := by
    funext n
    exact minusMeasure_spinUp_eq_one_sub_plusMeasure_spinUp (phiMinus n) beta x
  have hminusLim' : Tendsto (fun n =>
      (minusMeasure d (phiMinus n) beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true}) atTop
      (nhds ((minusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true})) := by
    simpa only [Function.comp_apply] using hminusLim
  rw [heq] at hminusLim'
  exact tendsto_nhds_unique hminusLim' hrhs


theorem plusState_spinUp_eq_origin
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega x = true} =
      (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
        {omega | omega (Percolation.origin d) = true} := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hhom := iptp_plusMultiHomogeneous (d := d) hbeta le_rfl g
    ({x} : Finset (Site d))
  have hg : g⁻¹ • x = Percolation.origin d := by
    funext i
    simp [g, Percolation.origin, smul_site_apply]
  have himage : ({x} : Finset (Site d)).image (fun y => g⁻¹ • y) =
      {Percolation.origin d} := by
    simp [hg]
  rw [himage] at hhom
  simpa [fmu_multiOpen] using hhom



theorem plusState_eq_minusState_of_magnetization_eq_zero
    (beta : Real) (hbeta : 0 <= beta)
    (hmag : magnetization d beta = 0) :
    (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  have horigin :
      (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega (Percolation.origin d) = true} = 1 / 2 := by
    have hid := integral_spin_eq_two_mul_spinUp_sub_one
      (plusState d beta 0 : Measure (ConfigSpace (Site d)))
      (Percolation.origin d)
    unfold magnetization at hmag
    rw [hmag] at hid
    linarith
  have hmarg : ∀ x : Site d,
      (minusState d beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} =
        (plusState d beta 0 : Measure (ConfigSpace (Site d))).real
          {omega | omega x = true} := by
    intro x
    rw [minusState_spinUp_eq_one_sub_plusState_spinUp beta hbeta x,
      plusState_spinUp_eq_origin beta hbeta x, horigin]
    ring
  have hdomc :
      (minusState d beta 0 : Measure (ConfigSpace (Site d))) ≼c
        (plusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    (gsi_infinite_volume_sandwich beta 0 hbeta le_rfl
      (plusState d beta 0 : Measure (ConfigSpace (Site d)))
      (psdlr_plusState_isDLR_uncond beta 0)).1
  exact (measure_eq_of_clopenDom_coordinate_eq
    (minusState d beta 0 : Measure (ConfigSpace (Site d)))
    (plusState d beta 0 : Measure (ConfigSpace (Site d))) hdomc hmarg).symm

end StatMech.FrontierB
