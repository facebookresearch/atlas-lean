/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheRootBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Stirling








open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexSelectedBulkLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with J ≤ j.val,
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)




def sixVertexSelectedBulkLogKernel
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (∑ j : Fin (k + 1) with J ≤ j.val, Real.log
      (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) *
          Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
        (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)))) /
    (sixVertexFourWidth 0 k : Real)



theorem sixVertexSelectedBulkLogContribution_eq_logKernel
    {c : Real} (hc : 2 < c) (J k : Nat) :
    sixVertexSelectedBulkLogContribution hc J k =
      sixVertexSelectedBulkLogKernel hc J k := by
  unfold sixVertexSelectedBulkLogContribution
    sixVertexSelectedBulkLogKernel
  rw [Finset.mul_sum]
  apply congrArg (fun t : Real => t / (sixVertexFourWidth 0 k : Real))
  apply Finset.sum_congr rfl
  intro j hj
  have hlog := sixVertexBetheM_phase_log_norm c
    (sixVertexPositiveHalfBetheRoots hc k j)
    (sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j))
  rw [hlog]
  ring



theorem sixVertexSelectedInitialLogContribution_le_factorial
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ : J ≤ k + 1) :
    sixVertexSelectedInitialLogContribution hc J k ≤
      (2 * ((J : Real) *
          Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) -
        Real.log (J.factorial : Real))) /
        (sixVertexFourWidth 0 k : Real) := by
  let S : Finset (Fin (k + 1)) :=
    Finset.univ.filter (fun j => j.val < J)
  let B : Real :=
    Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2)
  let f : Fin (k + 1) → Real := fun j =>
    Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖
  have hN : (0 : Real) < sixVertexFourWidth 0 k := by
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hterm (j : Fin (k + 1)) :
      f j ≤ B - Real.log ((j.val + 1 : Nat) : Real) := by
    have hquant := sixVertexSelectedBetheM_log_norm_le_quantile hc k j
    have hnum : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) := by
      positivity
    have hjpos : (0 : Real) < (j.val + 1 : Nat) := by positivity
    have hsmall : 0 < c ^ 2 * (sixVertexFourWidth 0 k : Real) /
        (2 * (2 * (j : Real) + 1)) := by positivity
    have hfrac : c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1)) ≤
        c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real)) := by
      apply div_le_div_of_nonneg_left hnum.le (by positivity)
      push_cast
      nlinarith [show (0 : Real) ≤ j by positivity]
    calc
      f j ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (2 * (j : Real) + 1))) := hquant
      _ ≤ Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * ((j.val + 1 : Nat) : Real))) :=
        Real.log_le_log hsmall hfrac
      _ = B - Real.log ((j.val + 1 : Nat) : Real) := by
        dsimp [B]
        rw [show c ^ 2 * (sixVertexFourWidth 0 k : Real) /
            (2 * ((j.val + 1 : Nat) : Real)) =
          (c ^ 2 * (sixVertexFourWidth 0 k : Real) / 2) /
            ((j.val + 1 : Nat) : Real) by ring]
        rw [Real.log_div (by positivity) hjpos.ne']
  have hsum : (∑ j ∈ S, f j) ≤
      ∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hterm j
  have hindex :
      (∑ j ∈ S, (B - Real.log ((j.val + 1 : Nat) : Real))) =
        ∑ i ∈ Finset.range J,
          (B - Real.log ((i + 1 : Nat) : Real)) := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    · intro a ha b hb hab
      exact Fin.ext hab
    · intro i hi
      have hiJ := Finset.mem_range.mp hi
      let j : Fin (k + 1) := ⟨i, lt_of_lt_of_le hiJ hJ⟩
      refine ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiJ⟩
    · intro j hj
      rfl
  have hlogs :
      (∑ i ∈ Finset.range J, Real.log ((i + 1 : Nat) : Real)) =
        Real.log (J.factorial : Real) := by
    rw [← Real.log_prod (fun i hi => by positivity)]
    apply congrArg Real.log
    norm_cast
    exact Finset.prod_range_add_one_eq_factorial J
  have hsum' : (∑ j ∈ S, f j) ≤
      (J : Real) * B - Real.log (J.factorial : Real) := by
    rw [hindex, Finset.sum_sub_distrib, hlogs] at hsum
    simpa using hsum
  unfold sixVertexSelectedInitialLogContribution
  change (2 * ∑ j ∈ S, f j) / _ ≤ _
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith



theorem sixVertexSelectedInitialLogContribution_le_stirling
    {c : Real} (hc : 2 < c) {J k : Nat} (hJ0 : 0 < J)
    (hJ : J ≤ k + 1) :
    sixVertexSelectedInitialLogContribution hc J k ≤
      (2 * (J : Real) *
        (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
          (2 * (J : Real))) + 1)) /
        (sixVertexFourWidth 0 k : Real) := by
  let N : Real := sixVertexFourWidth 0 k
  let B : Real := Real.log (c ^ 2 * N / 2)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast sixVertexFourWidth_pos 0 k
  have hJreal : (0 : Real) < J := by exact_mod_cast hJ0
  have hlogJ : 0 ≤ Real.log (J : Real) :=
    Real.log_nonneg (by exact_mod_cast hJ0)
  have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  have hfactorial := Stirling.le_log_factorial_stirling hJ0.ne'
  have hfactorial' :
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
        Real.log (J.factorial : Real) := by
    calc
      (J : Real) * Real.log (J : Real) - (J : Real) ≤
          (J : Real) * Real.log (J : Real) - (J : Real) +
            Real.log (J : Real) / 2 + Real.log (2 * Real.pi) / 2 := by
        nlinarith [hlogJ, hlogTwoPi]
      _ ≤ Real.log (J.factorial : Real) := hfactorial
  have hlog :
      Real.log (c ^ 2 * N / (2 * (J : Real))) =
        B - Real.log (J : Real) := by
    dsimp [B]
    rw [show c ^ 2 * N / (2 * (J : Real)) =
      (c ^ 2 * N / 2) / (J : Real) by ring]
    rw [Real.log_div (by positivity) hJreal.ne']
  have hbase := sixVertexSelectedInitialLogContribution_le_factorial
    hc hJ
  change sixVertexSelectedInitialLogContribution hc J k ≤
    (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N at hbase
  change sixVertexSelectedInitialLogContribution hc J k ≤
    (2 * (J : Real) *
      (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N
  calc
    sixVertexSelectedInitialLogContribution hc J k ≤
        (2 * ((J : Real) * B - Real.log (J.factorial : Real))) / N := hbase
    _ ≤ (2 * (J : Real) *
        (Real.log (c ^ 2 * N / (2 * (J : Real))) + 1)) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      rw [hlog]
      nlinarith





theorem sixVertexSelectedInitialLogContribution_tendsto_zero_of_sublinear
    {c : Real} (hc : 2 < c) (J : Nat → Nat)
    (hJ0 : ∀ᶠ k in atTop, 0 < J k)
    (hJle : ∀ᶠ k in atTop, J k ≤ k + 1)
    (hsublinear : Tendsto (fun k : Nat =>
      (J k : Real) / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0)) :
    Tendsto (fun k => sixVertexSelectedInitialLogContribution hc (J k) k)
      atTop (nhds 0) := by
  let x : Nat → Real := fun k =>
    (J k : Real) / (sixVertexFourWidth 0 k : Real)
  let C : Real := Real.log (c ^ 2 / 2)
  have hx : Tendsto x atTop (nhds 0) := hsublinear
  have hxlog : Tendsto (fun k => x k * Real.log (x k)) atTop (nhds 0) := by
    have h := Real.continuous_mul_log.continuousAt.tendsto.comp hx
    simpa using h
  have hupper : Tendsto (fun k =>
      2 * x k * (C - Real.log (x k) + 1)) atTop (nhds 0) := by
    have hlinear := hx.const_mul (2 * (C + 1))
    have hlogterm := hxlog.const_mul 2
    convert hlinear.sub hlogterm using 1
    · funext k
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [] with k
    exact (sixVertexSelectedInitialLogContribution_bounds hc (J k) k).1
  · filter_upwards [hJ0, hJle] with k hk0 hkle
    have hN : (0 : Real) < sixVertexFourWidth 0 k := by
      exact_mod_cast sixVertexFourWidth_pos 0 k
    have hJreal : (0 : Real) < J k := by exact_mod_cast hk0
    have hxpos : 0 < x k := div_pos hJreal hN
    have hratio :
        c ^ 2 * (sixVertexFourWidth 0 k : Real) / (2 * (J k : Real)) =
          (c ^ 2 / 2) / x k := by
      dsimp [x]
      field_simp [hN.ne', hJreal.ne']
    calc
      sixVertexSelectedInitialLogContribution hc (J k) k ≤
          (2 * (J k : Real) *
            (Real.log (c ^ 2 * (sixVertexFourWidth 0 k : Real) /
              (2 * (J k : Real))) + 1)) /
            (sixVertexFourWidth 0 k : Real) :=
        sixVertexSelectedInitialLogContribution_le_stirling hc hk0 hkle
      _ = 2 * x k * (C - Real.log (x k) + 1) := by
        rw [hratio, Real.log_div (by positivity : c ^ 2 / 2 ≠ 0) hxpos.ne']
        dsimp [x, C]
        ring
  · exact hupper



theorem sixVertexSelectedRootAverage_eq_initial_add_bulk
    {c : Real} (hc : 2 < c) (J k : Nat) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k =
      sixVertexSelectedInitialLogContribution hc J k +
        sixVertexSelectedBulkLogContribution hc J k := by
  let f : Fin (k + 1) → Real := fun j =>
    Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (k + 1))) (fun j => j.val < J) f
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
    sixVertexSelectedInitialLogContribution
    sixVertexSelectedBulkLogContribution
  simp only [not_lt] at hsplit
  rw [← hsplit]
  ring


theorem sixVertexSelectedRootAverage_eq_log2Initial_add_bulk
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k =
      sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k +
        sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k :=
  sixVertexSelectedRootAverage_eq_initial_add_bulk hc _ _



theorem sixVertexHalfFilledBetheCandidateRate_eq_log2Edge_add_bulkKernel
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexHalfFilledBetheCandidateRate hc k =
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k +
          sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k := by
  rw [sixVertexHalfFilledBetheCandidateRate_eq_rootAverage,
    sixVertexSelectedRootAverage_eq_log2Initial_add_bulk,
    sixVertexSelectedBulkLogContribution_eq_logKernel]
  ring




theorem sixVertexSelectedRootAverage_tendsto_iff_bulkLog2
    {c a : Real} (hc : 2 < c) :
    Tendsto (sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc)) atTop (nhds a) ↔
      Tendsto (fun k => sixVertexSelectedBulkLogContribution hc
        (Nat.log2 (k + 1)) k) atTop (nhds a) := by
  let edge : Nat → Real := fun k =>
    sixVertexSelectedInitialLogContribution hc (Nat.log2 (k + 1)) k
  let bulk : Nat → Real := fun k =>
    sixVertexSelectedBulkLogContribution hc (Nat.log2 (k + 1)) k
  have hedge : Tendsto edge atTop (nhds 0) := by
    exact sixVertexSelectedInitialLogContribution_log2_tendsto_zero hc
  have hdecomp :
      sixVertexSymmetricBetheRootAverage c
          (sixVertexPositiveHalfBetheRootFamily hc) =
        fun k => edge k + bulk k := by
    funext k
    exact sixVertexSelectedRootAverage_eq_log2Initial_add_bulk hc k
  rw [hdecomp]
  constructor
  · intro h
    have hsub := h.sub hedge
    simpa [edge, bulk] using hsub
  · intro h
    simpa [edge, bulk] using hedge.add h




theorem sixVertexHalfFilledBetheCandidateRate_tendsto_iff_bulkLog2
    {c a : Real} (hc : 2 < c) :
    Tendsto (sixVertexHalfFilledBetheCandidateRate hc) atTop (nhds a) ↔
      Tendsto (fun k => sixVertexSelectedBulkLogContribution hc
        (Nat.log2 (k + 1)) k) atTop (nhds a) := by
  have havg := sixVertexSelectedRootAverage_tendsto_iff_bulkLog2
    (a := a) hc
  have hcandidate : sixVertexHalfFilledBetheCandidateRate hc = fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexPositiveHalfBetheRootFamily hc) k := by
    funext k
    exact sixVertexHalfFilledBetheCandidateRate_eq_rootAverage hc k
  have hfinite : Tendsto (fun k : Nat =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2 / 4)).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    funext k
    simp [sixVertexFourWidth]
    field_simp
  rw [hcandidate]
  constructor
  · intro h
    apply havg.mp
    have hsub := h.sub hfinite
    simpa using hsub
  · intro h
    have havg' := havg.mpr h
    simpa using hfinite.add havg'




def SixVertexSelectedBulkFreeEnergyAsymptotic
    {c : Real} (hc : 2 < c) : Prop :=
  Tendsto (fun k => sixVertexSelectedBulkLogKernel hc
      (Nat.log2 (k + 1)) k) atTop
    (nhds (sixVertexAntiferroelectricFreeEnergyValue
      (sixVertexAntiferroelectricLambda c)))



theorem sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution
    {c : Real} (hc : 2 < c) :
    SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔
      Tendsto (fun k => sixVertexSelectedBulkLogContribution hc
        (Nat.log2 (k + 1)) k) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  apply tendsto_congr'
  filter_upwards [] with k
  exact (sixVertexSelectedBulkLogContribution_eq_logKernel hc _ _).symm



theorem sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue
          (sixVertexAntiferroelectricLambda c))) ↔
      SixVertexSelectedBulkFreeEnergyAsymptotic hc := by
  have hident :=
    sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase
      hc hphase
  refine (sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage
      hc (sixVertexPositiveHalfBetheRootFamily hc) hident).trans ?_
  exact (sixVertexSelectedRootAverage_tendsto_iff_bulkLog2 hc).trans
    (sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution hc).symm



theorem sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
    (hbulk : SixVertexSelectedBulkFreeEnergyAsymptotic hc) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) := by
  apply (sixVertexBalanced_iteratedLimit_iff_widthRate (by linarith)).2
  exact (sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase
    hc hphase).2 hbulk

end

end StatMech.FrontierD
