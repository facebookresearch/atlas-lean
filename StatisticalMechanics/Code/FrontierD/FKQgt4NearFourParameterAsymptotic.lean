/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4CorrelationReduction
import Code.FrontierD.SixVertexDualGapAsymptotic
import Code.FrontierD.SixVertexGapEtaModular
import Mathlib.Analysis.Calculus.Taylor

open Filter Topology Asymptotics

namespace StatMech.FrontierD

noncomputable section



theorem sinh_sub_id_isLittleO_sq :
    (fun x : Real => Real.sinh x - x) =o[nhds 0]
      (fun x : Real => x ^ 2) := by
  have hsmallDeriv : (fun x : Real => Real.cosh x - 1) =o[nhds 0]
      (fun x : Real => x ^ 1) := by
    simpa using ((Real.hasDerivAt_cosh 0).sub_const 1).isLittleO
  have hsmallDeriv' : (fun x : Real => Real.cosh x - 1) =o[nhdsWithin 0 Set.univ]
      (fun x : Real => (x - 0) ^ 1) := by
    simpa using hsmallDeriv
  have h := convex_univ.isLittleO_pow_succ_real (Set.mem_univ (0 : Real))
    (fun x _ => ((Real.hasDerivAt_sinh x).sub
      (hasDerivAt_id x)).hasDerivWithinAt) hsmallDeriv'
  simpa using h




theorem one_div_sub_one_div_sinh_tendsto_zero :
    Tendsto (fun x : Real => 1 / x - 1 / Real.sinh x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hzero : Tendsto (fun x : Real => (Real.sinh x - x) / x ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    sinh_sub_id_isLittleO_sq.tendsto_div_nhds_zero.mono_left
      nhdsWithin_le_nhds
  have heq : (fun x : Real => x) ~[nhdsWithin 0 (Set.Ioi 0)] Real.sinh :=
    Real.isEquivalent_sinh.symm.mono nhdsWithin_le_nhds
  have hnz : ∀ᶠ x : Real in nhdsWithin 0 (Set.Ioi 0), Real.sinh x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.sinh_pos_iff.mpr hx).ne'
  have hone : Tendsto (fun x : Real => x / Real.sinh x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    (isEquivalent_iff_tendsto_one hnz).mp heq
  have hmul := hzero.mul hone
  convert hmul using 1
  · funext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]
  · norm_num



theorem exp_gap_lambda_div_exp_gap_sinh_tendsto_one :
    Tendsto (fun lam : Real =>
      Real.exp (-(Real.pi ^ 2) / (2 * lam)) /
        Real.exp (-(Real.pi ^ 2) / (2 * Real.sinh lam)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hdiff : Tendsto (fun lam : Real =>
      -(Real.pi ^ 2) / (2 * lam) -
        (-(Real.pi ^ 2) / (2 * Real.sinh lam)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert one_div_sub_one_div_sinh_tendsto_zero.const_mul
      (-(Real.pi ^ 2) / 2) using 1
    · funext lam
      ring
    · ring
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hdiff
  simpa only [Function.comp_def, Real.exp_sub, Real.exp_zero] using hexp

theorem sixVertexAntiferroelectricLambda_fkQgt4_eq_arcosh
    {q : Real} (hq : 4 < q) :
    sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) =
      Real.arcosh (Real.sqrt q / 2) := by
  unfold sixVertexAntiferroelectricLambda
  rw [fkQgt4SixVertexWeight_sq hq]
  congr 1
  ring



theorem sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero :
    Tendsto
      (fun q : Real =>
        sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
      (nhdsWithin 4 (Set.Ioi 4)) (nhdsWithin 0 (Set.Ioi 0)) := by
  let g : Real -> Real := fun q => Real.sqrt q / 2
  have hsqrt4 : Real.sqrt (4 : Real) = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : Real) <= 4 by norm_num),
      Real.sqrt_nonneg (4 : Real)]
  have hgNhds : Tendsto g (nhdsWithin 4 (Set.Ioi 4)) (nhds 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa [g, hsqrt4] using
      (Real.continuous_sqrt.div_const 2).tendsto (4 : Real)
  have hgMem : Tendsto g (nhdsWithin 4 (Set.Ioi 4))
      (Filter.principal (Set.Ici 1)) := by
    rw [Filter.tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with q hq
    change 4 < q at hq
    dsimp [g]
    have hq0 : 0 <= q := by linarith
    have hsqrt : 2 < Real.sqrt q := by
      nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
    change 1 <= Real.sqrt q / 2
    linarith
  have hg : Tendsto g (nhdsWithin 4 (Set.Ioi 4))
      (nhdsWithin 1 (Set.Ici 1)) := by
    change Tendsto g (nhdsWithin 4 (Set.Ioi 4))
      (nhds 1 ⊓ Filter.principal (Set.Ici 1))
    exact Filter.tendsto_inf.2 ⟨hgNhds, hgMem⟩
  have harcosh : Tendsto Real.arcosh (nhdsWithin 1 (Set.Ici 1)) (nhds 0) := by
    simpa [Real.arcosh_zero] using
      (Real.continuousOn_arcosh.continuousWithinAt
        (show (1 : Real) ∈ Set.Ici 1 by simp)).tendsto
  have hzero : Tendsto
      (fun q : Real =>
        sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
      (nhdsWithin 4 (Set.Ioi 4)) (nhds 0) := by
    apply (harcosh.comp hg).congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (sixVertexAntiferroelectricLambda_fkQgt4_eq_arcosh hq).symm
  change Tendsto
    (fun q : Real =>
      sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))
    (nhdsWithin 4 (Set.Ioi 4))
    (nhds 0 ⊓ Filter.principal (Set.Ioi 0))
  apply Filter.tendsto_inf.2
  constructor
  · exact hzero
  · rw [Filter.tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact sixVertexAntiferroelectricLambda_fkQgt4_pos hq


theorem fkQgt4_exp_lambda_div_exp_sqrt_sub_four_tendsto_one :
    Tendsto (fun q : Real =>
      let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
      Real.exp (-(Real.pi ^ 2) / (2 * lam)) /
        Real.exp (-(Real.pi ^ 2) / Real.sqrt (q - 4)))
      (nhdsWithin 4 (Set.Ioi 4)) (nhds 1) := by
  have hcomp := exp_gap_lambda_div_exp_gap_sinh_tendsto_one.comp
    sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  change 4 < q at hq
  simp only [Function.comp_apply]
  rw [sqrt_fkQgt4_sub_four_eq_two_mul_sinh hq]



theorem sixVertexAntiferroelectricGapRate_div_exp_tendsto_one :
    Tendsto (fun lam : Real =>
      sixVertexAntiferroelectricGapRate lam /
        (8 * Real.exp (-(Real.pi ^ 2) / (2 * lam))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  apply sixVertexDualGapRate_div_tendsto_one.congr'
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  rw [sixVertexAntiferroelectricGapRate_eq_dualGapRate hlam]


theorem fkQgt4SixVertexGapRate_div_exp_sqrt_sub_four_tendsto_one :
    Tendsto (fun q : Real =>
      fkQgt4SixVertexGapRate q /
        (8 * Real.exp (-(Real.pi ^ 2) / Real.sqrt (q - 4))))
      (nhdsWithin 4 (Set.Ioi 4)) (nhds 1) := by
  have hgap := sixVertexAntiferroelectricGapRate_div_exp_tendsto_one.comp
    sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero
  have hscale := fkQgt4_exp_lambda_div_exp_sqrt_sub_four_tendsto_one
  have hmul := hgap.mul hscale
  convert hmul using 1
  · funext q
    dsimp only [fkQgt4SixVertexGapRate]
    simp only [Function.comp_apply]
    have h8 : (8 : Real) ≠ 0 := by norm_num
    have he1 : Real.exp (-(Real.pi ^ 2) /
        (2 * sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) ≠ 0 :=
      (Real.exp_pos _).ne'
    have he2 : Real.exp (-(Real.pi ^ 2) / Real.sqrt (q - 4)) ≠ 0 :=
      (Real.exp_pos _).ne'
    field_simp
  · norm_num

end

end StatMech.FrontierD
