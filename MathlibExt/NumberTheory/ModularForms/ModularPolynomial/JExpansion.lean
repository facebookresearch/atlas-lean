/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean`,
`P2M/Sol/S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean`,
`Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean`,
`P2M/Sol/S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean`,
`Theorems/Thm_ModularCurve_hasSum_jNum_qParam.lean`,
`P2M/Sol/S_ModularCurve_hasSum_jNum_qParam.lean`,
`Theorems/Thm_ModularCurve_hasSum_jq_qParam.lean`,
`P2M/Sol/S_ModularCurve_hasSum_jq_qParam.lean`,
`Theorems/Thm_ModularCurve_hasSum_qParam_mul_laurent.lean`,
`P2M/Sol/S_ModularCurve_hasSum_qParam_mul_laurent.lean`,
`Theorems/Thm_ModularCurve_E4_cube_div_discriminant_smul.lean`,
and
`P2M/Sol/S_ModularCurve_E4_cube_div_discriminant_smul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialData
public import MathlibExt.NumberTheory.ModularForms.QParamProduct
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.PiTopology

@[expose] public section

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

open Polynomial in
private def truncPoly (N : ℕ) : ℂ[X] := ∏ n ∈ Finset.range N, (1 - Polynomial.X ^ (n + 1)) ^ 24

private def etaPow : PowerSeries ℂ := ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1)) ^ 24

private def gfun (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

private lemma coeff_mul_factor_eq {R : Type*} [CommRing R] {m n : ℕ} (hmn : m < n + 1)
    (Q : PowerSeries R) :
    PowerSeries.coeff m (Q * ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m Q := by
  obtain ⟨S, hS⟩ : PowerSeries.X ^ (n + 1) ∣
      ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24 - 1 := by
    have h := sub_dvd_pow_sub_pow ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) 1 24
    rw [one_pow, sub_sub_cancel_left] at h
    exact neg_dvd.mp h
  replace hS : ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24 =
      1 + PowerSeries.X ^ (n + 1) * S := by
    rw [← hS]; ring
  rw [hS, mul_add, mul_one, map_add, ← mul_assoc, mul_comm Q, mul_assoc,
    PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hmn), add_zero]

private lemma coeff_trunc_eq_coeff_tprod (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (m : ℕ) {N : ℕ} (hN : m < N) :
    PowerSeries.coeff m (∏ n ∈ Finset.range N,
        ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m (∏' n : ℕ, ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) := by
  have hmul : Multipliable fun n : ℕ => ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24 :=
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow R).pow 24
  have hlim : Tendsto (fun N => PowerSeries.coeff m
      (∏ n ∈ Finset.range N, ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24)) atTop
      (𝓝 (PowerSeries.coeff m (∏' n : ℕ, ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R m).tendsto _).comp hmul.hasProd.tendsto_prod_nat
  have hconst : ∀ N', N ≤ N' →
      PowerSeries.coeff m (∏ n ∈ Finset.range N',
          ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m (∏ n ∈ Finset.range N,
          ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) := by
    intro N' hle
    induction N', hle using Nat.le_induction with
    | base => rfl
    | succ N' hle ih => rw [Finset.prod_range_succ, coeff_mul_factor_eq (by omega), ih]
  have hev : (fun N' => PowerSeries.coeff m
      (∏ n ∈ Finset.range N', ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24)) =ᶠ[atTop]
      fun _ => PowerSeries.coeff m
        (∏ n ∈ Finset.range N, ((1 : PowerSeries R) - PowerSeries.X ^ (n + 1)) ^ 24) :=
    eventually_atTop.mpr ⟨N, hconst⟩
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hev)

open Polynomial in
private lemma truncPoly_toPowerSeries (N : ℕ) :
    ((truncPoly N : ℂ[X]) : PowerSeries ℂ) =
      ∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by
  rw [truncPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]

open Polynomial in
private lemma truncPoly_eval (N : ℕ) (q : ℂ) :
    (truncPoly N).eval q = ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) ^ 24 := by
  simp [truncPoly, Polynomial.eval_prod]

private lemma tendstoLocallyUniformlyOn_trunc :
    TendstoLocallyUniformlyOn (fun N q => ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) ^ 24) gfun atTop
      (Metric.ball (0 : ℂ) 1) := by
  have h1 : TendstoLocallyUniformlyOn (fun N q => ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)))
      (fun q => ∏' n : ℕ, (1 - q ^ (n + 1))) atTop (Metric.ball (0 : ℂ) 1) := by
    have := ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
      |>.tendstoLocallyUniformlyOn_finsetRange
    refine this.congr (fun N => ?_)
    intro q _
    simp
  have hc : ContinuousOn (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) :=
    ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn
  have hpow : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun N q => (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ k)
      (fun q => (∏' n : ℕ, (1 - q ^ (n + 1))) ^ k) atTop (Metric.ball (0 : ℂ) 1) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero]
      intro u hu x _
      exact ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩
    | succ k ih =>
      simp only [pow_succ]
      exact ih.mul₀ h1 (hc.pow k) hc
  refine ((hpow 24).congr fun N q _ => ?_).congr_right fun q hq => ?_
  · exact (Finset.prod_pow _ _ _).symm
  · exact ((ModularForm.multipliable_one_sub_pow (by simpa using hq)).tprod_pow 24).symm

private lemma differentiableOn_gfun : DifferentiableOn ℂ gfun (Metric.ball (0 : ℂ) 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

open Polynomial in
private lemma tendstoLocallyUniformlyOn_iterate_deriv_trunc (m : ℕ) :
    TendstoLocallyUniformlyOn (fun N q => (derivative^[m] (truncPoly N)).eval q) (deriv^[m] gfun)
      atTop (Metric.ball (0 : ℂ) 1) := by
  induction m with
  | zero =>
    simpa only [Function.iterate_zero, id_eq, truncPoly_eval] using tendstoLocallyUniformlyOn_trunc
  | succ m ih =>
    have h := ih.deriv (Eventually.of_forall fun N =>
        (Polynomial.differentiable _).differentiableOn)
      Metric.isOpen_ball
    rw [Function.iterate_succ', Function.iterate_succ']
    refine h.congr fun N q _ => ?_
    simp only [Function.comp_apply, Polynomial.deriv]

open Polynomial in
private lemma iteratedDeriv_gfun_zero (m : ℕ) :
    iteratedDeriv m gfun 0 = m.factorial * PowerSeries.coeff m etaPow := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hlim : Tendsto (fun N => (derivative^[m] (truncPoly N)).eval 0) atTop
      (𝓝 (deriv^[m] gfun 0)) :=
    (tendstoLocallyUniformlyOn_iterate_deriv_trunc m).tendsto_at h0
  have hev : (fun N => (derivative^[m] (truncPoly N)).eval 0) =ᶠ[atTop]
      fun _ => (m.factorial : ℂ) * PowerSeries.coeff m etaPow := by
    refine eventually_atTop.mpr ⟨m + 1, fun N hN => ?_⟩
    simp only
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul, ← Polynomial.coeff_coe, truncPoly_toPowerSeries,
      coeff_trunc_eq_coeff_tprod ℂ m (by omega), etaPow]
  rw [iteratedDeriv_eq_iterate]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

private lemma hasSum_coeff_etaPow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => PowerSeries.coeff m etaPow * q ^ m) (gfun q) := by
  have hq' : q ∈ Metric.ball (0 : ℂ) 1 := by simpa using hq
  have h := Complex.hasSum_taylorSeries_on_ball differentiableOn_gfun hq'
  refine h.congr_fun fun m => ?_
  rw [iteratedDeriv_gfun_zero, sub_zero, smul_eq_mul, smul_eq_mul]
  field_simp
  rw [mul_div_assoc, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), mul_one]

private lemma hasSum_coeff_X_mul_etaPow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (PowerSeries.X * etaPow) * q ^ m) (q * gfun q) := by
  have h := (hasSum_coeff_etaPow hq).mul_left q
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      PowerSeries.coeff_zero_X_mul,
    sub_zero]
  refine h.congr_fun fun m => ?_
  rw [PowerSeries.coeff_succ_X_mul, pow_succ]
  ring

private lemma discriminant_eq_qParam_mul_gfun (τ : ℍ) :
    ModularForm.discriminant τ = 𝕢 1 (τ : ℂ) * gfun (𝕢 1 (τ : ℂ)) := by
  rw [ModularForm.discriminant_eq_q_prod, gfun]

end ModularCurve

open ModularCurve in
theorem ModularCurve.qExpansion_discriminant_eq_X_mul_tprod :
    UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      PowerSeries.X * ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.X * etaPow) • 𝕢 1 (τ : ℂ) ^ m)
      (CuspForm.discriminant τ) := by
    intro τ
    simp_rw [smul_eq_mul, CuspForm.coe_discriminant, discriminant_eq_qParam_mul_gfun τ]
    exact hasSum_coeff_X_mul_etaPow (by exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ)
  ext m
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    one_mem_strictPeriods_SL (f := CuspForm.discriminant) hsum m
  rw [CuspForm.coe_discriminant] at h
  rw [← h]
  rfl
end

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

private lemma tprod_eq_map_dedekindEtaUnit :
    (∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) =
      dedekindEtaUnit.map (Int.castRingHom ℂ) := by
  ext m
  rw [dedekindEtaUnit, etaProd,
    ← ((PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).tprod_pow 24),
    PowerSeries.coeff_map, ← coeff_trunc_eq_coeff_tprod ℂ m (Nat.lt_succ_self m),
    ← coeff_trunc_eq_coeff_tprod ℤ m (Nat.lt_succ_self m), ← PowerSeries.coeff_map,
    map_prod (PowerSeries.map (Int.castRingHom ℂ))]
  simp

end ModularCurve

open ModularCurve in
theorem ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit :
    UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by
  rw [qExpansion_discriminant_eq_X_mul_tprod, map_mul, PowerSeries.map_X,
    tprod_eq_map_dedekindEtaUnit]
end

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

private def qJ (τ : ℍ) : ℂ := 𝕢 1 (τ : ℂ) * (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)

private def Dq (τ : ℍ) : ℂ := ModularForm.discriminant τ / 𝕢 1 (τ : ℂ)

private lemma Dq_eq (τ : ℍ) : Dq τ = gfun (𝕢 1 (τ : ℂ)) := by
  rw [Dq, discriminant_eq_qParam_mul_gfun,
      mul_div_cancel_left₀ _ (Function.Periodic.qParam_ne_zero _)]

private lemma gfun_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : gfun q ≠ 0 := by
  rw [gfun, (ModularForm.multipliable_one_sub_pow hq).tprod_pow]
  refine pow_ne_zero _ (tprod_one_add_ne_zero_of_summable (f := fun n => -q ^ (n + 1)) ?_ ?_)
  · intro i
    have : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero i)
    intro h
    rw [add_neg_eq_zero] at h
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  · simpa [summable_nat_add_iff 1] using summable_geometric_of_lt_one (norm_nonneg _) hq

private lemma continuousAt_gfun {q : ℂ} (hq : ‖q‖ < 1) : ContinuousAt gfun q :=
  (differentiableOn_gfun.differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).continuousAt

private lemma qJ_eq (τ : ℍ) : qJ τ = ModularForm.E₄ τ ^ 3 / gfun (𝕢 1 (τ : ℂ)) := by
  have hq : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  rw [qJ, discriminant_eq_qParam_mul_gfun]
  field_simp

private lemma qJ_mul_Dq : qJ * Dq = fun τ => ModularForm.E₄ τ ^ 3 := by
  funext τ
  have hq : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  simp only [Pi.mul_apply, qJ, Dq]
  field_simp

private lemma cuspFunction_eqOn {f : ℍ → ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g 0)
    (hfg : ∀ τ : ℍ, f τ = g (𝕢 1 (τ : ℂ))) : Set.EqOn (cuspFunction 1 f) g (Metric.ball 0 1) := by
  have hne : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → cuspFunction 1 f q = g q := by
    intro q hq hq0
    have him := Function.Periodic.im_invQParam_pos_of_norm_lt_one Real.zero_lt_one hq hq0
    rw [cuspFunction, Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hq0, Function.comp_apply,
      hfg, ofComplex_apply_of_im_pos him, Function.Periodic.qParam_right_inv one_ne_zero hq0]
  intro q hq
  rw [Metric.mem_ball, dist_zero_right] at hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    refine Tendsto.limUnder_eq ?_
    have hball : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), ‖q‖ < 1 :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) one_pos) fun q hq => by
        simpa using hq
    have h1 : ∀ᶠ q : ℂ in 𝓝[≠] (0 : ℂ), ‖q‖ < 1 ∧ q ≠ 0 :=
      (hball.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    have hev : g =ᶠ[𝓝[≠] (0 : ℂ)] Function.Periodic.cuspFunction 1 (f ∘ ofComplex) := by
      filter_upwards [h1] with q hq'
      exact (hne q hq'.1 hq'.2).symm
    exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  · exact hne q hq hq0

private lemma cuspFunction_Dq : Set.EqOn (cuspFunction 1 Dq) gfun (Metric.ball 0 1) :=
  cuspFunction_eqOn (continuousAt_gfun (by simp)) Dq_eq

private lemma cuspFunction_qJ : Set.EqOn (cuspFunction 1 qJ)
    (fun q => cuspFunction 1 ⇑ModularForm.E₄ q ^ 3 / gfun q) (Metric.ball 0 1) := by
  refine cuspFunction_eqOn ?_ fun τ => ?_
  · have hE : ContinuousAt (cuspFunction 1 ⇑ModularForm.E₄) 0 :=
      (ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos
        one_mem_strictPeriods_SL).continuousAt
    exact (hE.pow 3).div (continuousAt_gfun (by simp)) (gfun_ne_zero (by simp))
  · show qJ τ = cuspFunction 1 ⇑ModularForm.E₄ (𝕢 1 (τ : ℂ)) ^ 3 / gfun (𝕢 1 (τ : ℂ))
    rw [qJ_eq, SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL
      one_ne_zero]

private lemma analyticAt_cuspFunction_Dq : AnalyticAt ℂ (cuspFunction 1 Dq) 0 := by
  have h : AnalyticAt ℂ gfun 0 :=
    differentiableOn_gfun.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))
  exact h.congr (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp))
    fun q hq => (cuspFunction_Dq hq).symm)

private lemma analyticAt_cuspFunction_qJ : AnalyticAt ℂ (cuspFunction 1 qJ) 0 := by
  have hE : AnalyticAt ℂ (cuspFunction 1 ⇑ModularForm.E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL
  have hg : AnalyticAt ℂ gfun 0 :=
    differentiableOn_gfun.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))
  have h : AnalyticAt ℂ (fun q => cuspFunction 1 ⇑ModularForm.E₄ q ^ 3 / gfun q) 0 :=
    (hE.pow 3).div hg (gfun_ne_zero (by simp))
  exact h.congr (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp))
    fun q hq => (cuspFunction_qJ hq).symm)

private lemma qExpansion_qParam_fun : qExpansion 1 (fun τ : ℍ => 𝕢 1 (τ : ℂ)) = PowerSeries.X := by
  have hcusp : Set.EqOn (cuspFunction 1 (fun τ : ℍ => 𝕢 1 (τ : ℂ))) id (Metric.ball 0 1) :=
    cuspFunction_eqOn continuousAt_id fun τ => rfl
  have hev : cuspFunction 1 (fun τ : ℍ => 𝕢 1 (τ : ℂ)) =ᶠ[𝓝 0] id :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp)) hcusp
  ext m
  rw [qExpansion_coeff, hev.iteratedDeriv_eq, PowerSeries.coeff_X]
  cases m with
  | zero => simp
  | succ m =>
    rw [iteratedDeriv_succ']
    have hd : deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) := by funext x; exact deriv_id x
    rw [hd, iteratedDeriv_const]
    by_cases hm : m = 0
    · subst hm; simp
    · simp [hm]

private lemma qExpansion_Dq' : qExpansion 1 Dq = dedekindEtaUnit.map (Int.castRingHom ℂ) := by
  have han : AnalyticAt ℂ (cuspFunction 1 (fun τ : ℍ => 𝕢 1 (τ : ℂ))) 0 := by
    have hcusp : Set.EqOn (cuspFunction 1 (fun τ : ℍ => 𝕢 1 (τ : ℂ))) id (Metric.ball 0 1) :=
      cuspFunction_eqOn continuousAt_id fun τ => rfl
    exact analyticAt_id.congr (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp))
      fun q hq => (hcusp hq).symm)
  have hmul := qExpansion_mul han analyticAt_cuspFunction_Dq
  have hfun : ((fun τ : ℍ => 𝕢 1 (τ : ℂ)) * Dq) = ModularForm.discriminant := by
    funext τ
    simp only [Pi.mul_apply, Dq]
    rw [mul_div_cancel₀ _ (Function.Periodic.qParam_ne_zero _)]
  rw [hfun, qExpansion_qParam_fun, qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, map_mul,
    PowerSeries.map_X] at hmul
  exact (mul_left_cancel₀ PowerSeries.X_ne_zero hmul).symm

/-- **The `q`-expansion of `E₄` has integer coefficients.** The `q`-expansion
(`UpperHalfPlane.qExpansion 1`) of the weight-`4` Eisenstein series `ModularForm.E₄` is the image
in `ℂ⟦X⟧` of the integer power series `ModularCurve.eisenstein4 = 1 + 240 ∑_{n ≥ 1} σ₃(n) Xⁿ`,
whose constant term is `1` (`ModularCurve.constantCoeff_eisenstein4`).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.5, p. 3: "g₂(τ) = (4π⁴/3)(1 + 240 ∑_{n=1}^∞ σ₃(n)qⁿ)", with
"σₖ(n) = ∑_{d|n} dᵏ" and "q = e^{2πiτ}"; the normalization `g₂ = (4π⁴/3) E₄` is not proved
here. -/
theorem qExpansion_E4_eq_map_eisenstein4 : qExpansion 1 ⇑ModularForm.E₄ =
    PowerSeries.map (Int.castRingHom ℂ) eisenstein4 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩ m, PowerSeries.coeff_map, eisenstein4,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four,
      ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast]
    push_cast
    ring

/-- The integer power series `1 - 504 ∑_{n ≥ 1} σ₅(n) Xⁿ`, where `σ₅(n) = ∑_{d ∣ n} d⁵`; it is
the `q`-expansion of `ModularForm.E₆` (`ModularCurve.qExpansion_E6_eq_map_eisenstein6`).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.5, p. 3: "g₃(τ) = (8π⁶/27)(1 − 504 ∑_{n=1}^∞ σ₅(n)qⁿ)". -/
def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

/-- The constant term of `ModularCurve.eisenstein6` is `1`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.5, p. 3 (the constant term `1` of
"1 − 504 ∑_{n=1}^∞ σ₅(n)qⁿ"). -/
@[simp]
theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein6]

private lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5, Nat.choose]

/-- **The `q`-expansion of `E₆` has integer coefficients.** The `q`-expansion
(`UpperHalfPlane.qExpansion 1`) of the weight-`6` Eisenstein series `ModularForm.E₆` is the image
in `ℂ⟦X⟧` of the integer power series `ModularCurve.eisenstein6 = 1 - 504 ∑_{n ≥ 1} σ₅(n) Xⁿ`,
whose constant term is `1` (`ModularCurve.constantCoeff_eisenstein6`).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Lemma 19.5, p. 3: "g₃(τ) = (8π⁶/27)(1 − 504 ∑_{n=1}^∞ σ₅(n)qⁿ)", with
"σₖ(n) = ∑_{d|n} dᵏ" and "q = e^{2πiτ}"; the normalization `g₃ = (8π⁶/27) E₆` is not proved
here. -/
theorem qExpansion_E6_eq_map_eisenstein6 : qExpansion 1 ⇑ModularForm.E₆ =
    PowerSeries.map (Int.castRingHom ℂ) eisenstein6 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩ m, PowerSeries.coeff_map, eisenstein6,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_six, ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_sum,
      Int.cast_pow, Int.cast_natCast]
    push_cast
    ring

private lemma qExpansion_qJ : qExpansion 1 qJ = jNum.map (Int.castRingHom ℂ) := by
  have hmul := qExpansion_mul analyticAt_cuspFunction_qJ analyticAt_cuspFunction_Dq
  rw [qJ_mul_Dq, qExpansion_Dq'] at hmul
  have hE3 : qExpansion 1 (fun τ =>
      ModularForm.E₄ τ ^ 3) = (eisenstein4.map (Int.castRingHom ℂ)) ^ 3 := by
    rw [← qExpansion_E4_eq_map_eisenstein4,
      ← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3,
      ModularForm.coe_pow]
    rfl
  rw [hE3] at hmul
  have hinv :
      dedekindEtaUnit.map (Int.castRingHom ℂ) * dedekindEtaUnitInv.map (Int.castRingHom ℂ) = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv, map_one]
  calc qExpansion 1 qJ
      = qExpansion 1 qJ * (dedekindEtaUnit.map (Int.castRingHom ℂ) *
          dedekindEtaUnitInv.map (Int.castRingHom ℂ)) := by rw [hinv, mul_one]
    _ = (eisenstein4.map (Int.castRingHom ℂ)) ^ 3 * dedekindEtaUnitInv.map (Int.castRingHom ℂ) := by
          rw [← mul_assoc, ← hmul]
    _ = jNum.map (Int.castRingHom ℂ) := by rw [jNum, map_mul, map_pow]

private lemma periodic_qJ : Function.Periodic (qJ ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have hE := SlashInvariantFormClass.periodic_comp_ofComplex (h := 1) ModularForm.E₄
      one_mem_strictPeriods_SL w
    have hΔ := SlashInvariantFormClass.periodic_comp_ofComplex (h := 1) CuspForm.discriminant
      one_mem_strictPeriods_SL w
    simp only [Function.comp_apply, CuspForm.coe_discriminant, Complex.ofReal_one] at hE hΔ
    rw [ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw'] at hE hΔ
    have hq : 𝕢 1 (w + 1) = 𝕢 1 w := by
      simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one,
        Complex.exp_add, Complex.exp_two_pi_mul_I]
    simp only [Function.comp_apply, qJ, hE, hΔ, ofComplex_apply_of_im_pos hw,
      ofComplex_apply_of_im_pos hw', UpperHalfPlane.coe_mk, hq]
  · push Not at hw
    have hw' : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_eq_of_im_nonpos hw' hw]

private lemma gfun_zero : gfun 0 = 1 := by
  simp [gfun]

private lemma mdiff_qJ :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) qJ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hE : DifferentiableOn ℂ (⇑ModularForm.E₄ ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo ModularForm.E₄)
  have hΔ : DifferentiableOn ℂ (ModularForm.discriminant ∘ ofComplex) {z : ℂ | 0 < z.im} := by
    have h := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo CuspForm.discriminant)
    simpa only [CuspForm.coe_discriminant] using h
  have hq : DifferentiableOn ℂ (fun z : ℂ => 𝕢 1 ((ofComplex z : ℍ) : ℂ)) {z : ℂ | 0 < z.im} :=
    (Function.Periodic.differentiable_qParam (h := (1 : ℝ))).differentiableOn.congr
      fun z hz => by simp only [ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]
  have h : DifferentiableOn ℂ (fun z : ℂ => 𝕢 1 ((ofComplex z : ℍ) : ℂ) *
      ((⇑ModularForm.E₄ ∘ ofComplex) z ^ 3 / (ModularForm.discriminant ∘ ofComplex) z))
      {z : ℂ | 0 < z.im} :=
    hq.mul ((hE.pow 3).div hΔ fun z _ => ModularForm.discriminant_ne_zero _)
  exact h.congr fun z _ => by simp only [Function.comp_apply, qJ]

private lemma tendsto_gfun_qParam : Tendsto (fun τ : ℍ => gfun (𝕢 1 (τ : ℂ))) atImInfty (𝓝 1) := by
  have h := (continuousAt_gfun (q := 0) (by simp)).tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rwa [gfun_zero] at h

private lemma isBoundedAtImInfty_qJ : IsBoundedAtImInfty qJ := by
  have hE : IsBoundedAtImInfty ⇑ModularForm.E₄ := ModularFormClass.bdd_at_infty ModularForm.E₄
  have hE3 : BoundedAtFilter atImInfty (fun τ : ℍ => ModularForm.E₄ τ ^ 3) := by
    have h := (hE.mul hE).mul hE
    refine (show (fun τ : ℍ => ModularForm.E₄ τ ^ 3) = ⇑ModularForm.E₄ * ⇑ModularForm.E₄ *
      ⇑ModularForm.E₄ from ?_) ▸ h
    funext τ; simp only [Pi.mul_apply]; ring
  have hg : BoundedAtFilter atImInfty (fun τ : ℍ => (gfun (𝕢 1 (τ : ℂ)))⁻¹) :=
    (tendsto_gfun_qParam.inv₀ one_ne_zero).isBigO_one ℝ
  have h := hE3.mul hg
  refine (show qJ = (fun τ : ℍ => ModularForm.E₄ τ ^ 3) * fun τ : ℍ => (gfun (𝕢 1 (τ : ℂ)))⁻¹
    from ?_) ▸ h
  funext τ
  simp only [Pi.mul_apply, qJ_eq, div_eq_mul_inv]

end ModularCurve

open ModularCurve in
theorem ModularCurve.hasSum_jNum_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ =>
        ((PowerSeries.coeff m ModularCurve.jNum : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (Function.Periodic.qParam 1 (τ : ℂ) *
        (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by
  have h := hasSum_qExpansion one_pos periodic_qJ mdiff_qJ isBoundedAtImInfty_qJ τ
  rw [qExpansion_qJ] at h
  refine h.congr_fun fun m => ?_
  rw [PowerSeries.coeff_map, smul_eq_mul, eq_intCast]
end

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

end ModularCurve

open ModularCurve in
theorem ModularCurve.hasSum_jq_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ =>
        ((ModularCurve.jq.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
  set q : ℂ := 𝕢 1 (τ : ℂ) with hqdef
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have h := (hasSum_jNum_qParam τ).mul_left q⁻¹
  rw [← hqdef, inv_mul_cancel_left₀ hq] at h
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) - 1 := fun a b hab => by
    simpa using hab
  rw [← hinj.hasSum_iff]
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply]
    rw [jq, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, sub_add_cancel, jNumQ,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, Rat.cast_intCast,
      zpow_sub_one₀ hq, zpow_natCast]
    ring
  · intro m hm
    have hm' : m < -1 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m + 1).toNat, by simp; omega⟩
    rw [coeff_jq_of_lt hm', Rat.cast_zero, zero_mul]
end

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

private theorem hasSum_single_mul_coe_iff (k : ℤ) (P : PowerSeries ℂ) {q : ℂ} (hq : q ≠ 0) (t : ℂ) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m)
        (t * q ^ k) ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) t := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ =>
      (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) ∘
        (fun n : ℕ => (n : ℤ) + k) = fun n : ℕ => (PowerSeries.coeff n P * q ^ n) * q ^ k := by
      funext n
      simp only [Function.comp_apply]
      rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.coeff_coe_powerSeries,
          zpow_add₀ hq,
        zpow_natCast]
      ring
    rw [hfg]
    exact hasSum_mul_right_iff (zpow_ne_zero k hq)
  · intro m hm
    have hmk : m - k < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m - k).toNat, by simp only; omega⟩
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe,
        ite_eq_left hmk,
      zero_mul]

theorem _root_.ModularCurve.hasSum_qParam_mul_laurent (h : ℝ) (hh : 0 < h) (A B : LaurentSeries ℂ)
    (F G : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : ℍ, HasSum (fun m : ℤ => B.coeff m * 𝕢 h (τ : ℂ) ^ m) (G τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (A * B).coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ * G τ) := by
  have hq0 : ∀ τ : ℍ, 𝕢 h (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _
  set F' : ℍ → ℂ := fun τ => F τ * (𝕢 h (τ : ℂ) ^ A.order)⁻¹ with hF'
  set G' : ℍ → ℂ := fun τ => G τ * (𝕢 h (τ : ℂ) ^ B.order)⁻¹ with hG'
  have hA' : ∀ τ : ℍ,
      HasSum (fun n : ℕ => PowerSeries.coeff n A.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n) (F' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff A.order A.powerSeriesPart (hq0 τ),
        A.single_order_mul_powerSeriesPart,
      hF', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hA τ
  have hB' : ∀ τ : ℍ,
      HasSum (fun n : ℕ => PowerSeries.coeff n B.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n) (G' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff B.order B.powerSeriesPart (hq0 τ),
        B.single_order_mul_powerSeriesPart,
      hG', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hB τ
  have H := ModularCurve.hasSum_qParam_mul h hh A.powerSeriesPart B.powerSeriesPart F' G' hA' hB' τ
  have hAB : HahnSeries.single (A.order + B.order) (1 : ℂ) *
      ((A.powerSeriesPart * B.powerSeriesPart : PowerSeries ℂ) : LaurentSeries ℂ) = A * B := by
    conv_rhs => rw [← A.single_order_mul_powerSeriesPart, ← B.single_order_mul_powerSeriesPart]
    rw [PowerSeries.coe_mul, ← one_mul (1 : ℂ), ← HahnSeries.single_mul_single, one_mul]
    ring
  have hFG : F τ * G τ = F' τ * G' τ * 𝕢 h (τ : ℂ) ^ (A.order + B.order) := by
    have hqτ := hq0 τ
    simp only [hF', hG']
    rw [zpow_add₀ hqτ]
    field_simp
  rw [← hAB, hFG]
  exact (hasSum_single_mul_coe_iff _ _ (hq0 τ) _).mpr H

end Realized

end ModularCurve

end

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial
open scoped MatrixGroups ModularForm OnePoint

namespace ModularCurve

theorem E4_cube_div_discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE : ModularForm.E₄ (γ • τ) = denom (mapGL ℝ γ) τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) hγ τ
  have hΔ : ModularForm.discriminant (γ • τ)
      = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
    simp only [CuspForm.coe_discriminant] at this
    exact this
  have hd : denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [hE, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  norm_num
  rw [mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

end ModularCurve

end
