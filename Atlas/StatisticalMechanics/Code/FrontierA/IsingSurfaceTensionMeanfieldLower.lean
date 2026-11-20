/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy
import Code.FrontierA.IsingSurfaceTensionLebowitzPfisterLower
import Code.Sharpness.IsingSharpnessUnconditional

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section



theorem standardCubicInterfaceDensity_nonneg
    {beta : Real} (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n) :
    0 <= standardCubicInterfaceDensity beta n := by
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    beta n hn]
  unfold rectangularPrismInterfaceDensity
  exact div_nonneg
    (StatMech.Ising.rectangularDobrushinFreeEnergy_nonneg
      (by norm_num) hbeta (2 * n + 1) (2 * n + 1) n)
    (sq_nonneg _)




theorem standardCubicInterfaceDensity_ge_meanfield_increment
    {betaC a beta : Real} (hbetaC : 0 < betaC)
    (hsharp : forall gamma, betaC <= gamma ->
      Real.sqrt (1 - (betaC / gamma) ^ 2) <= magnetization 3 gamma)
    (ha : betaC < a) (hab : a < beta) (n : Nat) (hn : 0 < n) :
    2 * (Real.sqrt (1 - (betaC / a) ^ 2)) ^ 2 * (beta - a) <=
      standardCubicInterfaceDensity beta n := by
  let s : Real := Real.sqrt (1 - (betaC / a) ^ 2)
  have ha0 : 0 < a := hbetaC.trans ha
  have hs0 : 0 <= s := Real.sqrt_nonneg _
  have hdiff : Differentiable Real
      (fun gamma => standardCubicInterfaceDensity gamma n) := by
    intro gamma
    exact (hasDerivAt_standardCubicInterfaceDensity gamma n).differentiableAt
  have hderiv : forall gamma, gamma ∈ interior (Icc a beta) ->
      2 * s ^ 2 <=
        deriv (fun b => standardCubicInterfaceDensity b n) gamma := by
    intro gamma hgamma
    rw [interior_Icc] at hgamma
    have hagamma : a <= gamma := hgamma.1.le
    have hgamma0 : 0 < gamma := ha0.trans_le hagamma
    have hratio0 : 0 <= betaC / gamma := div_nonneg hbetaC.le hgamma0.le
    have hratioa0 : 0 <= betaC / a := div_nonneg hbetaC.le ha0.le
    have hratio : betaC / gamma <= betaC / a :=
      div_le_div_of_nonneg_left hbetaC.le ha0 hagamma
    have hrad : 1 - (betaC / a) ^ 2 <= 1 - (betaC / gamma) ^ 2 := by
      have hsquares : (betaC / gamma) ^ 2 <= (betaC / a) ^ 2 :=
        (sq_le_sq₀ hratio0 hratioa0).2 hratio
      linarith
    have hsM : s <= magnetization 3 gamma := by
      exact (Real.sqrt_le_sqrt hrad).trans
        (hsharp gamma (ha.le.trans hagamma))
    have hfinite :=
      standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq
        gamma hgamma0.le n hn
    have hsquares : s ^ 2 <= magnetization 3 gamma ^ 2 :=
      (sq_le_sq₀ hs0 (hs0.trans hsM)).2 hsM
    linarith
  have hgrowth := (convex_Icc a beta).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn hderiv
    a
    (show a ∈ Icc a beta from ⟨le_rfl, hab.le⟩)
    beta
    (show beta ∈ Icc a beta from ⟨hab.le, le_rfl⟩) hab.le
  have hnonneg := standardCubicInterfaceDensity_nonneg ha0.le n hn
  dsimp [s] at hgrowth ⊢
  linarith




theorem rectangularIsingSurfaceTension_pos_of_prismComparison
    {beta : Real} (hcritical : betaC 3 < beta)
    (hprism : HasPrismCubicalSurfaceComparison beta) :
    0 < rectangularIsingSurfaceTension beta := by
  have hbetaC : 0 < betaC 3 := by
    have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by norm_num)
    have hcrit := tildeBetaCIsing_pos (d := 3) (by norm_num)
    have hsqrt : forall gamma, tildeBetaCIsing 3 <= gamma ->
        Real.sqrt (1 - (tildeBetaCIsing 3 / gamma) ^ 2) <=
          magnetization 3 gamma := fun gamma hgamma =>
      sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hgamma
    rw [bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by norm_num) hsqrt]
    exact hcrit
  have hsharp := (ising_sharpness_unconditional (d := 3) (by norm_num)).1
  let a : Real := (betaC 3 + beta) / 2
  let c : Real :=
    2 * (Real.sqrt (1 - (betaC 3 / a) ^ 2)) ^ 2 * (beta - a)
  have ha : betaC 3 < a := by dsimp [a]; linarith
  have hab : a < beta := by dsimp [a]; linarith
  have ha0 : 0 < a := hbetaC.trans ha
  have hratio0 : 0 <= betaC 3 / a := div_nonneg hbetaC.le ha0.le
  have hratio1 : betaC 3 / a < 1 := (div_lt_one ha0).2 ha
  have hrad : 0 < 1 - (betaC 3 / a) ^ 2 := by nlinarith
  have hc : 0 < c := by
    dsimp [c]
    rw [Real.sq_sqrt hrad.le]
    positivity
  have hlower : forall n, 0 < n -> c <= standardCubicInterfaceDensity beta n := by
    intro n hn
    dsimp [c]
    exact standardCubicInterfaceDensity_ge_meanfield_increment
      hbetaC hsharp ha hab n hn
  have hlim := standardCubicInterfaceDensity_tendsto_of_prismComparison
    (hbetaC.trans hcritical) hprism
  have hcle : c <= rectangularIsingSurfaceTension beta :=
    ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hlower n (by omega))
  exact hc.trans_le hcle

end

end StatMech.FrontierA
