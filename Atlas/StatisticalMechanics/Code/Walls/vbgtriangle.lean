/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Ising.GKS
import Code.Ising.AizenmanBarsky
import Code.Ising.IsingFKGLayer
import Code.Walls.ghc_urselleqgap

open scoped BigOperators
open Finset

namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000



variable {Ω : Type*} [Fintype Ω]


noncomputable def vbg_exp (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, μ ω * f ω


noncomputable def vbg_cov (μ : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  vbg_exp μ (fun ω => f ω * g ω) - vbg_exp μ f * vbg_exp μ g


noncomputable def vbg_var (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ := vbg_cov μ f f



noncomputable def vbg_condPlus (μ : Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  μ ω * Y ω / vbg_exp μ Y


noncomputable def vbg_condMinus (μ : Ω → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  μ ω * (1 - Y ω) / (1 - vbg_exp μ Y)


noncomputable def vbg_covPlus (μ : Ω → ℝ) (Y f g : Ω → ℝ) : ℝ :=
  vbg_cov (vbg_condPlus μ Y) f g


noncomputable def vbg_varPlus (μ : Ω → ℝ) (Y f : Ω → ℝ) : ℝ :=
  vbg_var (vbg_condPlus μ Y) f


noncomputable def vbg_covMinus (μ : Ω → ℝ) (Y f g : Ω → ℝ) : ℝ :=
  vbg_cov (vbg_condMinus μ Y) f g


noncomputable def vbg_varMinus (μ : Ω → ℝ) (Y f : Ω → ℝ) : ℝ :=
  vbg_var (vbg_condMinus μ Y) f



theorem vbg_exp_add (μ : Ω → ℝ) (f g : Ω → ℝ) :
    vbg_exp μ (fun ω => f ω + g ω) = vbg_exp μ f + vbg_exp μ g := by
  unfold vbg_exp; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem vbg_exp_const_mul (μ : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    vbg_exp μ (fun ω => c * f ω) = c * vbg_exp μ f := by
  unfold vbg_exp; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)


theorem vbg_exp_reweight (μ w : Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    vbg_exp (fun ω => μ ω * w ω / c) f = (∑ ω, μ ω * w ω * f ω) / c := by
  unfold vbg_exp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun ω _ => by ring)








section Prop1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)



theorem vbg_expPlus_eq (f : Ω → ℝ) :
    vbg_exp (vbg_condPlus μ Y) f = (∑ ω, μ ω * Y ω * f ω) / vbg_exp μ Y := by
  unfold vbg_condPlus
  exact vbg_exp_reweight μ Y (vbg_exp μ Y) f



theorem vbg_expMinus_eq (f : Ω → ℝ) :
    vbg_exp (vbg_condMinus μ Y) f = (∑ ω, μ ω * (1 - Y ω) * f ω) / (1 - vbg_exp μ Y) := by
  unfold vbg_condMinus
  exact vbg_exp_reweight μ (fun ω => 1 - Y ω) (1 - vbg_exp μ Y) f












theorem vbg_prop1 (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1) :
    (vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z)
        * (vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X)
      = (vbg_exp μ Y * vbg_covPlus μ Y X Z + (1 - vbg_exp μ Y) * vbg_covMinus μ Y X Z)
        * (vbg_var μ X * vbg_var μ Y - vbg_cov μ X Y ^ 2) := by
  
  set p := vbg_exp μ Y with hp
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hq_ne : (1 - p) ≠ 0 := by intro h; apply absurd hp1; linarith [sub_eq_zero.mp h]
  
  simp only [vbg_varPlus, vbg_varMinus, vbg_covPlus, vbg_covMinus, vbg_var, vbg_cov,
    vbg_expPlus_eq, vbg_expMinus_eq, ← hp]
  
  set AX := ∑ ω, μ ω * Y ω * X ω with hAX
  set AZ := ∑ ω, μ ω * Y ω * Z ω with hAZ
  set AXZ := ∑ ω, μ ω * Y ω * (X ω * Z ω) with hAXZ
  set AXX := ∑ ω, μ ω * Y ω * (X ω * X ω) with hAXX
  set BX := ∑ ω, μ ω * (1 - Y ω) * X ω with hBX
  set BZ := ∑ ω, μ ω * (1 - Y ω) * Z ω with hBZ
  set BXZ := ∑ ω, μ ω * (1 - Y ω) * (X ω * Z ω) with hBXZ
  set BXX := ∑ ω, μ ω * (1 - Y ω) * (X ω * X ω) with hBXX
  
  
  
  have eEX : vbg_exp μ X = AX + BX := by
    rw [hAX, hBX]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEZ : vbg_exp μ Z = AZ + BZ := by
    rw [hAZ, hBZ]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEXZ : vbg_exp μ (fun ω => X ω * Z ω) = AXZ + BXZ := by
    rw [hAXZ, hBXZ]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEXX : vbg_exp μ (fun ω => X ω * X ω) = AXX + BXX := by
    rw [hAXX, hBXX]; unfold vbg_exp; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have eEYY : vbg_exp μ (fun ω => Y ω * Y ω) = p := by
    rw [hp]; unfold vbg_exp
    exact Finset.sum_congr rfl (fun ω _ => by simp only []; rw [hY ω])
  have eEXY : vbg_exp μ (fun ω => X ω * Y ω) = AX := by
    rw [hAX]; unfold vbg_exp; exact Finset.sum_congr rfl (fun ω _ => by simp only []; ring)
  have eEYZ : vbg_exp μ (fun ω => Y ω * Z ω) = AZ := by
    rw [hAZ]; unfold vbg_exp; exact Finset.sum_congr rfl (fun ω _ => by simp only []; ring)
  
  rw [eEX, eEZ, eEXZ, eEXX, eEYY, eEXY, eEYZ]
  field_simp
  ring







theorem vbg_cov_centered (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : Ω → ℝ) :
    vbg_cov μ f g = ∑ ω, μ ω * ((f ω - vbg_exp μ f) * (g ω - vbg_exp μ g)) := by
  unfold vbg_cov vbg_exp
  have hexp : ∀ (c : ℝ) (φ : Ω → ℝ), (∑ ω, μ ω * (c * φ ω)) = c * ∑ ω, μ ω * φ ω := by
    intro c φ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)
  have expand : ∀ ω, μ ω * ((f ω - (∑ ω', μ ω' * f ω')) * (g ω - (∑ ω', μ ω' * g ω')))
      = μ ω * (f ω * g ω)
        - (∑ ω', μ ω' * g ω') * (μ ω * f ω)
        - (∑ ω', μ ω' * f ω') * (μ ω * g ω)
        + ((∑ ω', μ ω' * f ω') * (∑ ω', μ ω' * g ω')) * μ ω := fun ω => by ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hμ, mul_one]
  ring


theorem vbg_var_nonneg (μ : Ω → ℝ) (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f : Ω → ℝ) :
    0 ≤ vbg_var μ f := by
  unfold vbg_var
  rw [vbg_cov_centered μ hμ]
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hμ0 ω) (mul_self_nonneg _)



theorem vbg_cauchy_schwarz (μ : Ω → ℝ) (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f g : Ω → ℝ) :
    vbg_cov μ f g ^ 2 ≤ vbg_var μ f * vbg_var μ g := by
  set a : Ω → ℝ := fun ω => f ω - vbg_exp μ f with ha
  set b : Ω → ℝ := fun ω => g ω - vbg_exp μ g with hb
  have hcov : vbg_cov μ f g = ∑ ω, μ ω * a ω * b ω := by
    rw [vbg_cov_centered μ hμ]; exact Finset.sum_congr rfl (fun ω _ => by rw [ha, hb]; ring)
  have hvf : vbg_var μ f = ∑ ω, μ ω * a ω ^ 2 := by
    unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by rw [ha]; ring)
  have hvg : vbg_var μ g = ∑ ω, μ ω * b ω ^ 2 := by
    unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by rw [hb]; ring)
  rw [hcov, hvf, hvg]
  
  have key : (∑ ω, μ ω * a ω * b ω) ^ 2
      ≤ (∑ ω, μ ω * a ω ^ 2) * (∑ ω, μ ω * b ω ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ)
      (f := fun ω => μ ω * a ω ^ 2) (g := fun ω => μ ω * b ω ^ 2)
      (r := fun ω => μ ω * a ω * b ω)
    · intro ω _; exact mul_nonneg (hμ0 ω) (sq_nonneg _)
    · intro ω _; exact mul_nonneg (hμ0 ω) (sq_nonneg _)
    · intro ω _; nlinarith [sq_nonneg (a ω), sq_nonneg (b ω), hμ0 ω]
  exact key




theorem vbg_condPlus_nonneg {π Y : Ω → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hp0 : 0 < vbg_exp π Y) : 0 ≤ vbg_condPlus π Y := by
  intro ω
  unfold vbg_condPlus
  exact div_nonneg (mul_nonneg (hπ0 ω) (hY0 ω)) hp0.le


theorem vbg_condPlus_norm {π Y : Ω → ℝ} (hp0 : 0 < vbg_exp π Y) :
    ∑ ω, vbg_condPlus π Y ω = 1 := by
  unfold vbg_condPlus
  rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hp0)]
  unfold vbg_exp
  exact Finset.sum_congr rfl (fun ω _ => by ring)


theorem vbg_exp_one_sub {π Y : Ω → ℝ} (hπ : ∑ ω, π ω = 1) :
    vbg_exp π (fun ω => 1 - Y ω) = 1 - vbg_exp π Y := by
  unfold vbg_exp
  rw [show (∑ ω, π ω * (1 - Y ω)) = (∑ ω, π ω) - ∑ ω, π ω * Y ω by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring), hπ]



theorem vbg_condMinus_eq_condPlus {π Y : Ω → ℝ} (hπ : ∑ ω, π ω = 1) :
    vbg_condMinus π Y = vbg_condPlus π (fun ω => 1 - Y ω) := by
  funext ω
  unfold vbg_condMinus vbg_condPlus
  rw [vbg_exp_one_sub hπ]









section Degenerate

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)



theorem vbg_ae_const_of_var_zero (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (f : Ω → ℝ)
    (hvar : vbg_var μ f = 0) : ∀ ω, μ ω * (f ω - vbg_exp μ f) = 0 := by
  
  have hsum : ∑ ω, μ ω * (f ω - vbg_exp μ f) ^ 2 = 0 := by
    rw [← hvar]; unfold vbg_var; rw [vbg_cov_centered μ hμ]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have hnn : ∀ ω ∈ (Finset.univ : Finset Ω), 0 ≤ μ ω * (f ω - vbg_exp μ f) ^ 2 :=
    fun ω _ => mul_nonneg (hμ0 ω) (sq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  intro ω
  have := hzero ω (Finset.mem_univ ω)
  
  rcases mul_eq_zero.mp this with h | h
  · rw [h]; ring
  · have : f ω - vbg_exp μ f = 0 := by nlinarith [sq_nonneg (f ω - vbg_exp μ f)]
    rw [this]; ring





theorem vbg_thm1_degenerate (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1)
    (hVP : vbg_varPlus μ Y X = 0) (hVM : vbg_varMinus μ Y X = 0) :
    vbg_var μ Y * vbg_cov μ X Z = vbg_cov μ X Y * vbg_cov μ Y Z := by
  have hp0' := hp0
  have hYbnd : ∀ ω, Y ω ≤ 1 := by
    intro ω; nlinarith [hY ω, sq_nonneg (Y ω - 1), sq_nonneg (Y ω)]
  have hcompl0 : (0 : Ω → ℝ) ≤ (fun ω => 1 - Y ω) := by
    intro ω; show (0 : ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]
  have hY0 : (0 : Ω → ℝ) ≤ Y := by
    intro ω; show (0:ℝ) ≤ Y ω; nlinarith [hY ω, sq_nonneg (Y ω)]
  set a₁ := vbg_exp (vbg_condPlus μ Y) X with ha1  
  set a₀ := vbg_exp (vbg_condMinus μ Y) X with ha0  
  
  have hpm := vbg_exp_one_sub (Y := Y) hμ
  have hq0 : 0 < vbg_exp μ (fun ω => 1 - Y ω) := by rw [hpm]; linarith
  have hplus := vbg_ae_const_of_var_zero (vbg_condPlus μ Y)
    (vbg_condPlus_nonneg hμ0 hY0 hp0) (vbg_condPlus_norm hp0) X hVP
  have hminus := vbg_ae_const_of_var_zero (vbg_condMinus μ Y)
    (by rw [vbg_condMinus_eq_condPlus hμ]; exact vbg_condPlus_nonneg hμ0 hcompl0 hq0)
    (by rw [vbg_condMinus_eq_condPlus hμ]; exact vbg_condPlus_norm hq0) X hVM
  
  have hplus' : ∀ ω, μ ω * Y ω * (X ω - a₁) = 0 := by
    intro ω
    have h := hplus ω
    
    have hp := congrArg (fun t => vbg_exp μ Y * t) h
    simp only [mul_zero] at hp
    rw [← ha1] at hp
    have hpe : vbg_exp μ Y * (vbg_condPlus μ Y ω * (X ω - a₁)) = μ ω * Y ω * (X ω - a₁) := by
      unfold vbg_condPlus; field_simp
    rw [hpe] at hp; exact hp
  have hminus' : ∀ ω, μ ω * (1 - Y ω) * (X ω - a₀) = 0 := by
    intro ω
    have h := hminus ω
    have hp := congrArg (fun t => vbg_exp μ (fun ω => 1 - Y ω) * t) h
    simp only [mul_zero] at hp
    rw [← ha0] at hp
    have hq_ne : (1 - vbg_exp μ Y) ≠ 0 := by intro h; apply absurd hp1; linarith [sub_eq_zero.mp h]
    have hpe : vbg_exp μ (fun ω => 1 - Y ω) * (vbg_condMinus μ Y ω * (X ω - a₀))
        = μ ω * (1 - Y ω) * (X ω - a₀) := by
      unfold vbg_condMinus; rw [hpm]; field_simp
    rw [hpe] at hp; exact hp
  
  have haffine : ∀ ω, μ ω * X ω = μ ω * (a₀ + (a₁ - a₀) * Y ω) := by
    intro ω
    have h1 := hplus' ω; have h2 := hminus' ω
    nlinarith [h1, h2, hY ω]
  
  set c := a₁ - a₀ with hc
  have eEX : vbg_exp μ X = a₀ + c * vbg_exp μ Y := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * X ω) = ∑ ω, μ ω * (a₀ + c * Y ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [haffine ω])]
    rw [show (∑ ω, μ ω * (a₀ + c * Y ω)) = a₀ * (∑ ω, μ ω) + c * ∑ ω, μ ω * Y ω by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring), hμ]
    ring
  have eEXZ : vbg_exp μ (fun ω => X ω * Z ω) = a₀ * vbg_exp μ Z + c * vbg_exp μ (fun ω => Y ω * Z ω) := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * (X ω * Z ω)) = ∑ ω, μ ω * ((a₀ + c * Y ω) * Z ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [show μ ω * (X ω * Z ω) = (μ ω * X ω) * Z ω by ring, haffine ω]; ring)]
    rw [show (∑ ω, μ ω * ((a₀ + c * Y ω) * Z ω))
        = a₀ * (∑ ω, μ ω * Z ω) + c * ∑ ω, μ ω * (Y ω * Z ω) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring)]
  have eEXY : vbg_exp μ (fun ω => X ω * Y ω) = a₀ * vbg_exp μ Y + c * vbg_exp μ (fun ω => Y ω * Y ω) := by
    unfold vbg_exp
    rw [show (∑ ω, μ ω * (X ω * Y ω)) = ∑ ω, μ ω * ((a₀ + c * Y ω) * Y ω) from Finset.sum_congr rfl
      (fun ω _ => by rw [show μ ω * (X ω * Y ω) = (μ ω * X ω) * Y ω by ring, haffine ω]; ring)]
    rw [show (∑ ω, μ ω * ((a₀ + c * Y ω) * Y ω))
        = a₀ * (∑ ω, μ ω * Y ω) + c * ∑ ω, μ ω * (Y ω * Y ω) by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ω _ => by ring)]
  
  unfold vbg_var vbg_cov
  rw [eEX, eEXZ, eEXY]
  ring

end Degenerate















section Thm1

variable (μ : Ω → ℝ) (X Y Z : Ω → ℝ)











theorem vbg_thm1 (hμ0 : 0 ≤ μ) (hμ : ∑ ω, μ ω = 1) (hY : ∀ ω, Y ω * Y ω = Y ω)
    (hp0 : 0 < vbg_exp μ Y) (hp1 : vbg_exp μ Y < 1)
    (hCovP : 0 ≤ vbg_covPlus μ Y X Z) (hCovM : 0 ≤ vbg_covMinus μ Y X Z)
    (hnondeg : 0 < vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X) :
    vbg_cov μ X Y * vbg_cov μ Y Z ≤ vbg_var μ Y * vbg_cov μ X Z := by
  set p := vbg_exp μ Y with hp
  
  have hid := vbg_prop1 μ X Y Z hY hp0 hp1
  rw [← hp] at hid
  
  have hRHS1 : 0 ≤ p * vbg_covPlus μ Y X Z + (1 - p) * vbg_covMinus μ Y X Z := by
    apply add_nonneg
    · exact mul_nonneg hp0.le hCovP
    · exact mul_nonneg (by linarith) hCovM
  have hRHS2 : 0 ≤ vbg_var μ X * vbg_var μ Y - vbg_cov μ X Y ^ 2 := by
    have hcs := vbg_cauchy_schwarz μ hμ0 hμ X Y
    
    nlinarith [hcs, vbg_var_nonneg μ hμ0 hμ X, vbg_var_nonneg μ hμ0 hμ Y]
  
  have hprodnn : 0 ≤ (vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z)
      * (p * vbg_varPlus μ Y X + (1 - p) * vbg_varMinus μ Y X) := by
    rw [hid]; exact mul_nonneg hRHS1 hRHS2
  have hLHS1 : 0 ≤ vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z :=
    nonneg_of_mul_nonneg_left hprodnn hnondeg
  linarith

end Thm1










section CondFKG

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def vbg_coordUp (j : E) (ω : ConfigSpace E) : ℝ := if ω j then 1 else 0


noncomputable def vbg_coordDown (j : E) (ω : ConfigSpace E) : ℝ := if ω j then 0 else 1


theorem vbg_coordUp_idem (j : E) (ω : ConfigSpace E) :
    vbg_coordUp j ω * vbg_coordUp j ω = vbg_coordUp j ω := by
  unfold vbg_coordUp; by_cases h : ω j <;> simp [h]


theorem vbg_coordDown_idem (j : E) (ω : ConfigSpace E) :
    vbg_coordDown j ω * vbg_coordDown j ω = vbg_coordDown j ω := by
  unfold vbg_coordDown; by_cases h : ω j <;> simp [h]


theorem vbg_sup_apply (ω ω' : ConfigSpace E) (e : E) : (ω ⊔ ω') e = (ω e || ω' e) := rfl

theorem vbg_inf_apply (ω ω' : ConfigSpace E) (e : E) : (ω ⊓ ω') e = (ω e && ω' e) := rfl



theorem vbg_coordUp_logSupermod (j : E) (ω ω' : ConfigSpace E) :
    vbg_coordUp j ω * vbg_coordUp j ω'
      ≤ vbg_coordUp j (ω ⊔ ω') * vbg_coordUp j (ω ⊓ ω') := by
  unfold vbg_coordUp
  rw [vbg_sup_apply, vbg_inf_apply]
  by_cases h : ω j <;> by_cases h' : ω' j <;> simp [h, h']


theorem vbg_coordDown_logSupermod (j : E) (ω ω' : ConfigSpace E) :
    vbg_coordDown j ω * vbg_coordDown j ω'
      ≤ vbg_coordDown j (ω ⊔ ω') * vbg_coordDown j (ω ⊓ ω') := by
  unfold vbg_coordDown
  rw [vbg_sup_apply, vbg_inf_apply]
  by_cases h : ω j <;> by_cases h' : ω' j <;> simp [h, h']



theorem vbg_mul_logSupermod {π Y : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω')) :
    FKGLatticeCondition (fun ω => π ω * Y ω) := by
  intro ω ω'
  have hππ := hπ ω ω'
  have hYY := hY ω ω'
  
  have e1 : π ω * Y ω * (π ω' * Y ω') = (π ω * π ω') * (Y ω * Y ω') := by ring
  have e2 : π (ω ⊔ ω') * Y (ω ⊔ ω') * (π (ω ⊓ ω') * Y (ω ⊓ ω'))
      = (π (ω ⊔ ω') * π (ω ⊓ ω')) * (Y (ω ⊔ ω') * Y (ω ⊓ ω')) := by ring
  rw [e1, e2]
  apply mul_le_mul hππ hYY
  · exact mul_nonneg (hY0 _) (hY0 _)
  · exact mul_nonneg (hπ0 _) (hπ0 _)


theorem vbg_div_const_logSupermod {ρ : ConfigSpace E → ℝ} (c : ℝ) (hc : 0 < c)
    (hρ : FKGLatticeCondition ρ) : FKGLatticeCondition (fun ω => ρ ω / c) := by
  intro ω ω'
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (hρ ω ω') (by positivity)



theorem vbg_condPlus_FKG {π Y : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
    (hp0 : 0 < vbg_exp π Y) : FKGLatticeCondition (vbg_condPlus π Y) := by
  have hmul : FKGLatticeCondition (fun ω => π ω * Y ω) := vbg_mul_logSupermod hπ0 hY0 hπ hY
  have := vbg_div_const_logSupermod (vbg_exp π Y) hp0 hmul
  convert this using 1





theorem vbg_covPlus_nonneg {π Y f g : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hY0 : 0 ≤ Y)
    (hπ : FKGLatticeCondition π)
    (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
    (hp0 : 0 < vbg_exp π Y) (hf : Monotone f) (hg : Monotone g) :
    0 ≤ vbg_covPlus π Y f g := by
  unfold vbg_covPlus vbg_cov
  have hfkg := fkg_inequality (vbg_condPlus_nonneg hπ0 hY0 hp0) (vbg_condPlus_norm hp0)
    (vbg_condPlus_FKG hπ0 hY0 hπ hY hp0) hf hg
  
  have e : vbg_exp (vbg_condPlus π Y) (fun ω => f ω * g ω)
      = ∑ ω, vbg_condPlus π Y ω * (f ω * g ω) := rfl
  have e2 : ∀ h', vbg_exp (vbg_condPlus π Y) h' = ∑ ω, vbg_condPlus π Y ω * h' ω := fun _ => rfl
  rw [e2, e2, e2]
  linarith [hfkg]




theorem vbg_covMinus_nonneg {π Y f g : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hπnorm : ∑ ω, π ω = 1)
    (hYbnd : ∀ ω, Y ω ≤ 1)
    (hπ : FKGLatticeCondition π)
    (hYc : ∀ ω ω', (1 - Y ω) * (1 - Y ω') ≤ (1 - Y (ω ⊔ ω')) * (1 - Y (ω ⊓ ω')))
    (hp1 : vbg_exp π Y < 1) (hf : Monotone f) (hg : Monotone g) :
    0 ≤ vbg_covMinus π Y f g := by
  have hcompl0 : (0 : ConfigSpace E → ℝ) ≤ (fun ω => 1 - Y ω) := by
    intro ω; show (0 : ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]
  have hp0' : 0 < vbg_exp π (fun ω => 1 - Y ω) := by
    rw [vbg_exp_one_sub hπnorm]; linarith
  have h := vbg_covPlus_nonneg (Y := fun ω => 1 - Y ω) (f := f) (g := g)
    hπ0 hcompl0 hπ hYc hp0' hf hg
  unfold vbg_covMinus vbg_covPlus at *
  rw [vbg_condMinus_eq_condPlus hπnorm]
  exact h


















theorem vbg_thm1_configSpace {π : ConfigSpace E → ℝ} (hπ0 : 0 ≤ π) (hπnorm : ∑ ω, π ω = 1)
    (hπ : FKGLatticeCondition π) (j : E) {X Z : ConfigSpace E → ℝ}
    (hX : Monotone X) (hZ : Monotone Z)
    (hp0 : 0 < vbg_exp π (vbg_coordUp j)) (hp1 : vbg_exp π (vbg_coordUp j) < 1) :
    vbg_cov π X (vbg_coordUp j) * vbg_cov π (vbg_coordUp j) Z
      ≤ vbg_var π (vbg_coordUp j) * vbg_cov π X Z := by
  set Y := vbg_coordUp j with hYdef
  have hYidem : ∀ ω, Y ω * Y ω = Y ω := fun ω => vbg_coordUp_idem j ω
  have hY0 : (0 : ConfigSpace E → ℝ) ≤ Y := by
    intro ω; show (0:ℝ) ≤ vbg_coordUp j ω; unfold vbg_coordUp; by_cases h : ω j <;> simp [h]
  have hYbnd : ∀ ω, Y ω ≤ 1 := by
    intro ω; show vbg_coordUp j ω ≤ 1; unfold vbg_coordUp; by_cases h : ω j <;> simp [h]
  have hYls : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω') := vbg_coordUp_logSupermod j
  
  have hcompleq : ∀ ω, 1 - Y ω = vbg_coordDown j ω := by
    intro ω; show 1 - vbg_coordUp j ω = vbg_coordDown j ω
    unfold vbg_coordUp vbg_coordDown; by_cases h : ω j <;> simp [h]
  have hYc : ∀ ω ω', (1 - Y ω) * (1 - Y ω') ≤ (1 - Y (ω ⊔ ω')) * (1 - Y (ω ⊓ ω')) := by
    intro ω ω'; rw [hcompleq, hcompleq, hcompleq, hcompleq]; exact vbg_coordDown_logSupermod j ω ω'
  
  have hCovP : 0 ≤ vbg_covPlus π Y X Z := vbg_covPlus_nonneg hπ0 hY0 hπ hYls hp0 hX hZ
  have hCovM : 0 ≤ vbg_covMinus π Y X Z := vbg_covMinus_nonneg hπ0 hπnorm hYbnd hπ hYc hp1 hX hZ
  
  set LHS2 := vbg_exp π Y * vbg_varPlus π Y X + (1 - vbg_exp π Y) * vbg_varMinus π Y X with hL2
  have hVP0 : 0 ≤ vbg_varPlus π Y X := by
    unfold vbg_varPlus
    exact vbg_var_nonneg _ (vbg_condPlus_nonneg hπ0 hY0 hp0) (vbg_condPlus_norm hp0) X
  have hVM0 : 0 ≤ vbg_varMinus π Y X := by
    unfold vbg_varMinus
    have hq0 : 0 < vbg_exp π (fun ω => 1 - Y ω) := by rw [vbg_exp_one_sub hπnorm]; linarith
    rw [vbg_condMinus_eq_condPlus hπnorm]
    exact vbg_var_nonneg _ (vbg_condPlus_nonneg hπ0 (by intro ω; show (0:ℝ) ≤ 1 - Y ω; linarith [hYbnd ω]) hq0)
      (vbg_condPlus_norm hq0) X
  have hL2nn : 0 ≤ LHS2 := by
    rw [hL2]; exact add_nonneg (mul_nonneg hp0.le hVP0) (mul_nonneg (by linarith) hVM0)
  rcases eq_or_lt_of_le hL2nn with hL2eq | hL2pos
  · 
    have hVPz : vbg_varPlus π Y X = 0 := by
      by_contra hne
      have : 0 < vbg_exp π Y * vbg_varPlus π Y X := mul_pos hp0 (lt_of_le_of_ne hVP0 (Ne.symm hne))
      have := mul_nonneg (show (0:ℝ) ≤ 1 - vbg_exp π Y by linarith) hVM0
      linarith [hL2eq]
    have hVMz : vbg_varMinus π Y X = 0 := by
      by_contra hne
      have h1 : 0 < (1 - vbg_exp π Y) * vbg_varMinus π Y X :=
        mul_pos (by linarith) (lt_of_le_of_ne hVM0 (Ne.symm hne))
      have := mul_nonneg hp0.le hVP0
      linarith [hL2eq]
    have := vbg_thm1_degenerate π X Y Z hπ0 hπnorm hYidem hp0 hp1 hVPz hVMz
    linarith [this]
  · 
    exact vbg_thm1 π X Y Z hπ0 hπnorm hYidem hp0 hp1 hCovP hCovM (by rw [← hL2]; exact hL2pos)

end CondFKG

end Prop1











section Ising

open StatMech.Ising StatMech.ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem vbg_isingExp_eq (β h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G β h f = vbg_exp (isingProb G β h) f := rfl


theorem vbg_cov2_eq (β h : ℝ) (x y : V) :
    cov2 G β h x y = vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s y) := by
  unfold cov2 vbg_cov vbg_exp isingExpectation; rfl


theorem vbg_spin_eq_coordUp (j : V) (s : ConfigSpace V) :
    spin s j = 2 * vbg_coordUp j s - 1 := by
  unfold spin vbg_coordUp
  by_cases h : s j <;> · simp only [h, Bool.false_eq_true, if_true, if_false]; ring


theorem vbg_spin_monotone (j : V) : Monotone (fun s : ConfigSpace V => spin s j) :=
  fun _ _ hab => StatMech.Ising.ifk_spin_mono hab j



theorem vbg_cov_affine_right (μ : ConfigSpace V → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : ConfigSpace V → ℝ)
    (a b : ℝ) : vbg_cov μ f (fun ω => a * g ω + b) = a * vbg_cov μ f g := by
  unfold vbg_cov vbg_exp
  have e1 : (∑ ω, μ ω * (f ω * (a * g ω + b)))
      = a * (∑ ω, μ ω * (f ω * g ω)) + b * ∑ ω, μ ω * f ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * (a * g ω + b)) = a * (∑ ω, μ ω * g ω) + b * ∑ ω, μ ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, hμ]; ring

theorem vbg_cov_affine_left (μ : ConfigSpace V → ℝ) (hμ : ∑ ω, μ ω = 1) (f g : ConfigSpace V → ℝ)
    (a b : ℝ) : vbg_cov μ (fun ω => a * f ω + b) g = a * vbg_cov μ f g := by
  unfold vbg_cov vbg_exp
  have e1 : (∑ ω, μ ω * ((a * f ω + b) * g ω))
      = a * (∑ ω, μ ω * (f ω * g ω)) + b * ∑ ω, μ ω * g ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  have e2 : (∑ ω, μ ω * (a * f ω + b)) = a * (∑ ω, μ ω * f ω) + b * ∑ ω, μ ω := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [e1, e2, hμ]; ring





theorem vbg_cov_spin_coordUp (β h : ℝ) (x j : V) :
    vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s j)
      = 2 * vbg_cov (isingProb G β h) (fun s => spin s x) (vbg_coordUp j) := by
  have hnorm : ∑ ω, isingProb G β h ω = 1 := isingProb_sum_eq_one G β h
  have : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
    funext s; rw [vbg_spin_eq_coordUp]; ring
  rw [this, vbg_cov_affine_right (isingProb G β h) hnorm _ (vbg_coordUp j) 2 (-1)]




theorem vbg_ising_coordUp_pos_lt_one (β h : ℝ) (j : V) :
    0 < vbg_exp (isingProb G β h) (vbg_coordUp j)
      ∧ vbg_exp (isingProb G β h) (vbg_coordUp j) < 1 := by
  
  have hexpand : vbg_exp (isingProb G β h) (vbg_coordUp j)
      = ∑ s, isingProb G β h s * vbg_coordUp j s := rfl
  
  set sT : ConfigSpace V := fun i => if i = j then true else false with hsT
  set sF : ConfigSpace V := fun i => false with hsF
  have hYnn : ∀ s, 0 ≤ isingProb G β h s * vbg_coordUp j s := by
    intro s; apply mul_nonneg (isingProb_nonneg G β h s)
    unfold vbg_coordUp; by_cases hh : s j <;> simp [hh]
  have hYle : ∀ s, isingProb G β h s * vbg_coordUp j s ≤ isingProb G β h s := by
    intro s; unfold vbg_coordUp
    by_cases hh : s j <;> simp [hh, (isingProb_nonneg G β h s)]
  constructor
  · 
    rw [hexpand]
    exact Finset.sum_pos' (fun s _ => hYnn s) ⟨sT, Finset.mem_univ sT, by
      have hpos := isingProb_pos G β h sT
      have : vbg_coordUp j sT = 1 := by unfold vbg_coordUp; rw [hsT]; simp
      rw [this, mul_one]; exact hpos⟩
  · 
    have hsum1 : ∑ s, isingProb G β h s = 1 := isingProb_sum_eq_one G β h
    rw [hexpand]
    have hlt : ∑ s, isingProb G β h s * vbg_coordUp j s < ∑ s, isingProb G β h s := by
      apply Finset.sum_lt_sum (fun s _ => hYle s) ⟨sF, Finset.mem_univ sF, ?_⟩
      have hpos := isingProb_pos G β h sF
      have : vbg_coordUp j sF = 0 := by unfold vbg_coordUp; rw [hsF]; simp
      rw [this, mul_zero]; exact hpos
    rw [hsum1] at hlt; exact hlt










theorem vbg_cor1 (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    cov2 G β h i j * cov2 G β h j k
      ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k := by
  have hπ0 : (0 : ConfigSpace V → ℝ) ≤ isingProb G β h := fun s => isingProb_nonneg G β h s
  have hπnorm : ∑ ω, isingProb G β h ω = 1 := isingProb_sum_eq_one G β h
  have hπfkg : FKGLatticeCondition (fun s => isingProb G β h s) :=
    StatMech.Ising.ifk_isingProb_FKGLatticeCondition G hβ h
  obtain ⟨hp0, hp1⟩ := vbg_ising_coordUp_pos_lt_one G β h j
  
  have hT1 := vbg_thm1_configSpace hπ0 hπnorm hπfkg j
    (X := fun s => spin s i) (Z := fun s => spin s k)
    (vbg_spin_monotone i) (vbg_spin_monotone k) hp0 hp1
  
  
  have hij : cov2 G β h i j = 2 * vbg_cov (isingProb G β h) (fun s => spin s i) (vbg_coordUp j) := by
    rw [vbg_cov2_eq]; exact vbg_cov_spin_coordUp G β h i j
  have hjk : cov2 G β h j k = 2 * vbg_cov (isingProb G β h) (vbg_coordUp j) (fun s => spin s k) := by
    rw [vbg_cov2_eq]
    
    have heq : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
      funext s; rw [vbg_spin_eq_coordUp]; ring
    rw [heq, vbg_cov_affine_left (isingProb G β h) hπnorm (vbg_coordUp j) (fun s => spin s k) 2 (-1)]
  have hik : cov2 G β h i k
      = vbg_cov (isingProb G β h) (fun s => spin s i) (fun s => spin s k) := vbg_cov2_eq G β h i k
  
  have hvarj : vbg_var (isingProb G β h) (fun s => spin s j)
      = 4 * vbg_var (isingProb G β h) (vbg_coordUp j) := by
    unfold vbg_var
    have heq : (fun s => spin s j) = (fun s => 2 * vbg_coordUp j s + (-1)) := by
      funext s; rw [vbg_spin_eq_coordUp]; ring
    rw [heq, vbg_cov_affine_left (isingProb G β h) hπnorm (vbg_coordUp j) _ 2 (-1),
      vbg_cov_affine_right (isingProb G β h) hπnorm _ (vbg_coordUp j) 2 (-1)]
    ring
  rw [hij, hjk, hik, hvarj]
  
  nlinarith [hT1]

end Ising







section MachineCheck


noncomputable def mcMu : Fin 4 → ℝ := ![0.4, 0.1, 0.3, 0.2]


noncomputable def mcX : Fin 4 → ℝ := ![1, 0, 1, 0]


noncomputable def mcY : Fin 4 → ℝ := ![1, 1, 0, 0]


noncomputable def mcZ : Fin 4 → ℝ := ![0, 1, 1, 0]


theorem mc_Y_idem : ∀ ω, mcY ω * mcY ω = mcY ω := by
  intro ω; fin_cases ω <;> simp [mcY]


theorem mc_p_pos : 0 < vbg_exp mcMu mcY := by
  unfold vbg_exp mcMu mcY; simp [Fin.sum_univ_four]; norm_num

theorem mc_p_lt_one : vbg_exp mcMu mcY < 1 := by
  unfold vbg_exp mcMu mcY; simp [Fin.sum_univ_four]; norm_num



theorem mc_prop1 :
    (vbg_var mcMu mcY * vbg_cov mcMu mcX mcZ - vbg_cov mcMu mcX mcY * vbg_cov mcMu mcY mcZ)
        * (vbg_exp mcMu mcY * vbg_varPlus mcMu mcY mcX
            + (1 - vbg_exp mcMu mcY) * vbg_varMinus mcMu mcY mcX)
      = (vbg_exp mcMu mcY * vbg_covPlus mcMu mcY mcX mcZ
            + (1 - vbg_exp mcMu mcY) * vbg_covMinus mcMu mcY mcX mcZ)
        * (vbg_var mcMu mcX * vbg_var mcMu mcY - vbg_cov mcMu mcX mcY ^ 2) :=
  vbg_prop1 mcMu mcX mcY mcZ mc_Y_idem mc_p_pos mc_p_lt_one

end MachineCheck

















































section GHSRelationship

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












theorem vbg_ghs_distinct (β h : ℝ) (v : V) :
    StatMech.Walls.GhcEqGap.eg_ursell3 G β h v v v
      = 2 * (isingExpectation G β h (fun s => spin s v))^3
        - 2 * isingExpectation G β h (fun s => spin s v) := by
  unfold StatMech.Walls.GhcEqGap.eg_ursell3
  have e_sss : (fun s : ConfigSpace V => spin s v * (spin s v * spin s v))
      = (fun s => spin s v) := by funext s; rw [spin_sq s v, mul_one]
  have e_ss : (fun s : ConfigSpace V => spin s v * spin s v) = (fun _ => (1:ℝ)) := by
    funext s; exact spin_sq s v
  rw [e_sss, e_ss]
  have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1:ℝ)) = 1 := by
    unfold isingExpectation; simp only [mul_one]; exact isingProb_sum_eq_one G β h
  rw [hone]; ring





theorem vbg_cor1_arbitrary_field (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    cov2 G β h i j * cov2 G β h j k
      ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k :=
  vbg_cor1 G β h hβ i j k



























theorem vbg_ghs_relationship_notes : True := trivial

end GHSRelationship

end VBG

end Walls

end StatMech
