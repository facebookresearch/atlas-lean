/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Code.Probability.RhoOptimiseClose2
import Code.Probability.ConvexGapHC
import Code.Probability.DegreeTruncation
import Code.Probability.KKLpBiased

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]












theorem fsr_ptn_psi_half (b : Bool) :
    ptn_psi (1 / 2 : ℝ) b = - khc_sign b := by
  unfold ptn_psi khc_sign
  rw [show ptn_sigma (1 / 2 : ℝ) = 1 / 2 from by
    unfold ptn_sigma; rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 from by ring,
      Real.sqrt_sq (by norm_num)]]
  cases b <;> norm_num [ptn_val]

omit [Fintype ι] [DecidableEq ι] in


theorem fsr_ptn_pchar_half (S : Finset ι) (ω : ConfigSpace ι) :
    ptn_pchar (1 / 2 : ℝ) S ω = (-1) ^ S.card * khc_walshChar S ω := by
  unfold ptn_pchar khc_walshChar
  rw [show (fun i => ptn_psi (1 / 2 : ℝ) (ω i)) = (fun i => - khc_sign (ω i)) from by
    funext i; exact fsr_ptn_psi_half (ω i)]
  rw [Finset.prod_neg]





theorem fsr_ptn_coeff_half_sq (f : ConfigSpace ι → ℝ) (S : Finset ι) :
    (ptn_coeff (1 / 2 : ℝ) f S) ^ 2 = (khc_fourierCoeff f S) ^ 2 := by
  have heq : ptn_coeff (1 / 2 : ℝ) f S = (-1) ^ S.card * khc_fourierCoeff f S := by
    unfold ptn_coeff khc_fourierCoeff
    rw [khc_expect_half]
    rw [show (fun ω => f ω * ptn_pchar (1 / 2 : ℝ) S ω)
        = (fun ω => (-1) ^ S.card * (f ω * khc_walshChar S ω)) from by
      funext ω; rw [fsr_ptn_pchar_half]; ring]
    rw [vtp_uexp_smul]
  rw [heq, mul_pow]
  rcases Nat.even_or_odd S.card with he | ho
  · rw [he.neg_one_pow]; ring
  · rw [ho.neg_one_pow]; ring




theorem fsr_totalInfl_half_eq (φ : ConfigSpace ι → Bool) :
    totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      = ∑ S : Finset ι, 4 * (S.card : ℝ)
          * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
  rw [khc_totalInfl_eq_fourierWeight φ]
  apply Finset.sum_congr rfl
  intro S _
  rw [fsr_ptn_coeff_half_sq]

























theorem fsr_smallDeltaBound_at_half {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  
  have Hcap : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
            ^ (2 / (1 + ρ ^ 2) - 1)
          * (∑ S : Finset E, 4 * (S.card : ℝ)
              * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
    fun ρ h0 h1 => bph_capped_hc h0 h1 φ
  
  have hms := cro2_master_sub φ Hcap u hu0.le hu1.le
  
  rw [khc_totalInfl_eq_fourierWeight φ]
  calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
        apply Finset.sum_congr rfl
        intro S _; rw [fsr_ptn_coeff_half_sq]
    _ ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * (∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := hms















theorem fsr_pbiased_endpoint_proved :
    KKLHypercontractive (1 / 2 : ℝ) 2 :=
  kpb_PBiasedHC_half_holds












theorem fsr_pbiased_engine_is_damped [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ)
        * ((4 * p * (1 - p)) ^ (S.card - 1) / (4 * p * (1 - p)))
        * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  fpe_master_sub hp0 hp1 φ u hu0 hu1







theorem fsr_smallDelta_of_pbiased {q : ℝ}
    (H : dtr_lowDegreeResidue q) : cvg_smallDeltaResidue q :=
  dtr_smallDelta_of_residue H

end StatMech.Probability
