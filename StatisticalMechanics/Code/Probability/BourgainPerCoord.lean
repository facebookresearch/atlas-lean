/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.Probability.KKLLogOptimisation

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





noncomputable def bph_deriv (f : ConfigSpace ι → ℝ) (e : ι) : ConfigSpace ι → ℝ :=
  fun ω => f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)










theorem bph_noiseOp_sum_walsh (ρ : ℝ) (s : Finset (Finset ι)) (a : Finset ι → ℝ)
    (T : Finset ι → Finset ι) :
    bnt_noiseOp ρ (fun x => ∑ S ∈ s, a S * khc_walshChar (T S) x)
      = fun x => ∑ S ∈ s, (a S * ρ ^ (T S).card) * khc_walshChar (T S) x := by
  rw [khc_noiseOp_finset_sum]
  funext x
  apply Finset.sum_congr rfl
  intro S _
  rw [khc_noiseOp_const_mul ρ (a S) (khc_walshChar (T S))]
  show a S * bnt_noiseOp ρ (khc_walshChar (T S)) x = _
  rw [khc_noiseOp_walshChar_apply]
  ring



theorem bph_noiseOp_l2sq_relabel (ρ : ℝ) (s : Finset (Finset ι)) (a : Finset ι → ℝ)
    (T : Finset ι → Finset ι) (hTinj : Set.InjOn T s) :
    bnt_uexp (fun x => (bnt_noiseOp ρ (fun x => ∑ S ∈ s, a S * khc_walshChar (T S) x) x) ^ 2)
      = ∑ S ∈ s, (ρ ^ (T S).card) ^ 2 * (a S) ^ 2 := by
  rw [bph_noiseOp_sum_walsh, khc_uexp_sum_walsh_sq s (fun S => a S * ρ ^ (T S).card) T hTinj]
  apply Finset.sum_congr rfl
  intro S _; ring





theorem bph_noiseOp_deriv_l2sq (ρ : ℝ) (f : ConfigSpace ι → ℝ) (e : ι) :
    bnt_uexp (fun x => (bnt_noiseOp ρ (bph_deriv f e) x) ^ 2)
      = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * (4 * (khc_fourierCoeff f S) ^ 2) := by
  have heq : bph_deriv f e
      = fun x => ∑ S ∈ univ.filter (fun S => e ∈ S),
          ((-2 : ℝ) * khc_fourierCoeff f S) * khc_walshChar (S.erase e) x := by
    funext ω; exact khc_deriv_fourier f e ω
  rw [heq, bph_noiseOp_l2sq_relabel ρ _ (fun S => (-2 : ℝ) * khc_fourierCoeff f S)
      (fun S => S.erase e) (khc_erase_injOn e)]
  apply Finset.sum_congr rfl
  intro S _; ring






omit [Fintype ι] in

theorem bph_abs_deriv_rpow {q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool)
    (e : ι) (ω : ConfigSpace ι) :
    |bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω| ^ q
      = (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω) ^ 2 := by
  unfold bph_deriv
  simp only
  by_cases hO : φ (StatMech.setOpen e ω) <;> by_cases hC : φ (StatMech.setClosed e ω) <;>
    simp [hO, hC, Real.one_rpow, Real.zero_rpow (ne_of_gt hq)]




theorem bph_uexp_deriv_sq (φ : ConfigSpace ι → Bool) (e : ι) :
    bnt_uexp (fun ω => (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω) ^ 2)
      = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  unfold OSSS.infl bph_deriv
  rw [khc_expect_half]
  congr 1
  funext ω
  exact (khc_abs_diff_indicator φ e ω).symm




theorem bph_qnormPow_deriv {q : ℝ} (hq : 0 < q) (φ : ConfigSpace ι → Bool) (e : ι) :
    bnt_qnormPow q (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)
      = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  unfold bnt_qnormPow
  rw [show (fun ω => |bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω| ^ q)
      = (fun ω => (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e ω) ^ 2)
    from by funext ω; exact bph_abs_deriv_rpow hq φ e ω]
  exact bph_uexp_deriv_sq φ e




theorem bph_qnorm_deriv_sq {ρ : ℝ} (φ : ConfigSpace ι → Bool) (e : ι) :
    (bnt_qnorm (1 + ρ ^ 2) (bph_deriv (fun ω => if φ ω then (1 : ℝ) else 0) e)) ^ 2
      = (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
  have hq : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
  unfold bnt_qnorm
  rw [bph_qnormPow_deriv hq φ e]
  set Ie := OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e
    with hIe
  have hIenn : 0 ≤ Ie := by
    rw [hIe]
    exact kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) _ e
  rw [← Real.rpow_natCast (Ie ^ (1 / (1 + ρ ^ 2))) 2, ← Real.rpow_mul hIenn]
  congr 1
  push_cast
  field_simp



















theorem bph_perCoord_hc {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2
          * (4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2))
      ≤ (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  have hhc : bnt_qnorm 2 (bnt_noiseOp ρ (bph_deriv f e)) ≤ bnt_qnorm (1 + ρ ^ 2) (bph_deriv f e) :=
    khc_hypercontractivity_general h0 h1 (bph_deriv f e)
  have hlhs : 0 ≤ bnt_qnorm 2 (bnt_noiseOp ρ (bph_deriv f e)) := bnt_qnorm_nonneg 2 _
  have hrhs : 0 ≤ bnt_qnorm (1 + ρ ^ 2) (bph_deriv f e) := bnt_qnorm_nonneg _ _
  have hsq : (bnt_qnorm 2 (bnt_noiseOp ρ (bph_deriv f e))) ^ 2
      ≤ (bnt_qnorm (1 + ρ ^ 2) (bph_deriv f e)) ^ 2 := by nlinarith [hhc, hlhs, hrhs]
  rw [vtp_qnorm2_sq, vtp_qnormPow2_eq_uexp_sq, bph_noiseOp_deriv_l2sq,
      bph_qnorm_deriv_sq φ e] at hsq
  exact hsq













theorem bph_summed_hc {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2
        * (4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)))
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) := by
  set c := fun S : Finset ι => (4 * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
    with hc
  have hsum : (∑ e : ι, ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * c S)
      ≤ ∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)) :=
    Finset.sum_le_sum (fun e _ => bph_perCoord_hc h0 h1 φ e)
  refine le_trans ?_ hsum
  have hlhs : (∑ e : ι, ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * c S)
      = ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * c S) := by
    have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * c S)
        = ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
            (ρ ^ (S.card - 1)) ^ 2 * c S := by
      intro e
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.card_erase_of_mem (by simpa using hS)]
    simp_rw [hinner]
    have hsf : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.card - 1)) ^ 2 * c S)
        = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * c S else 0) := by
      intro e; rw [Finset.sum_filter]
    simp_rw [hsf]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hlhs]







omit [Fintype ι] [DecidableEq ι] in


theorem bph_cap_term (x δ θ : ℝ) (hx : 0 ≤ x) (hcap : x ≤ δ) (hθ : 1 ≤ θ) :
    x ^ θ ≤ δ ^ (θ - 1) * x := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith), mul_zero]
  · have h1 : x ^ θ = x ^ (θ - 1) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hpos]; ring_nf
    rw [h1, Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hcap (by linarith)) hx







theorem bph_cap_sum [Nonempty ι] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (φ : ConfigSpace ι → Bool) :
    (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ))
        (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / (1 + ρ ^ 2)))
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (2 / (1 + ρ ^ 2) - 1)
        * (∑ S : Finset ι, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f with hδ
  set θ := 2 / (1 + ρ ^ 2) with hθdef
  have hθ1 : 1 ≤ θ := by
    rw [hθdef, le_div_iff₀ (by positivity)]; nlinarith [h1, h0]
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := ι) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hterm : ∀ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e) ^ θ
      ≤ δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e) :=
    fun e => bph_cap_term _ _ _ (kkl_infl_nonneg hprob f e) (kkl_infl_le_maxInfl _ f e) hθ1
  calc (∑ e : ι, (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e) ^ θ)
      ≤ ∑ e : ι, δ ^ (θ - 1) * (OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e) :=
        Finset.sum_le_sum (fun e _ => hterm e)
    _ = δ ^ (θ - 1) * (∑ e : ι, OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e) := by
        rw [Finset.mul_sum]
    _ = δ ^ (θ - 1) * (∑ S : Finset ι, 4 * (S.card : ℝ) * (khc_fourierCoeff f S) ^ 2) := by
        rw [show (∑ e : ι, OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f e)
            = totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f from rfl,
            khc_totalInfl_eq_fourierWeight φ]
















theorem bph_capped_hc [Nonempty ι] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
        * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (2 / (1 + ρ ^ 2) - 1)
        * (∑ S : Finset ι, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  refine le_trans ?_ (le_trans (bph_summed_hc h0 h1 φ) (bph_cap_sum h0 h1 φ))
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro S _; ring


































def bph_RhoOptimise (c : ℝ) : Prop :=
  ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool),
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        (∑ S : Finset E, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (2 / (1 + ρ ^ 2) - 1)
            * (∑ S : Finset E, 4 * (S.card : ℝ)
                * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)) →
      c * (∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2







theorem bph_rhoOptimise_hyp_holds [Nonempty ι] (φ : ConfigSpace ι → Bool) :
    ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (∑ S : Finset ι, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
            ^ (2 / (1 + ρ ^ 2) - 1)
          * (∑ S : Finset ι, 4 * (S.card : ℝ)
              * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
  fun _ρ h0 h1 => bph_capped_hc h0 h1 φ




theorem bph_rhoOptimise_zero : bph_RhoOptimise 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  exact kls_W_nonneg φ










theorem bph_logOptimisation_of_rho {c : ℝ} (H : bph_RhoOptimise c) :
    kls_LogOptimisation c := by
  intro E _ _ _ φ _hfluct
  exact H φ (fun ρ h0 h1 => bph_capped_hc h0 h1 φ)
















theorem bph_KKL {c : ℝ} (H : bph_RhoOptimise c) :
    KKLHypercontractive (1 / 2 : ℝ) c :=
  kls_logSobolevStep (bph_logOptimisation_of_rho H)





























end StatMech.Probability
