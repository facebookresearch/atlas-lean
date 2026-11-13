/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.CorrelationLength










namespace StatMech
namespace Exact3D




theorem finiteDistanceDecayRate_eq_of_abs_eq_exp
    (G : ℕ → ℝ) {A m : ℝ} (hA : 0 < A) {n : ℕ} (hn : n ≠ 0)
    (hG : |G n| = A * Real.exp (-(m * (n : ℝ)))) :
    finiteDistanceDecayRate G n =
      m - Real.log A / (n : ℝ) := by
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hA_ne : A ≠ 0 := hA.ne'
  have hexp_ne : Real.exp (-(m * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
  simp [finiteDistanceDecayRate, hn, hG, Real.log_mul hA_ne hexp_ne,
    Real.log_exp]
  field_simp [hnℝ]
  ring




theorem finiteDistanceDecayRate_eq_of_abs_eq_prefactor_exp
    (G : ℕ → ℝ) {A : ℕ → ℝ} {m : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hA : 0 < A n)
    (hG : |G n| = A n * Real.exp (-(m * (n : ℝ)))) :
    finiteDistanceDecayRate G n =
      m - Real.log (A n) / (n : ℝ) := by
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hA_ne : A n ≠ 0 := hA.ne'
  have hexp_ne : Real.exp (-(m * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
  simp [finiteDistanceDecayRate, hn, hG, Real.log_mul hA_ne hexp_ne,
    Real.log_exp]
  field_simp [hnℝ]
  ring


theorem tendsto_log_prefactor_div_nat_atTop (A : ℝ) :
    Filter.Tendsto (fun n : ℕ => Real.log A / (n : ℝ)) Filter.atTop (nhds 0) := by
  simpa using
    (tendsto_const_nhds (x := Real.log A)).div_atTop tendsto_natCast_atTop_atTop



theorem finiteDistanceDecayRate_bounds_of_abs_between_exp
    (G : ℕ → ℝ) {Alo Ahi m : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hlo_pos : 0 < Alo) (hhi_pos : 0 < Ahi)
    (hlo : Alo * Real.exp (-(m * (n : ℝ))) ≤ |G n|)
    (hhi : |G n| ≤ Ahi * Real.exp (-(m * (n : ℝ)))) :
    m - Real.log Ahi / (n : ℝ) ≤ finiteDistanceDecayRate G n ∧
      finiteDistanceDecayRate G n ≤ m - Real.log Alo / (n : ℝ) := by
  have hnℝ_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnℝ_pos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hexp_pos : 0 < Real.exp (-(m * (n : ℝ))) := Real.exp_pos _
  have hlo_prod_pos : 0 < Alo * Real.exp (-(m * (n : ℝ))) :=
    mul_pos hlo_pos hexp_pos
  have hG_pos : 0 < |G n| := lt_of_lt_of_le hlo_prod_pos hlo
  have hhi_prod_pos : 0 < Ahi * Real.exp (-(m * (n : ℝ))) :=
    mul_pos hhi_pos hexp_pos
  have hlo_log :
      Real.log Alo - m * (n : ℝ) ≤ Real.log |G n| := by
    have hlog := Real.log_le_log hlo_prod_pos hlo
    have hprod_ne : Alo * Real.exp (-(m * (n : ℝ))) ≠ 0 :=
      hlo_prod_pos.ne'
    have hA_ne : Alo ≠ 0 := hlo_pos.ne'
    have hexp_ne : Real.exp (-(m * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
    rw [Real.log_mul hA_ne hexp_ne, Real.log_exp] at hlog
    linarith
  have hhi_log :
      Real.log |G n| ≤ Real.log Ahi - m * (n : ℝ) := by
    have hlog := Real.log_le_log hG_pos hhi
    have hA_ne : Ahi ≠ 0 := hhi_pos.ne'
    have hexp_ne : Real.exp (-(m * (n : ℝ))) ≠ 0 := Real.exp_ne_zero _
    rw [Real.log_mul hA_ne hexp_ne, Real.log_exp] at hlog
    linarith
  have hlower_raw :
      m * (n : ℝ) - Real.log Ahi ≤ -Real.log |G n| := by
    linarith
  have hupper_raw :
      -Real.log |G n| ≤ m * (n : ℝ) - Real.log Alo := by
    linarith
  constructor
  · have hleft_eq :
        m - Real.log Ahi / (n : ℝ) =
          (m * (n : ℝ) - Real.log Ahi) / (n : ℝ) := by
      field_simp [hnℝ_ne]
    have hdiv :=
      div_le_div_of_nonneg_right hlower_raw hnℝ_pos.le
    rw [hleft_eq, finiteDistanceDecayRate, if_neg hn]
    exact hdiv
  · have hright_eq :
        m - Real.log Alo / (n : ℝ) =
          (m * (n : ℝ) - Real.log Alo) / (n : ℝ) := by
      field_simp [hnℝ_ne]
    have hdiv :=
      div_le_div_of_nonneg_right hupper_raw hnℝ_pos.le
    rw [finiteDistanceDecayRate, if_neg hn, hright_eq]
    exact hdiv



theorem tendsto_finiteDistanceDecayRate_of_eventually_abs_between_prefactor_exp
    (G : ℕ → ℝ) {Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
    (hlog_lo :
      Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlog_hi :
      Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlo :
      ∀ᶠ n in Filter.atTop,
        Alo n * Real.exp (-(m * (n : ℝ))) ≤ |G n|)
    (hhi :
      ∀ᶠ n in Filter.atTop,
        |G n| ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
    Filter.Tendsto (fun n : ℕ => finiteDistanceDecayRate G n)
      Filter.atTop (nhds m) := by
  have hlow_tendsto :
      Filter.Tendsto (fun n : ℕ => m - Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using (tendsto_const_nhds.sub hlog_hi)
  have hup_tendsto :
      Filter.Tendsto (fun n : ℕ => m - Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using (tendsto_const_nhds.sub hlog_lo)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tendsto
    hup_tendsto ?_ ?_
  · filter_upwards [hlo_pos, hhi_pos, hlo, hhi, Filter.eventually_ne_atTop 0]
      with n hlo_n hhi_n hlo_bound hhi_bound hn
    exact (finiteDistanceDecayRate_bounds_of_abs_between_exp
      G hn hlo_n hhi_n hlo_bound hhi_bound).1
  · filter_upwards [hlo_pos, hhi_pos, hlo, hhi, Filter.eventually_ne_atTop 0]
      with n hlo_n hhi_n hlo_bound hhi_bound hn
    exact (finiteDistanceDecayRate_bounds_of_abs_between_exp
      G hn hlo_n hhi_n hlo_bound hhi_bound).2




theorem tendsto_neg_log_div_of_eventually_between_prefactor_exp
    (G : ℕ → ℝ) {Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
    (hlog_lo :
      Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlog_hi :
      Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlo :
      ∀ᶠ n in Filter.atTop,
        Alo n * Real.exp (-(m * (n : ℝ))) ≤ G n)
    (hhi :
      ∀ᶠ n in Filter.atTop,
        G n ≤ Ahi n * Real.exp (-(m * (n : ℝ)))) :
    Filter.Tendsto (fun n : ℕ => -Real.log (G n) / (n : ℝ))
      Filter.atTop (nhds m) := by
  have hG_pos : ∀ᶠ n in Filter.atTop, 0 < G n := by
    filter_upwards [hlo_pos, hlo] with n hlo_n hlo_bound
    exact lt_of_lt_of_le
      (mul_pos hlo_n (Real.exp_pos (-(m * (n : ℝ))))) hlo_bound
  have hlo_abs :
      ∀ᶠ n in Filter.atTop,
        Alo n * Real.exp (-(m * (n : ℝ))) ≤ |G n| := by
    filter_upwards [hlo] with n hlo_bound
    exact le_trans hlo_bound (le_abs_self (G n))
  have hhi_abs :
      ∀ᶠ n in Filter.atTop,
        |G n| ≤ Ahi n * Real.exp (-(m * (n : ℝ))) := by
    filter_upwards [hG_pos, hhi] with n hGn hhi_bound
    simpa [abs_of_pos hGn] using hhi_bound
  have hrate :
      Filter.Tendsto (fun n : ℕ => finiteDistanceDecayRate G n)
        Filter.atTop (nhds m) :=
    tendsto_finiteDistanceDecayRate_of_eventually_abs_between_prefactor_exp
      G hlo_pos hhi_pos hlog_lo hlog_hi hlo_abs hhi_abs
  refine Filter.Tendsto.congr' ?_ hrate
  filter_upwards [hG_pos, Filter.eventually_ne_atTop 0] with n hGn hn
  simp [finiteDistanceDecayRate, hn, abs_of_pos hGn]




theorem hasInverseCorrelationLength_of_eventually_abs_eq_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {A m : ℝ} (hA : 0 < A)
    (hG :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| =
          A * Real.exp (-(m * (n : ℝ)))) :
    HasInverseCorrelationLength M β origin ray m := by
  unfold HasInverseCorrelationLength inverseDecayRate
  have hformula :
      ∀ᶠ n in Filter.atTop,
        finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) n =
          m - Real.log A / (n : ℝ) := by
    filter_upwards [hG, Filter.eventually_ne_atTop 0] with n hGn hn
    exact finiteDistanceDecayRate_eq_of_abs_eq_exp
      (TwoPointAlongRay M β origin ray) hA hn hGn
  have hlimit :
      Filter.Tendsto (fun n : ℕ => m - Real.log A / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using
      (tendsto_const_nhds.sub (tendsto_log_prefactor_div_nat_atTop A))
  exact Filter.Tendsto.congr' (hformula.mono fun _ h => h.symm) hlimit




theorem hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {A : ℕ → ℝ} {m : ℝ}
    (hA : ∀ᶠ n in Filter.atTop, 0 < A n)
    (hlogA :
      Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hG :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| =
          A n * Real.exp (-(m * (n : ℝ)))) :
    HasInverseCorrelationLength M β origin ray m := by
  unfold HasInverseCorrelationLength inverseDecayRate
  have hformula :
      ∀ᶠ n in Filter.atTop,
        finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) n =
          m - Real.log (A n) / (n : ℝ) := by
    filter_upwards [hG, hA, Filter.eventually_ne_atTop 0] with n hGn hAn hn
    exact finiteDistanceDecayRate_eq_of_abs_eq_prefactor_exp
      (TwoPointAlongRay M β origin ray) hn hAn hGn
  have hlimit :
      Filter.Tendsto (fun n : ℕ => m - Real.log (A n) / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using (tendsto_const_nhds.sub hlogA)
  exact Filter.Tendsto.congr' (hformula.mono fun _ h => h.symm) hlimit




theorem hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
    (hlog_lo :
      Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlog_hi :
      Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlo :
      ∀ᶠ n in Filter.atTop,
        Alo n * Real.exp (-(m * (n : ℝ))) ≤
          |TwoPointAlongRay M β origin ray n|)
    (hhi :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| ≤
          Ahi n * Real.exp (-(m * (n : ℝ)))) :
    HasInverseCorrelationLength M β origin ray m := by
  unfold HasInverseCorrelationLength inverseDecayRate
  have hlow_tendsto :
      Filter.Tendsto (fun n : ℕ => m - Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using (tendsto_const_nhds.sub hlog_hi)
  have hup_tendsto :
      Filter.Tendsto (fun n : ℕ => m - Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds m) := by
    simpa using (tendsto_const_nhds.sub hlog_lo)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tendsto hup_tendsto ?_ ?_
  · filter_upwards [hlo_pos, hhi_pos, hlo, hhi, Filter.eventually_ne_atTop 0]
      with n hlo_n hhi_n hlo_bound hhi_bound hn
    exact (finiteDistanceDecayRate_bounds_of_abs_between_exp
      (TwoPointAlongRay M β origin ray) hn hlo_n hhi_n hlo_bound hhi_bound).1
  · filter_upwards [hlo_pos, hhi_pos, hlo, hhi, Filter.eventually_ne_atTop 0]
      with n hlo_n hhi_n hlo_bound hhi_bound hn
    exact (finiteDistanceDecayRate_bounds_of_abs_between_exp
      (TwoPointAlongRay M β origin ray) hn hlo_n hhi_n hlo_bound hhi_bound).2



theorem hasCorrelationLength_of_eventually_abs_eq_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {A m : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hG :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| =
          A * Real.exp (-(m * (n : ℝ)))) :
    HasCorrelationLength M β origin ray m⁻¹ where
  xi_pos := inv_pos.mpr hm
  tendsto_inverse := by
    simpa [inv_inv] using
      hasInverseCorrelationLength_of_eventually_abs_eq_exp
        M β origin ray hA hG



theorem hasCorrelationLength_of_eventually_abs_eq_prefactor_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {A : ℕ → ℝ} {m : ℝ}
    (hA : ∀ᶠ n in Filter.atTop, 0 < A n)
    (hlogA :
      Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hm : 0 < m)
    (hG :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| =
          A n * Real.exp (-(m * (n : ℝ)))) :
    HasCorrelationLength M β origin ray m⁻¹ where
  xi_pos := inv_pos.mpr hm
  tendsto_inverse := by
    simpa [inv_inv] using
      hasInverseCorrelationLength_of_eventually_abs_eq_prefactor_exp
        M β origin ray hA hlogA hG



theorem hasCorrelationLength_of_eventually_abs_between_prefactor_exp {ι : Type*}
    (M : CriticalModel ι) (β : ℝ) (origin : ι) (ray : ℕ → ι)
    {Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hlo_pos : ∀ᶠ n in Filter.atTop, 0 < Alo n)
    (hhi_pos : ∀ᶠ n in Filter.atTop, 0 < Ahi n)
    (hlog_lo :
      Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hlog_hi :
      Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
        Filter.atTop (nhds 0))
    (hm : 0 < m)
    (hlo :
      ∀ᶠ n in Filter.atTop,
        Alo n * Real.exp (-(m * (n : ℝ))) ≤
          |TwoPointAlongRay M β origin ray n|)
    (hhi :
      ∀ᶠ n in Filter.atTop,
        |TwoPointAlongRay M β origin ray n| ≤
          Ahi n * Real.exp (-(m * (n : ℝ)))) :
    HasCorrelationLength M β origin ray m⁻¹ where
  xi_pos := inv_pos.mpr hm
  tendsto_inverse := by
    simpa [inv_inv] using
      hasInverseCorrelationLength_of_eventually_abs_between_prefactor_exp
        M β origin ray hlo_pos hhi_pos hlog_lo hlog_hi hlo hhi

end Exact3D
end StatMech
