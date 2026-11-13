/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum











namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_mvMonomialValue
    {E : Type*} (weight : E → ℂ) (m : E →₀ ℕ) : ℂ :=
  m.prod fun edge n ↦ weight edge ^ n

theorem ons_mvMonomialValue_add
    {E : Type*} [DecidableEq E] (weight : E → ℂ)
    (m n : E →₀ ℕ) :
    ons_mvMonomialValue weight (m + n) =
      ons_mvMonomialValue weight m * ons_mvMonomialValue weight n := by
  unfold ons_mvMonomialValue
  apply Finsupp.prod_add_index
  · intro edge hedge
    simp
  · intro edge hedge a b
    rw [pow_add]

theorem ons_mvSeriesEval_eq
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) :
    ons_mvSeriesEval series weight =
      ∑' m : E →₀ ℕ,
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m := by
  rfl

def ons_MvSeriesEvalSummable
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) : Prop :=
  Summable fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖

theorem ons_MvSeriesEvalSummable.mul
    {E : Type*} [DecidableEq E]
    {f g : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight)
    (hg : ons_MvSeriesEvalSummable g weight) :
    ons_MvSeriesEvalSummable (f * g) weight := by
  let F := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m f * ons_mvMonomialValue weight m‖
  let G := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m g * ons_mvMonomialValue weight m‖
  have hF : Summable F := hf
  have hG : Summable G := hg
  have hFnorm : Summable fun m ↦ ‖F m‖ := by
    simpa [F, Real.norm_eq_abs, abs_of_nonneg] using hF
  have hGnorm : Summable fun m ↦ ‖G m‖ := by
    simpa [G, Real.norm_eq_abs, abs_of_nonneg] using hG
  have hprod : Summable fun p : (E →₀ ℕ) × (E →₀ ℕ) ↦
      F p.1 * G p.2 :=
    summable_mul_of_summable_norm hFnorm hGnorm
  have hmajor : Summable fun m : E →₀ ℕ ↦
      ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  apply Summable.of_nonneg_of_le
    (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) hmajor
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  calc
    ‖∑ p ∈ Finset.antidiagonal m,
        (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
          ons_mvMonomialValue weight m‖ ≤
        ∑ p ∈ Finset.antidiagonal m,
          ‖(MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
            ons_mvMonomialValue weight m‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hadd : p.1 + p.2 = m :=
        Finset.mem_antidiagonal.mp hp
      rw [← hadd, ons_mvMonomialValue_add]
      simp only [F, G, norm_mul]
      ring

theorem ons_mvSeriesEval_mul
    {E : Type*} [DecidableEq E]
    {f g : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight)
    (hg : ons_MvSeriesEvalSummable g weight) :
    ons_mvSeriesEval (f * g) weight =
      ons_mvSeriesEval f weight * ons_mvSeriesEval g weight := by
  let F := fun m : E →₀ ℕ ↦
    MvPowerSeries.coeff m f * ons_mvMonomialValue weight m
  let G := fun m : E →₀ ℕ ↦
    MvPowerSeries.coeff m g * ons_mvMonomialValue weight m
  have hF : Summable F := Summable.of_norm hf
  have hG : Summable G := Summable.of_norm hg
  have hFnorm : Summable fun m ↦ ‖F m‖ := hf
  have hGnorm : Summable fun m ↦ ‖G m‖ := hg
  have hprod : Summable fun p : (E →₀ ℕ) × (E →₀ ℕ) ↦
      F p.1 * G p.2 :=
    summable_mul_of_summable_norm hFnorm hGnorm
  rw [ons_mvSeriesEval_eq, ons_mvSeriesEval_eq, ons_mvSeriesEval_eq,
    hF.tsum_mul_tsum_eq_tsum_sum_antidiagonal hG hprod]
  apply tsum_congr
  intro m
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hadd : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rw [← hadd, ons_mvMonomialValue_add]
  simp only [F, G]
  ring

noncomputable def ons_mvSeriesEvalNorm
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) : ℝ :=
  ∑' m : E →₀ ℕ,
    ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖

theorem ons_mvSeriesEvalNorm_mul_le
    {E : Type*} [DecidableEq E]
    {f g : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight)
    (hg : ons_MvSeriesEvalSummable g weight) :
    ons_mvSeriesEvalNorm (f * g) weight ≤
      ons_mvSeriesEvalNorm f weight * ons_mvSeriesEvalNorm g weight := by
  let F := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m f * ons_mvMonomialValue weight m‖
  let G := fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m g * ons_mvMonomialValue weight m‖
  have hF : Summable F := hf
  have hG : Summable G := hg
  have hFnorm : Summable fun m ↦ ‖F m‖ := by
    simpa [F, Real.norm_eq_abs, abs_of_nonneg] using hF
  have hGnorm : Summable fun m ↦ ‖G m‖ := by
    simpa [G, Real.norm_eq_abs, abs_of_nonneg] using hG
  have hprod : Summable fun p : (E →₀ ℕ) × (E →₀ ℕ) ↦
      F p.1 * G p.2 :=
    summable_mul_of_summable_norm hFnorm hGnorm
  have hmajor : Summable fun m : E →₀ ℕ ↦
      ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  have hmul := hf.mul hg
  unfold ons_mvSeriesEvalNorm
  calc
    (∑' m : E →₀ ℕ,
        ‖MvPowerSeries.coeff m (f * g) *
          ons_mvMonomialValue weight m‖) ≤
        ∑' m : E →₀ ℕ,
          ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 := by
      apply Summable.tsum_le_tsum _ hmul hmajor
      intro m
      rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
      calc
        ‖∑ p ∈ Finset.antidiagonal m,
            (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
              ons_mvMonomialValue weight m‖ ≤
            ∑ p ∈ Finset.antidiagonal m,
              ‖(MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) *
                ons_mvMonomialValue weight m‖ :=
          norm_sum_le _ _
        _ = ∑ p ∈ Finset.antidiagonal m, F p.1 * G p.2 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hadd : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
          rw [← hadd, ons_mvMonomialValue_add]
          simp only [F, G, norm_mul]
          ring
    _ = (∑' m, F m) * ∑' m, G m :=
      (hF.tsum_mul_tsum_eq_tsum_sum_antidiagonal hG hprod).symm

theorem ons_MvSeriesEvalSummable.one
    {E : Type*} [DecidableEq E] (weight : E → ℂ) :
    ons_MvSeriesEvalSummable (1 : MvPowerSeries E ℂ) weight := by
  apply summable_of_ne_finset_zero (s := {0})
  intro m hm
  simp only [Finset.mem_singleton] at hm
  rw [MvPowerSeries.coeff_one]
  simp [hm]

@[simp] theorem ons_mvSeriesEval_one
    {E : Type*} [DecidableEq E] (weight : E → ℂ) :
    ons_mvSeriesEval (1 : MvPowerSeries E ℂ) weight = 1 := by
  simpa using ons_mvSeriesEval_coe (1 : MvPolynomial E ℂ) weight

@[simp] theorem ons_mvSeriesEvalNorm_one
    {E : Type*} [DecidableEq E] (weight : E → ℂ) :
    ons_mvSeriesEvalNorm (1 : MvPowerSeries E ℂ) weight = 1 := by
  unfold ons_mvSeriesEvalNorm
  rw [tsum_eq_sum (s := {0})]
  · simp [ons_mvMonomialValue]
  · intro m hm
    simp only [Finset.mem_singleton] at hm
    rw [MvPowerSeries.coeff_one]
    simp [hm]

theorem ons_MvSeriesEvalSummable.pow
    {E : Type*} [DecidableEq E]
    {f : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight) (n : ℕ) :
    ons_MvSeriesEvalSummable (f ^ n) weight := by
  induction n with
  | zero => simpa using ons_MvSeriesEvalSummable.one weight
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hf

theorem ons_mvSeriesEval_pow
    {E : Type*} [DecidableEq E]
    {f : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight) (n : ℕ) :
    ons_mvSeriesEval (f ^ n) weight = ons_mvSeriesEval f weight ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ons_mvSeriesEval_mul (hf.pow n) hf, ih, pow_succ]

theorem ons_mvSeriesEvalNorm_pow_le
    {E : Type*} [DecidableEq E]
    {f : MvPowerSeries E ℂ} {weight : E → ℂ}
    (hf : ons_MvSeriesEvalSummable f weight) (n : ℕ) :
    ons_mvSeriesEvalNorm (f ^ n) weight ≤
      ons_mvSeriesEvalNorm f weight ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (ons_mvSeriesEvalNorm_mul_le (hf.pow n) hf).trans
        (mul_le_mul_of_nonneg_right ih (by
          unfold ons_mvSeriesEvalNorm
          exact tsum_nonneg fun _ ↦ norm_nonneg _))

theorem ons_powerSeries_exp_coeff_complex (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℂ) =
      (1 : ℂ) / (n.factorial : ℂ) := by
  rw [PowerSeries.coeff_exp]
  push_cast
  rfl

theorem ons_MvSeriesEvalSummable_subst_exp
    {E : Type*} [DecidableEq E]
    (f : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsubst : PowerSeries.HasSubst f)
    (hf : ons_MvSeriesEvalSummable f weight) :
    ons_MvSeriesEvalSummable
      (PowerSeries.subst f (PowerSeries.exp ℂ)) weight := by
  let H := fun n : ℕ ↦ fun m : E →₀ ℕ ↦
    (MvPowerSeries.coeff m (f ^ n) * ons_mvMonomialValue weight m) /
      (n.factorial : ℂ)
  have hfixed : ∀ n, Summable fun m ↦ ‖H n m‖ := by
    intro n
    have hpow := hf.pow n
    have hdiv := hpow.div_const (n.factorial : ℝ)
    simpa only [H, norm_div, Complex.norm_natCast] using hdiv
  have hnormSum : ∀ n,
      (∑' m, ‖H n m‖) =
        ons_mvSeriesEvalNorm (f ^ n) weight / (n.factorial : ℝ) := by
    intro n
    unfold ons_mvSeriesEvalNorm
    simp only [H, norm_div, Complex.norm_natCast]
    rw [tsum_div_const]
  have houter : Summable fun n ↦ ∑' m, ‖H n m‖ := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ tsum_nonneg fun m ↦ norm_nonneg (H n m))
      (fun n ↦ ?_)
      (Real.summable_pow_div_factorial
        (ons_mvSeriesEvalNorm f weight))
    rw [hnormSum]
    exact div_le_div_of_nonneg_right
      (ons_mvSeriesEvalNorm_pow_le hf n)
      (Nat.cast_nonneg n.factorial)
  have hnormJoint : Summable fun p : ℕ × (E →₀ ℕ) ↦
      ‖H p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    exact ⟨hfixed, houter⟩
  have hnormJointSwap : Summable fun p : (E →₀ ℕ) × ℕ ↦
      ‖H p.2 p.1‖ :=
    (Equiv.prodComm (E →₀ ℕ) ℕ).summable_iff.mpr hnormJoint
  have hmajor : Summable fun m : E →₀ ℕ ↦ ∑' n, ‖H n m‖ := by
    exact hnormJointSwap.prod
  apply Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_) hmajor
  rw [PowerSeries.coeff_subst hsubst]
  have hfinite :=
    PowerSeries.coeff_subst_finite hsubst (PowerSeries.exp ℂ) m
  have htf :
      (∑' n : ℕ, PowerSeries.coeff n (PowerSeries.exp ℂ) •
        MvPowerSeries.coeff m (f ^ n)) =
      ∑ᶠ n : ℕ, PowerSeries.coeff n (PowerSeries.exp ℂ) •
        MvPowerSeries.coeff m (f ^ n) :=
    tsum_eq_finsum hfinite
  rw [← htf, ← tsum_mul_right]
  calc
    ‖∑' n : ℕ,
        (PowerSeries.coeff n (PowerSeries.exp ℂ) •
          MvPowerSeries.coeff m (f ^ n)) *
            ons_mvMonomialValue weight m‖ ≤
      ∑' n : ℕ, ‖(PowerSeries.coeff n (PowerSeries.exp ℂ) •
          MvPowerSeries.coeff m (f ^ n)) *
            ons_mvMonomialValue weight m‖ :=
      norm_tsum_le_tsum_norm <| by
        have hm := hnormJointSwap.prod_factor m
        apply hm.congr
        intro n
        rw [ons_powerSeries_exp_coeff_complex]
        simp only [smul_eq_mul, H, norm_div, norm_mul, norm_one]
        ring
    _ = ∑' n, ‖H n m‖ := by
      apply tsum_congr
      intro n
      rw [ons_powerSeries_exp_coeff_complex]
      simp only [smul_eq_mul, H]
      congr 1
      ring

theorem ons_mvSeriesEval_subst_exp
    {E : Type*} [DecidableEq E]
    (f : MvPowerSeries E ℂ) (weight : E → ℂ)
    (hsubst : PowerSeries.HasSubst f)
    (hf : ons_MvSeriesEvalSummable f weight) :
    ons_mvSeriesEval (PowerSeries.subst f (PowerSeries.exp ℂ)) weight =
      Complex.exp (ons_mvSeriesEval f weight) := by
  let H := fun n : ℕ ↦ fun m : E →₀ ℕ ↦
    (MvPowerSeries.coeff m (f ^ n) * ons_mvMonomialValue weight m) /
      (n.factorial : ℂ)
  have hfixed : ∀ n, Summable fun m ↦ ‖H n m‖ := by
    intro n
    have hpow := hf.pow n
    have hdiv := hpow.div_const (n.factorial : ℝ)
    simpa only [H, norm_div, Complex.norm_natCast] using hdiv
  have hnormSum : ∀ n,
      (∑' m, ‖H n m‖) =
        ons_mvSeriesEvalNorm (f ^ n) weight / (n.factorial : ℝ) := by
    intro n
    unfold ons_mvSeriesEvalNorm
    simp only [H, norm_div, Complex.norm_natCast]
    rw [tsum_div_const]
  have houter : Summable fun n ↦ ∑' m, ‖H n m‖ := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ tsum_nonneg fun m ↦ norm_nonneg (H n m))
      (fun n ↦ ?_)
      (Real.summable_pow_div_factorial
        (ons_mvSeriesEvalNorm f weight))
    rw [hnormSum]
    exact div_le_div_of_nonneg_right
      (ons_mvSeriesEvalNorm_pow_le hf n)
      (Nat.cast_nonneg n.factorial)
  have hnormJoint : Summable fun p : ℕ × (E →₀ ℕ) ↦
      ‖H p.1 p.2‖ := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    exact ⟨hfixed, houter⟩
  have hjoint : Summable (Function.uncurry H) :=
    Summable.of_norm hnormJoint
  rw [ons_mvSeriesEval_eq]
  calc
    (∑' m : E →₀ ℕ,
        MvPowerSeries.coeff m
            (PowerSeries.subst f (PowerSeries.exp ℂ)) *
          ons_mvMonomialValue weight m) =
        ∑' m, ∑' n, H n m := by
      apply tsum_congr
      intro m
      rw [PowerSeries.coeff_subst hsubst]
      have hfinite :=
        PowerSeries.coeff_subst_finite hsubst (PowerSeries.exp ℂ) m
      have htf :
          (∑' n : ℕ, PowerSeries.coeff n (PowerSeries.exp ℂ) •
            MvPowerSeries.coeff m (f ^ n)) =
          ∑ᶠ n : ℕ, PowerSeries.coeff n (PowerSeries.exp ℂ) •
            MvPowerSeries.coeff m (f ^ n) :=
        tsum_eq_finsum hfinite
      rw [← htf]
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      rw [ons_powerSeries_exp_coeff_complex]
      simp only [smul_eq_mul, H]
      ring
    _ = ∑' n, ∑' m, H n m := hjoint.tsum_comm
    _ = ∑' n : ℕ,
        ons_mvSeriesEval f weight ^ n / (n.factorial : ℂ) := by
      apply tsum_congr
      intro n
      calc
        (∑' m, H n m) =
            (∑' m : E →₀ ℕ,
              MvPowerSeries.coeff m (f ^ n) *
                ons_mvMonomialValue weight m) /
              (n.factorial : ℂ) := by
                simp only [H]
                rw [tsum_div_const]
        _ = ons_mvSeriesEval (f ^ n) weight / (n.factorial : ℂ) := rfl
        _ = ons_mvSeriesEval f weight ^ n / (n.factorial : ℂ) := by
          rw [ons_mvSeriesEval_pow hf]
    _ = Complex.exp (ons_mvSeriesEval f weight) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact (NormedSpace.expSeries_div_hasSum_exp
        (ons_mvSeriesEval f weight)).tsum_eq

end StatMech.Onsager
