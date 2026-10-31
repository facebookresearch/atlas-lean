/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform
public import CSLibExt.Complexity.BooleanFunctions.KKL.MaxElementDecomp

/-!
# The capped estimate in the hypercontractive range

Under the Bernoulli(`p`) measure, write the damped total weight
`∑_S 4 |S| (1-u)^{|S|-1} f̂(S)²` as `4p(1-p) ∑ₑ Dₑ(u)` with per-coordinate damped weights
`Dₑ(u)` (`frh_lhs_eq`). When `1 - u = 4p(1-p)(q'-1)` for some `q' ∈ [1, 2]`, that is
`u ≥ 1 - 4p(1-p)`, hypercontractivity of `∂ₑ 1_A` gives the capped estimate
`∑_S 4 |S| (1-u)^{|S|-1} f̂(S)² ≤ δ^{2/q'-1} ∑ₑ Infₑ` (`frh_capped_martingale`). The estimate also
holds at the endpoints `u = 0` and `u = 1`. The predicate `frh_openResidue q` is the capped
estimate with exponent `u/(2-u)` for all `u ∈ (0, 1)` and `p ∈ (1/2, q)`; it is not proved in this
library for any `q > 1/2`.

## Main definitions

* `StatMech.Probability.frh_perCoordWeight`: the per-coordinate damped weight `Dₑ(u)`.
* `StatMech.Probability.frh_openResidue`: the capped estimate on `(1/2, q) × (0, 1)`.

## Main results

* `StatMech.Probability.frh_capped_martingale`: the capped estimate in the hypercontractive
  range.
* `StatMech.Probability.frh_at_zero`, `StatMech.Probability.frh_endpoint_one`: the endpoints.
* `StatMech.Probability.frh_martingaleHC_of_openResidue`: `frh_openResidue q` implies
  `mxd_martingaleHC_statement q`.
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The per-coordinate damped weight `Dₑ(u) = ∑_{S ∋ e} (1-u)^{|S|-1} (f̂(S)/√(p(1-p)))²` under
  `μ_p`. -/
noncomputable def frh_perCoordWeight (p u : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
    (Real.sqrt (1 - u) ^ (S.erase e).card) ^ 2
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2

/-- The damped total weight is `4p(1-p) ∑ₑ Dₑ(u)`. -/
theorem frh_lhs_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = 4 * (ptn_sigma p) ^ 2 * ∑ e : ι, frh_perCoordWeight p u φ e := by
  have hu1' : (0 : ℝ) ≤ 1 - u := by linarith
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2 : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hσ2sq : (0 : ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  set ρ := Real.sqrt (1 - u) with hρ
  have hρsq : ρ ^ 2 = 1 - u := Real.sq_sqrt hu1'
  have hWe : ∀ e : ι, frh_perCoordWeight p u φ e
      = (1 / (ptn_sigma p)^2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * cc S := by
    intro e
    unfold frh_perCoordWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hcc, div_pow, one_div, hρ]; ring
  simp_rw [hWe]
  rw [← Finset.mul_sum]
  rw [show 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ e : ι,
      ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = 4 * ∑ e : ι, ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S from by field_simp]
  rw [Finset.mul_sum]
  have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0) := by
    intro e
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : e ∈ S
    · rw [ite_eq_left he, ite_eq_left he, Finset.card_erase_of_mem he]
    · rw [ite_eq_right he, ite_eq_right he]
  simp_rw [hinner]
  rw [show (∑ e : ι, 4 * ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0))
      = ∑ e : ι, ∑ S : Finset ι, (if e ∈ S then 4 * ((ρ ^ (S.card - 1)) ^ 2 * cc S) else 0) from by
        apply Finset.sum_congr rfl; intro e _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro S _; by_cases he : e ∈ S <;> simp [he]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [show (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) from by rw [← pow_mul, mul_comm,
      pow_mul, hρsq]]
  ring

theorem frh_perCoordWeight_nonneg (p u : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    0 ≤ frh_perCoordWeight p u φ e := by
  unfold frh_perCoordWeight
  exact Finset.sum_nonneg (fun S _ => by positivity)

/-- At `u = 0` the damped total weight is at most the total influence. -/
theorem frh_at_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0 : ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set cc := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hcc
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  have hσ2sq : (0 : ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hσ2ne : (ptn_sigma p)^2 ≠ 0 := ne_of_gt hσ2sq
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0 : ℝ)) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [show (1 : ℝ) - 0 = 1 by norm_num, one_pow]
    rw [show 4 * (ptn_sigma p)^2 * (1 / (ptn_sigma p)^2 * ((S.card : ℝ) * cc S))
        = (4 * ((S.card : ℝ) * cc S)) * ((ptn_sigma p)^2 / (ptn_sigma p)^2) from by ring]
    rw [div_self hσ2ne, mul_one]; ring
  rw [hLHS]
  have hsumnn : 0 ≤ (1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun S _ => by positivity)
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  calc 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S)
      ≤ 1 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S) :=
        mul_le_mul_of_nonneg_right h4σ hsumnn
    _ = (1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S := by rw [one_mul]

/-- The capped estimate in the hypercontractive range: if `1 - u = 4p(1-p)(q'-1)` with `1 ≤ q' ≤ 2`,
  then `∑_S 4 |S| (1-u)^{|S|-1} f̂(S)² ≤ δ^{2/q'-1} ∑ₑ Infₑ`. -/
theorem frh_capped_martingale [Nonempty ι] {p q' : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 ≤ q') (hq2 : q' ≤ 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * (ptn_sigma p) ^ 2
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have hu1' : (0 : ℝ) ≤ 1 - u := by linarith
  set ρ := Real.sqrt (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) := by rw [Real.sq_sqrt hu1']; exact hrel
  have hcap := ptn_capped_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ
  have hσ2sq : (0 : ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hσne : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hpow : ∀ S : Finset ι, (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hu1']
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 *
          ((1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι,
              (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * cc S)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hpow S]
    field_simp
  rw [hLHS]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hcap

/-- Every `u ∈ [1 - 4p(1-p), 1]` has the form `1 - u = 4p(1-p)(q'-1)` with `q' ∈ [1, 2]`. -/
theorem frh_capped_param {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1) :
    ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) := by
  have hs : 0 < 4 * p * (1 - p) := by nlinarith
  refine ⟨1 + (1 - u) / (4 * p * (1 - p)), ?_, ?_, ?_⟩
  · have : 0 ≤ (1 - u) / (4 * p * (1 - p)) := by
      apply div_nonneg (by linarith) (by linarith)
    linarith
  · have : (1 - u) / (4 * p * (1 - p)) ≤ 1 := by
      rw [div_le_one hs]; linarith
    linarith
  · rw [show (1 + (1 - u) / (4 * p * (1 - p)) - 1) * 4 * p * (1 - p)
        = ((1 - u) / (4 * p * (1 - p))) * (4 * p * (1 - p)) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt hs)]

/-- The capped estimate `∑_S 4 |S| (1-u)^{|S|-1} f̂(S)² ≤ δ^{u/(2-u)} ∑ₑ Infₑ` for all `p ∈ (1/2,
  q)` with `p < 1` and all `u ∈ (0, 1)`. Not proved in this library for any `q > 1/2`. -/
def frh_openResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool), ∀ u : ℝ, 0 < u → u < 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)

/-- At `u = 1` the capped estimate holds. -/
theorem frh_endpoint_one [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1 : ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ ((1 : ℝ) / (2 - 1))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hcap := frh_capped_martingale hp0 hp1 (le_refl (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ)) (by ring) φ
  have hδnn : 0 ≤ δ := by
    rw [hδ]; exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := by
    rw [hT]; exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  have hσnn : (0 : ℝ) ≤ 4 * (ptn_sigma p)^2 := by positivity
  have hexp1 : (2 : ℝ) / 1 - 1 = (1 : ℝ) / (2 - 1) := by norm_num
  have hRHSnn : 0 ≤ δ ^ ((2 : ℝ)/1 - 1) * T := by positivity
  refine le_trans hcap ?_
  calc 4 * (ptn_sigma p)^2 * (δ ^ ((2 : ℝ)/1 - 1) * T)
      ≤ 1 * (δ ^ ((2 : ℝ)/1 - 1) * T) := mul_le_mul_of_nonneg_right h4σ hRHSnn
    _ = δ ^ ((2 : ℝ)/1 - 1) * T := by rw [one_mul]
    _ = δ ^ ((1 : ℝ) / (2 - 1)) * T := by rw [hexp1]

/-- `frh_openResidue q` implies `mxd_martingaleHC_statement q`, by adding the endpoints. -/
theorem frh_martingaleHC_of_openResidue {q : ℝ} (H : frh_openResidue q) :
    mxd_martingaleHC_statement q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  rcases eq_or_lt_of_le hu0 with hu0' | hu0'
  · subst hu0'
    have hbnd := frh_at_zero hp0 hp1 φ
    rw [show (0 : ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
    exact hbnd
  · rcases eq_or_lt_of_le hu1 with hu1' | hu1'
    · subst hu1'
      exact frh_endpoint_one hp0 hp1 φ
    · exact H p hp hp1 φ u hu0' hu1'

/-- For `p > 1/2` the hypercontractive range `u ≥ 1 - 4p(1-p)` excludes a nonempty interval near `u
  = 0`. -/
theorem frh_lowNoise_range_nonempty {p : ℝ} (hp : 1 / 2 < p) (_hp1 : p < 1) :
    0 < 1 - 4 * p * (1 - p) := by
  have heq : 1 - 4 * p * (1 - p) = (1 - 2 * p) ^ 2 := by ring
  rw [heq]
  have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
  positivity

end StatMech.Probability
