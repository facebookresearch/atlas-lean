/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Hypercontractivity.ConvexGapHC

/-!
# The capped estimate in the hypercontractive range with a gap condition

In the hypercontractive range `u ≥ 1 - 4p(1-p)`, `frh_capped_martingale` gives the capped
estimate with exponent `2/q' - 1`, where `1 - u = 4p(1-p)(q'-1)`; this is at most the target
exponent `u/(2-u)` (`hcq_exponent_le`). The two bounds differ by the factor `4p(1-p)` and by the
exponent gap; when `δ^{gap} ≥ 4p(1-p)` the target estimate follows
(`hcq_star_capped_threshold`). At `p = 1/2` the gap vanishes and the estimate holds for all
`u ∈ (0, 1)` (`hcq_smallDelta_p_half`). The predicate `hcq_lowRangeResidue q` covers the remaining
parameters; it is not proved in this library for any `q > 1/2`.

## Main definitions

* `StatMech.Probability.hcq_lowRangeResidue`: the capped estimate on `(1/2, q)` outside the range
  handled here.

## Main results

* `StatMech.Probability.hcq_exponent_le`: `2/q' - 1 ≤ u/(2-u)`.
* `StatMech.Probability.hcq_star_capped_threshold`: the capped estimate under the gap condition.
* `StatMech.Probability.hcq_smallDelta_p_half`: the capped estimate at `p = 1/2`.
* `StatMech.Probability.hcq_smallDelta_of_lowRange`: `hcq_lowRangeResidue q` implies
  `cvg_smallDeltaResidue q`.
* `StatMech.Probability.hcq_residue_proper`, `StatMech.Probability.hcq_antecedent_not_tautology`:
  for `p > 1/2` the gap condition holds for some `u`, so the hypothesis of
  `hcq_lowRangeResidue` is not always true.
-/

@[expose] public section

open scoped BigOperators
open Finset
open Real Set

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the hypercontractive range the exponent `2/q' - 1` is at most the target exponent `u/(2-u)`.
-/
theorem hcq_exponent_le {p q' u : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hu1 : u < 1) (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) :
    2 / q' - 1 ≤ u / (2 - u) := by
  have h4 : 0 < 4 * p * (1 - p) := by nlinarith
  have h4le : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hq1 : 1 ≤ q' := by nlinarith
  have h2u : 0 < 2 - u := by linarith
  have hge : 2 - u ≤ q' := by
    have hgeqm1 : 1 - u ≤ q' - 1 := by rw [hrel]; nlinarith [hq1]
    linarith
  have hdiv : 2 / q' ≤ 2 / (2 - u) := div_le_div_of_nonneg_left (by norm_num) h2u hge
  have htgt : 2 / (2 - u) - 1 = u / (2 - u) := by field_simp; ring
  linarith [hdiv, htgt]

/-- Closed form of the exponent gap `u/(2-u) - (2/q' - 1)`. -/
theorem hcq_gap_closedForm {s u : ℝ} (hs0 : 0 < s) (hu1 : u < 1) (hslu : 0 < s + 1 - u) :
    u / (2 - u) - (2 / (1 + (1 - u) / s) - 1)
      = 2 * (1 - u) * (1 - s) / ((s + 1 - u) * (2 - u)) := by
  have h2u : 0 < 2 - u := by linarith
  have hrw : (1 : ℝ) + (1 - u) / s = (s + 1 - u) / s := by field_simp; ring
  rw [hrw, div_div_eq_mul_div, div_sub_one (ne_of_gt hslu)]
  field_simp
  ring

/-- Upper bound on the exponent gap. -/
theorem hcq_gap_le {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu_lo : 1 - s < u) (hu_hi : u < 1) :
    u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ 2 * (1 - u) * (1 - s) / s := by
  have hslu : 0 < s + 1 - u := by linarith
  rw [hcq_gap_closedForm hs0 hu_hi hslu]
  have h1u : 0 < 1 - u := by linarith
  have h1s : 0 < 1 - s := by linarith
  apply div_le_div_of_nonneg_left (by positivity) hs0
  nlinarith [h1u, h1s]

/-- The capped estimate in the hypercontractive range, with the matching `q'`. -/
theorem hcq_capped_full [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1) :
    ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) ∧
      (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ 4 * (ptn_sigma p) ^ 2
          * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  obtain ⟨q', hq1, hq2, hrel⟩ := frh_capped_param hp0 hp1 hlo hu1
  refine ⟨q', hq1, hq2, hrel, ?_⟩
  have hu0 : 0 ≤ u := by nlinarith [sq_nonneg (1 - 2 * p)]
  exact frh_capped_martingale hp0 hp1 hq1 hq2 hu0 hu1 hrel φ

/-- If `δ^{gap} ≥ 4p(1-p)`, the bound with exponent `2/q' - 1` and factor `4p(1-p)` is at most
  `δ^{u/(2-u)}`. -/
theorem hcq_dom_of_threshold {p δ q' u : ℝ} (hδ0 : 0 < δ)
    (hthr : 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / q' - 1))) :
    4 * (ptn_sigma p) ^ 2 * δ ^ (2 / q' - 1) ≤ δ ^ (u / (2 - u)) := by
  have key : δ ^ (u / (2 - u)) = δ ^ (u / (2 - u) - (2 / q' - 1)) * δ ^ (2 / q' - 1) := by
    rw [← Real.rpow_add hδ0]; congr 1; ring
  rw [key]
  exact mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg hδ0.le _)

/-- The capped estimate with exponent `u/(2-u)` from a domination of the hypercontractive bound. -/
theorem hcq_star_of_dominates [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1)
    {q' : ℝ} (hq1 : 1 ≤ q') (hq2 : q' ≤ 2)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
    (hdom : 4 * (ptn_sigma p) ^ 2
        * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hu0 : 0 ≤ u := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hcap := frh_capped_martingale hp0 hp1 hq1 hq2 hu0 hu1 hrel φ
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  calc (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * (ptn_sigma p) ^ 2 * (δ ^ (2 / q' - 1) * T) := hcap
    _ = (4 * (ptn_sigma p) ^ 2 * δ ^ (2 / q' - 1)) * T := by ring
    _ ≤ δ ^ (u / (2 - u)) * T := mul_le_mul_of_nonneg_right hdom hTnn

/-- The capped estimate with exponent `u/(2-u)` in the hypercontractive range, under the gap
  condition `δ^{gap} ≥ 4p(1-p)`. -/
theorem hcq_star_capped_threshold [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u < 1)
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    {q' : ℝ} (hq1 : 1 ≤ q') (hq2 : q' ≤ 2)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
    (hthr : 4 * (ptn_sigma p) ^ 2
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u) - (2 / q' - 1))) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hdom := hcq_dom_of_threshold hδ0 hthr
  exact hcq_star_of_dominates hp0 hp1 φ hlo hu1.le hq1 hq2 hrel hdom

/-- At `p = 1/2` the capped estimate `∑_S 4 |S| (1-u)^{|S|-1} f̂(S)² ≤ δ^{u/(2-u)} ∑ₑ Infₑ` holds
  for all `u ∈ (0, 1)`. -/
theorem hcq_smallDelta_p_half [Nonempty ι]
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  have h4σ : (4 : ℝ) * (ptn_sigma (1 / 2 : ℝ)) ^ 2 = 1 := by
    rw [ptn_sigma_sq hp0 hp1]; norm_num
  have hlo : 1 - 4 * (1 / 2 : ℝ) * (1 - 1 / 2) ≤ u := by norm_num; linarith [hu0]
  set q' : ℝ := 2 - u with hq'
  have hq1 : 1 ≤ q' := by rw [hq']; linarith
  have hq2 : q' ≤ 2 := by rw [hq']; linarith
  have hrel : 1 - u = (q' - 1) * 4 * (1 / 2 : ℝ) * (1 - 1 / 2) := by rw [hq']; ring
  have h2u0 : (2 : ℝ) - u ≠ 0 := by intro h; linarith
  have hgap : u / (2 - u) - (2 / q' - 1) = 0 := by
    rw [hq', sub_eq_zero, div_sub_one h2u0]
    congr 1; ring
  have hδ0 : 0 < maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      ∨ maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
    rcases eq_or_lt_of_le (kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le) _) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hδ0 with hδpos | hδzero
  · apply hcq_star_capped_threshold hp0 hp1 φ hlo hu1 hδpos hq1 hq2 hrel
    rw [hgap, Real.rpow_zero, h4σ]
  · have hcap := frh_capped_martingale hp0 hp1 hq1 hq2 (by linarith [hu0]) hu1.le hrel φ
    rw [hδzero] at hcap ⊢
    have hupos : u / (2 - u) ≠ 0 := by
      have h2u : (0 : ℝ) < 2 - u := by linarith
      positivity
    rw [Real.zero_rpow hupos, zero_mul]
    rw [Real.zero_rpow (by
      have : (2 : ℝ) / q' - 1 = u / (2 - u) := by
        rw [hq', div_sub_one h2u0]; congr 1; ring
      rw [this]; exact hupos)] at hcap
    simpa using hcap

/-- The capped estimate for all `p ∈ (1/2, q)` with `p < 1`, `δ < e^{-1}`, and `u ∈ (0, 1)` either
  below the hypercontractive range or failing the gap condition. Not proved in this library for
  any `q > 1/2`. -/
def hcq_lowRangeResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < Real.exp (-1) →
      ∀ u : ℝ, 0 < u → u < 1 →
        (u < 1 - 4 * p * (1 - p) ∨
          (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1))
            < 4 * (ptn_sigma p) ^ 2) →
        (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)

/-- `hcq_lowRangeResidue q` implies `cvg_smallDeltaResidue q`. -/
theorem hcq_smallDelta_of_lowRange {q : ℝ} (H : hcq_lowRangeResidue q) :
    cvg_smallDeltaResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδdef
  set q' : ℝ := 1 + (1 - u) / (4 * p * (1 - p)) with hq'
  have h4 : (0 : ℝ) < 4 * p * (1 - p) := by nlinarith
  have hrel : 1 - u = (q' - 1) * 4 * p * (1 - p) := by
    rw [hq']
    rw [show (1 + (1 - u) / (4 * p * (1 - p)) - 1) * 4 * p * (1 - p)
        = ((1 - u) / (4 * p * (1 - p))) * (4 * p * (1 - p)) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h4)]
  by_cases hcapped : 1 - 4 * p * (1 - p) ≤ u
  · have hq1' : 1 ≤ q' := by
      rw [hq']
      have : 0 ≤ (1 - u) / (4 * p * (1 - p)) := div_nonneg (by linarith) h4.le
      linarith
    have hq2' : q' ≤ 2 := by
      rw [hq']
      have hsmall : (1 - u) / (4 * p * (1 - p)) ≤ 1 := by
        rw [div_le_one h4]; linarith
      linarith
    have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
    rcases eq_or_lt_of_le hδnn with hδ00 | hδ0
    · have hupos : (0 : ℝ) < u / (2 - u) := by
        have h2u : (0 : ℝ) < 2 - u := by linarith
        positivity
      have hT0 : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
        unfold totalInfl
        apply Finset.sum_eq_zero
        intro e _
        have hle : OSSS.infl (OSSS.bernoulliWeight p)
            (fun ω => if φ ω then (1 : ℝ) else 0) e ≤ δ := by
          rw [hδdef]; exact kkl_infl_le_maxInfl _ _ e
        have hge : 0 ≤ OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e :=
          OSSS.infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _ e
        rw [← hδ00] at hle; linarith
      rw [hT0, mul_zero]
      have hcap := frh_capped_martingale hp0 hp1 hq1' hq2'
        (by nlinarith [sq_nonneg (1 - 2*p)]) hu1.le hrel φ
      rw [← hδdef, hT0, mul_zero, mul_zero] at hcap
      exact hcap
    · by_cases hthr : 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / q' - 1))
      · exact hcq_star_capped_threshold hp0 hp1 φ hcapped hu1 hδ0 hq1' hq2' hrel hthr
      · rw [not_le] at hthr
        exact H p hp hp1 φ hδ u hu0 hu1 (Or.inr hthr)
  · rw [not_le] at hcapped
    exact H p hp hp1 φ hδ u hu0 hu1 (Or.inl hcapped)

/-- `hcq_lowRangeResidue q` implies `mxd_martingaleHC_statement q`. -/
theorem hcq_martingaleHC_of_lowRange {q : ℝ} (H : hcq_lowRangeResidue q) :
    mxd_martingaleHC_statement q :=
  cvg_martingaleHC_of_smallDelta (hcq_smallDelta_of_lowRange H)

/-- At `u = 1` (`q' = 1`) the gap condition holds. -/
theorem hcq_dominated_nonempty {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (_hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) :
    4 * (ptn_sigma p) ^ 2 ≤ δ ^ ((1 : ℝ) / (2 - 1) - (2 / (1 : ℝ) - 1)) := by
  have hgap : (1 : ℝ) / (2 - 1) - (2 / (1 : ℝ) - 1) = 0 := by norm_num
  rw [hgap, Real.rpow_zero]
  rw [ptn_sigma_sq hp0 hp1]
  nlinarith [sq_nonneg (1 - 2 * p)]

/-- `s ≤ δ^g` when `g ≤ log (1/s) / log (1/δ)`. -/
theorem hcq_threshold_of_gap_small {s δ g : ℝ} (hs0 : 0 < s)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hgle : g ≤ Real.log (1 / s) / Real.log (1 / δ)) :
    s ≤ δ ^ g := by
  have hlδ : 0 < Real.log (1 / δ) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hδ0]; linarith
  rw [Real.rpow_def_of_pos hδ0, show s = Real.exp (Real.log s) from (Real.exp_log hs0).symm]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (ne_of_gt hδ0), Real.log_one, zero_sub] at hgle hlδ
  rw [Real.log_div (by norm_num) (ne_of_gt hs0), Real.log_one, zero_sub] at hgle
  rw [le_div_iff₀ hlδ] at hgle
  nlinarith [hgle, mul_comm g (Real.log δ)]

/-- For `p > 1/2` and `0 < δ < 1`, some `u ∈ (0, 1)` lies in the hypercontractive range and
  satisfies the gap condition. -/
theorem hcq_residue_proper {p δ : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ u : ℝ, (0 < u ∧ u < 1) ∧ 1 - 4 * p * (1 - p) ≤ u ∧
      4 * (ptn_sigma p) ^ 2
        ≤ δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1)) := by
  have hp0 : 0 < p := by linarith
  set s := 4 * p * (1 - p) with hsdef
  have hsval : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p) ^ 2 = s := by rw [hsval, hsdef]; ring
  have hs0 : 0 < s := by rw [hsdef]; nlinarith
  have hs1 : s < 1 := by
    rw [hsdef]
    have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
    have hpos : 0 < (1 - 2 * p) ^ 2 := by positivity
    nlinarith [hpos]
  set B := Real.log (1 / s) / Real.log (1 / δ) with hBdef
  have hlδ : 0 < Real.log (1 / δ) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hδ0]; linarith
  have hls : 0 < Real.log (1 / s) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hs0]; linarith
  have hB : 0 < B := by rw [hBdef]; positivity
  have h1s : 0 < 1 - s := by linarith
  set m := min s (B * s / (2 * (1 - s))) with hm
  have hmpos : 0 < m := by rw [hm]; apply lt_min hs0; positivity
  have hms_s : m ≤ s := min_le_left _ _
  have hms_B : m ≤ B * s / (2 * (1 - s)) := min_le_right _ _
  set t := m / 2 with htdef
  have htpos : 0 < t := by positivity
  have hts : t < s := by rw [htdef]; linarith [hmpos]
  set u := 1 - t with hudef
  refine ⟨u, ⟨by rw [hudef]; linarith [hts, hs1], by rw [hudef]; linarith⟩, ?_, ?_⟩
  · rw [hudef]; linarith [hts]
  · rw [h4σ]
    have hu_lo : 1 - s < u := by rw [hudef]; linarith [hts]
    have hu_hi : u < 1 := by rw [hudef]; linarith
    have hgapbd : u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ 2 * (1 - u) * (1 - s) / s :=
      hcq_gap_le hs0 hs1 hu_lo hu_hi
    have h1u_eq : 1 - u = t := by rw [hudef]; ring
    have hgleB : 2 * (1 - u) * (1 - s) / s ≤ B := by
      rw [h1u_eq, div_le_iff₀ hs0]
      have hstep : (B * s / (2 * (1 - s))) * (1 - s) = B * s / 2 := by field_simp
      calc 2 * t * (1 - s) = (2 * t) * (1 - s) := by ring
        _ ≤ (2 * (B * s / (2 * (1 - s)))) * (1 - s) :=
            mul_le_mul_of_nonneg_right (by linarith [hms_B]) h1s.le
        _ = 2 * (B * s / 2) := by rw [mul_assoc, hstep]
        _ = B * s := by ring
    have hgle : u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ B := le_trans hgapbd hgleB
    rw [hBdef] at hgle
    exact hcq_threshold_of_gap_small hs0 hδ0 hδ1 hgle

/-- For `p > 1/2` and `0 < δ < 1`, the case condition in `hcq_lowRangeResidue` fails for some `u ∈
  (0, 1)`. -/
theorem hcq_antecedent_not_tautology {p δ : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ u : ℝ, (0 < u ∧ u < 1) ∧
      ¬ (u < 1 - 4 * p * (1 - p) ∨
          δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1))
            < 4 * (ptn_sigma p) ^ 2) := by
  obtain ⟨u, hu, hcap, hthr⟩ := hcq_residue_proper hp hp1 hδ0 hδ1
  refine ⟨u, hu, ?_⟩
  rintro (hlow | hbad)
  · linarith [hcap]
  · linarith [hthr]

/-- The right side `δ^{u/(2-u)} ∑ₑ Infₑ` of the capped estimate is nonnegative. -/
theorem hcq_lowRange_nonvacuous {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    {u : ℝ} (_hu0 : 0 < u) (_hu1 : u < 1) :
    (0 : ℝ)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  apply mul_nonneg
  · exact Real.rpow_nonneg
      (kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _) _
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _

end StatMech.Probability
