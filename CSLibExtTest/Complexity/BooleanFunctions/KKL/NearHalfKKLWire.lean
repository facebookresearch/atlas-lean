/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.NearHalfKKLWire
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLEvents
public import CSLibExtTest.Complexity.BooleanFunctions.Hypercontractivity.PBiasedTensorize

/-!
# Tests for the near-half KKL inequality for events and its sharp-threshold wire

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.NearHalfKKLWire`:

* `nhkw_nearHalf_kkl` at the event `{ω | ω true ∧ ω false}` and `p = 1/2`, where the correction
  vanishes: `2 · 3/16 · log 2 ≤ 1`;
* `nhkw_hinfl` on a genuine window: for the same event, `P_p = p²`, `∑ₑ Infₑ = 2p` and
  `log (1 / maxₑ Infₑ) = log (1/p)`, so on `[1/2, 3/5]` the hypotheses hold with
  `v₀ = 3/16`, `L = log (5/3)`, and the conclusion `3/16 · log(5/3) ≤ 2p` follows for every `p`
  in the interior;
* `nhkw_sharpThreshold`, `nhkw_sharpThreshold_admissible` and
  `nhkw_sharpThreshold_of_small_maxInfluence` on the window `[1/2, 3/5]` for three-bit majority,
  an increasing event with `P_p = 3p² - 2p³` (so `P_{1/2} = 1/2`) and all influences `2p(1-p)`:
  there the variance is at least `1/5` and `log (1 / maxₑ Infₑ) ≥ log 2 ≥ 1/2`, so every hypothesis
  holds with `q = 3/5` (resp. `ε = 49/100`, `δ = 1/2`) and the conclusions are
  `1/2 + 1/100 ≤ P_{3/5} = 81/125` and its variants. On two coordinates no such witness exists:
  the only increasing events with `P_{1/2} = 1/2` are dictators, with maximal influence `1`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability StatMech.TwoDim

/-- `nhkw_nearHalf_kkl` at the `AND` event and `p = 1/2`. -/
example : 2 * (1 / 4 * (1 - 1 / 4) : ℝ) * Real.log 2 ≤ 1 := by
  classical
  have h := nhkw_nearHalf_kkl (p := 1 / 2) (by norm_num) (by norm_num) andEvent
  rw [prob_andEvent, logMaxInfl_andEvent, Fintype.sum_bool, influence_andEvent,
    influence_andEvent] at h
  norm_num at h ⊢
  linarith

/-- `P_p` of the `AND` event is `p²`. -/
lemma nhkwt_prob_andEvent (p : ℝ) : StatMech.prob p andEvent = p ^ 2 := by
  rw [kklw_prob_eq_expect, andEvent_indicator]
  simp [expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  ring

/-- `log (1 / maxₑ Infₑ)` of the `AND` event under `μ_p` is `log (1/p)`. -/
lemma nhkwt_logMaxInfl_andEvent (p : ℝ) : kklw_logMaxInfl p andEvent = Real.log (1 / p) := by
  rw [kklw_logMaxInfl, andEvent_indicator, maxInfl_andInd_p]

/-- The total influence of the `AND` event under `μ_p` is `2p`. -/
lemma nhkwt_sum_influence_andEvent (p : ℝ) :
    ∑ e, StatMech.BeffaraDC.influence p andEvent e = 2 * p := by
  simp only [kklw_influence_eq_infl, andEvent_indicator]
  exact totalInfl_andInd_p p

/-- `nhkw_hinfl` on the window `[1/2, 3/5]` for the `AND` event. -/
example {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5)) :
    3 / 16 * Real.log (5 / 3) ≤ 2 * p := by
  classical
  have hlog53 : Real.log (5 / 3 : ℝ) ≤ 2 / 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 3 by norm_num)
    linarith
  have h := nhkw_hinfl andEvent (q := 3 / 5) (v₀ := 3 / 16) (L := Real.log (5 / 3))
    (by norm_num) (by norm_num) (Real.log_pos (by norm_num))
    (by nlinarith [hlog53])
    (fun p hp => by
      rw [interior_Icc] at hp
      rw [nhkwt_prob_andEvent]
      obtain ⟨h1, h2⟩ := hp
      have ha : 1 / 4 < p ^ 2 := by nlinarith
      have hb : p ^ 2 < 3 / 4 := by nlinarith
      nlinarith)
    (fun p hp => by
      rw [interior_Icc] at hp
      obtain ⟨h1, h2⟩ := hp
      rw [nhkwt_logMaxInfl_andEvent]
      have hp0 : 0 < p := by linarith
      exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hp0]; linarith))
    p (by rw [interior_Icc]; exact hp)
  rwa [nhkwt_sum_influence_andEvent] at h

/-! ## The sharp-threshold wire on a genuine window: three-bit majority -/

/-- Expansion of a sum over `{0, 1}^3` into eight terms. -/
lemma nhkwt_sum_configSpace_fin_three (g : ConfigSpace (Fin 3) → ℝ) :
    ∑ ω, g ω = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, g ![a, b, c] := by
  rw [← (Fin.consEquiv fun _ : Fin 3 => Bool).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ : Fin 2 => Bool).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  refine Finset.sum_congr rfl fun c _ => congrArg g ?_
  funext i; fin_cases i <;> rfl

/-- Three-bit majority. -/
def nhkwt_maj3 (ω : ConfigSpace (Fin 3)) : Bool := (ω 0 && ω 1) || (ω 0 && ω 2) || (ω 1 && ω 2)

/-- The majority event on `{0, 1}^3`. -/
def nhkwt_majEvent : Set (ConfigSpace (Fin 3)) := {ω | nhkwt_maj3 ω = true}

/-- Majority is increasing. -/
lemma nhkwt_majEvent_isIncreasing : IsIncreasing nhkwt_majEvent := by
  intro ω ω' hle h
  have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
  simp only [nhkwt_majEvent, nhkwt_maj3, Set.mem_ofPred_eq] at h ⊢
  revert h0 h1 h2 h
  cases ω 0 <;> cases ω 1 <;> cases ω 2 <;> cases ω' 0 <;> cases ω' 1 <;> cases ω' 2 <;> decide

/-- The indicator of the majority event. -/
lemma nhkwt_majEvent_indicator :
    nhkwt_majEvent.indicator (fun _ => (1 : ℝ))
      = fun ω => if nhkwt_maj3 ω then (1 : ℝ) else 0 := by
  funext ω; simp [nhkwt_majEvent, Set.indicator_apply]

/-- `P_p(majority) = 3p² - 2p³`. -/
lemma nhkwt_prob_majEvent (p : ℝ) : StatMech.prob p nhkwt_majEvent = 3 * p ^ 2 - 2 * p ^ 3 := by
  rw [kklw_prob_eq_expect, nhkwt_majEvent_indicator]
  simp [expect, weight, nhkwt_sum_configSpace_fin_three, nhkwt_maj3, bernoulliWeight,
    Fin.prod_univ_three]
  ring

/-- Every coordinate of majority has influence `2p(1-p)` under `μ_p`. -/
lemma nhkwt_infl_maj3 (p : ℝ) (e : Fin 3) :
    infl (bernoulliWeight p) (fun ω => if nhkwt_maj3 ω then (1 : ℝ) else 0) e
      = 2 * p * (1 - p) := by
  fin_cases e <;>
  · simp [infl, expect, weight, nhkwt_sum_configSpace_fin_three, nhkwt_maj3, bernoulliWeight,
      Fin.prod_univ_three, setOpen, setClosed]
    ring

/-- The maximal influence of majority under `μ_p` is `2p(1-p)`. -/
lemma nhkwt_maxInfl_majEvent (p : ℝ) :
    maxInfl (bernoulliWeight p) (nhkwt_majEvent.indicator (fun _ => (1 : ℝ)))
      = 2 * p * (1 - p) := by
  rw [nhkwt_majEvent_indicator]
  unfold maxInfl
  rw [show infl (bernoulliWeight p) (fun ω => if nhkwt_maj3 ω then (1 : ℝ) else 0)
      = fun _ => 2 * p * (1 - p) from funext (nhkwt_infl_maj3 p), Finset.sup'_const]

/-- `log (1 / maxₑ Infₑ)` of majority under `μ_p`. -/
lemma nhkwt_logMaxInfl_majEvent (p : ℝ) :
    kklw_logMaxInfl p nhkwt_majEvent = Real.log (1 / (2 * p * (1 - p))) := by
  rw [kklw_logMaxInfl, nhkwt_maxInfl_majEvent]

/-- On `[1/2, 3/5]` majority has variance at least `1/5` and log-max-influence at least `1/2`. -/
lemma nhkwt_maj_window {p : ℝ} (hp : p ∈ interior (Set.Icc (1 / 2 : ℝ) (3 / 5))) :
    1 / 5 ≤ StatMech.prob p nhkwt_majEvent * (1 - StatMech.prob p nhkwt_majEvent) ∧
      1 / 2 ≤ kklw_logMaxInfl p nhkwt_majEvent := by
  rw [interior_Icc] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [nhkwt_prob_majEvent, nhkwt_logMaxInfl_majEvent]
  refine ⟨?_, ?_⟩
  · have hlo : 1 / 2 ≤ 3 * p ^ 2 - 2 * p ^ 3 := by
      nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h1)]
    have hhi : 3 * p ^ 2 - 2 * p ^ 3 ≤ 7 / 10 := by
      nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]
    nlinarith
  · have hx : 0 < 2 * p * (1 - p) := by nlinarith
    have hle : 2 ≤ 1 / (2 * p * (1 - p)) := by
      rw [le_div_iff₀ hx]; nlinarith [sq_nonneg (2 * p - 1)]
    have := Real.log_le_log (by norm_num) hle
    have := Real.log_two_gt_d9
    linarith

/-- `nhkw_sharpThreshold` for majority on the window `[1/2, 3/5]`. -/
example : 1 / 2 + (1 / 5 * (1 / 2)) * ((3 / 5 : ℝ) - 1 / 2)
    ≤ StatMech.prob (3 / 5) nhkwt_majEvent := by
  classical
  exact nhkw_sharpThreshold nhkwt_majEvent nhkwt_majEvent_isIncreasing (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [nhkwt_prob_majEvent]; norm_num)
    (fun p hp => (nhkwt_maj_window hp).1) (fun p hp => (nhkwt_maj_window hp).2)

/-- The bound is not sharp here: `P_{3/5}(majority) = 81/125`. -/
example : 1 / 2 + (1 / 5 * (1 / 2)) * ((3 / 5 : ℝ) - 1 / 2)
    < StatMech.prob (3 / 5) nhkwt_majEvent := by
  rw [nhkwt_prob_majEvent]; norm_num

/-- `nhkw_sharpThreshold_admissible` for majority with `ε = 49/100` (window `[1/2, 3/5]`). -/
example : 1 - 49 / 100
    ≤ StatMech.prob (1 / 2 + (1 / 2 - 49 / 100) / (1 / 5 * (1 / 2))) nhkwt_majEvent := by
  classical
  have hq : (1 / 2 + (1 / 2 - 49 / 100) / (1 / 5 * (1 / 2)) : ℝ) = 3 / 5 := by norm_num
  exact nhkw_sharpThreshold_admissible nhkwt_majEvent nhkwt_majEvent_isIncreasing (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [nhkwt_prob_majEvent]; norm_num)
    (fun p hp => (nhkwt_maj_window (hq ▸ hp)).1) (fun p hp => (nhkwt_maj_window (hq ▸ hp)).2)

/-- `nhkw_sharpThreshold_of_small_maxInfluence` for majority, `δ = 1/2`. -/
example : 1 / 2 + (1 / 5 * Real.log (1 / (1 / 2))) * ((3 / 5 : ℝ) - 1 / 2)
    ≤ StatMech.prob (3 / 5) nhkwt_majEvent := by
  classical
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  refine nhkw_sharpThreshold_of_small_maxInfluence nhkwt_majEvent nhkwt_majEvent_isIncreasing
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num; nlinarith)
    (by rw [nhkwt_prob_majEvent]; norm_num) (fun p hp => (nhkwt_maj_window hp).1) (fun p _ => ?_)
  rw [nhkwt_maxInfl_majEvent]
  nlinarith [sq_nonneg (2 * p - 1)]

end StatMechTest.BooleanFunctions
