/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Probability.NearHalfBKKKL
import Code.Probability.EntropySubadditivity
import Code.TwoDim.KKLWire

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech.TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC
  StatMech.Probability StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem nhkw_nearHalf_kkl [Nonempty E] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A ≤
      (1 + 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2 * kklw_logMaxInfl p A)
        * ∑ e, StatMech.BeffaraDC.influence p A e := by
  have h := nhb_nearHalf_kkl hp0 hp1 (fun ω => decide (ω ∈ A))
  rw [kklw_decide_eq_indicator A] at h
  rw [kklw_var_eq, ← kklw_logMaxInfl, ← kklw_sum_influence_eq_totalInfl] at h
  exact h




theorem nhkw_hinfl [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)]
    {q v₀ L : ℝ} (hq1 : q ≤ 1) (hv0 : 0 < v₀) (hL : 0 < L)
    (hwindow : 2 * (q - 1 / 2) ^ 2 * L ≤ 1)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ kklw_logMaxInfl p A) :
    ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ * L ≤ ∑ e, StatMech.BeffaraDC.influence p A e := by
  intro p hp
  have hp' : p ∈ Set.Ioo (1 / 2 : ℝ) q := by simpa [interior_Icc] using hp
  have hp0 : 0 < p := by linarith [hp'.1]
  have hp1 : p < 1 := lt_of_lt_of_le hp'.2 hq1
  let V := StatMech.prob p A * (1 - StatMech.prob p A)
  let x := kklw_logMaxInfl p A
  let T := ∑ e, StatMech.BeffaraDC.influence p A e
  let e : ℝ := 2 * (1 - 4 * p * (1 - p)) * (ptn_sigma p) ^ 2
  have hk : 2 * V * x ≤ (1 + e * x) * T := nhkw_nearHalf_kkl hp0 hp1 A
  have hV : v₀ ≤ V := hvar p hp
  have hx : L ≤ x := hlog p hp
  have hx0 : 0 ≤ x := le_trans hL.le hx
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (fun i _ => influence_nonneg hp0.le hp1.le A i)
  have hsigma : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have he0 : 0 ≤ e := by
    dsimp [e]
    rw [hsigma]
    have hA : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
    positivity
  have hep : e ≤ 2 * (p - 1 / 2) ^ 2 := by
    dsimp [e]
    rw [hsigma]
    have hprod : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    nlinarith [sq_nonneg (p - 1 / 2), mul_nonneg (sub_nonneg.mpr hprod) (sq_nonneg (p - 1 / 2))]
  have hpqSq : (p - 1 / 2) ^ 2 ≤ (q - 1 / 2) ^ 2 := by
    nlinarith [hp'.1.le, hp'.2.le]
  have heL : e * L ≤ 1 := by
    calc
      e * L ≤ (2 * (p - 1 / 2) ^ 2) * L :=
        mul_le_mul_of_nonneg_right hep hL.le
      _ ≤ (2 * (q - 1 / 2) ^ 2) * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpqSq (by norm_num)) hL.le
      _ ≤ 1 := hwindow
  have hrearr : (2 * V - e * T) * x ≤ T := by
    nlinarith [hk]
  by_cases hgoal : v₀ * L ≤ T
  · exact hgoal
  have heT : e * T ≤ v₀ := by
    have hTL : T < v₀ * L := lt_of_not_ge hgoal
    calc e * T ≤ e * (v₀ * L) := mul_le_mul_of_nonneg_left hTL.le he0
      _ = (e * L) * v₀ := by ring
      _ ≤ 1 * v₀ := mul_le_mul_of_nonneg_right heL hv0.le
      _ = v₀ := one_mul _
  have hcoef : v₀ ≤ 2 * V - e * T := by linarith [hV, heT]
  calc
    v₀ * L ≤ v₀ * x := mul_le_mul_of_nonneg_left hx hv0.le
    _ ≤ (2 * V - e * T) * x := mul_le_mul_of_nonneg_right hcoef hx0
    _ ≤ T := hrearr



theorem nhkw_sharpThreshold [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L : ℝ} (hq0 : (1 : ℝ) / 2 ≤ q) (hq1 : q ≤ 1)
    (hv0 : 0 < v₀) (hL : 0 < L)
    (hwindow : 2 * (q - 1 / 2) ^ 2 * L ≤ 1)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ kklw_logMaxInfl p A) :
    1 / 2 + (v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  sth_sharpThreshold A hA hq0 hhalf
    (nhkw_hinfl A hq1 hv0 hL hwindow hvar hlog)











theorem nhkw_sharpThreshold_admissible [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {v₀ L ε : ℝ} (hv0 : 0 < v₀) (hL : 0 < L)
    (hεhalf : ε < 1 / 2)
    (hq1 : 2 * (1 / 2 - ε) ≤ v₀ * L)
    (hlarge : 2 * (1 / 2 - ε) ^ 2 ≤ v₀ ^ 2 * L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ)
        (1 / 2 + (1 / 2 - ε) / (v₀ * L))),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hlog : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ)
        (1 / 2 + (1 / 2 - ε) / (v₀ * L))),
      L ≤ kklw_logMaxInfl p A) :
    1 - ε ≤ StatMech.prob (1 / 2 + (1 / 2 - ε) / (v₀ * L)) A := by
  let q : ℝ := 1 / 2 + (1 / 2 - ε) / (v₀ * L)
  have hvL : 0 < v₀ * L := mul_pos hv0 hL
  have ha : 0 < 1 / 2 - ε := by linarith
  have hq0 : (1 : ℝ) / 2 ≤ q := by
    dsimp [q]
    have := div_pos ha hvL
    linarith
  have hqle : q ≤ 1 := by
    have hdiv : (1 / 2 - ε) / (v₀ * L) ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hvL]
      nlinarith
    dsimp [q]
    linarith
  have hwindow : 2 * (q - 1 / 2) ^ 2 * L ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hlarge hL.le
    have hvLne : v₀ * L ≠ 0 := hvL.ne'
    dsimp [q]
    field_simp [hvLne]
    nlinarith [hmul]
  have hsharp := nhkw_sharpThreshold A hA hq0 hqle hv0 hL hwindow hhalf hvar hlog
  have hstep : v₀ * L * (q - 1 / 2) = 1 / 2 - ε := by
    dsimp [q]
    field_simp [hvL.ne']
    ring
  rw [hstep] at hsharp
  linarith






theorem nhkw_sharpThreshold_of_small_maxInfluence [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ delta : ℝ} (hq0 : (1 : ℝ) / 2 <= q) (hq1 : q <= 1)
    (hv0 : 0 < v₀) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hwindow : 2 * (q - 1 / 2) ^ 2 * Real.log (1 / delta) <= 1)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hvar : forall p, p ∈ interior (Set.Icc (1 / 2 : ℝ) q) ->
      v₀ <= StatMech.prob p A * (1 - StatMech.prob p A))
    (hmax : forall p, p ∈ interior (Set.Icc (1 / 2 : ℝ) q) ->
      maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ))) <= delta) :
    1 / 2 + (v₀ * Real.log (1 / delta)) * (q - 1 / 2) <=
      StatMech.prob q A := by
  have hL : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta0 hdelta1)
  apply nhkw_sharpThreshold A hA hq0 hq1 hv0 hL hwindow hhalf hvar
  intro p hp
  have hp' : p ∈ Set.Ioo (1 / 2 : ℝ) q := by
    simpa [interior_Icc] using hp
  have hp0 : 0 < p := by linarith [hp'.1]
  have hp1 : p < 1 := lt_of_lt_of_le hp'.2 hq1
  have hVar : 0 < OSSS.var (OSSS.bernoulliWeight p)
      (fun omega => if decide (omega ∈ A) then (1 : ℝ) else 0) := by
    rw [kklw_decide_eq_indicator A, kklw_var_eq]
    exact hv0.trans_le (hvar p hp)
  have hmaxPos : 0 < maxInfl (OSSS.bernoulliWeight p)
      (A.indicator (fun _ => (1 : ℝ))) := by
    have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
    have hVT : OSSS.var (OSSS.bernoulliWeight p)
        (A.indicator (fun _ => (1 : ℝ))) <=
        totalInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ))) := by
      have h := kkl_var_le_total_influence hprob
        (fun omega : ConfigSpace E => decide (omega ∈ A))
      rwa [kklw_decide_eq_indicator A] at h
    have hTm := kkl_maxInfl_ge_avg (OSSS.bernoulliWeight p)
      (A.indicator (fun _ => (1 : ℝ)))
    have hcard : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
    have hmnn := kkl_maxInfl_nonneg hprob
      (A.indicator (fun _ => (1 : ℝ)))
    rw [kklw_decide_eq_indicator A] at hVar
    by_contra hnot
    have hm0 : maxInfl (OSSS.bernoulliWeight p)
        (A.indicator (fun _ => (1 : ℝ))) = 0 :=
      le_antisymm (not_lt.mp hnot) hmnn
    rw [hm0, mul_zero] at hTm
    linarith
  have hinv : 1 / delta <= 1 / maxInfl (OSSS.bernoulliWeight p)
      (A.indicator (fun _ => (1 : ℝ))) :=
    one_div_le_one_div_of_le hmaxPos (hmax p hp)
  unfold kklw_logMaxInfl
  exact Real.log_le_log (div_pos one_pos hdelta0) hinv

end StatMech.TwoDim
