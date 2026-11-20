/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Sharpness.PivotalFactor
import Code.BeffaraDC.RussoInfluence
import Code.Inequalities.IncreasingEvent

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC

variable {E : Type*} [Fintype E] [DecidableEq E]










theorem sth_prob_differentiable (A : Set (ConfigSpace E)) :
    Differentiable ℝ (fun p => prob p A) :=
  fun p => (hasDerivAt_prob A p).differentiableAt




theorem sth_sum_configWeight_eq_one (p : ℝ) :
    ∑ ω : ConfigSpace E, configWeight p ω = 1 := by
  unfold configWeight edgeWeight
  rw [← Fintype.prod_sum (fun (e : E) (b : Bool) => if b then p else 1 - p)]
  apply Finset.prod_eq_one
  intro e _
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]; ring



theorem sth_prob_le_one (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    prob p A ≤ 1 := by
  unfold prob
  calc ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeight p ω
      ≤ ∑ ω : ConfigSpace E, configWeight p ω := by
        apply Finset.sum_le_sum
        intro ω _
        have hind : A.indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
          classical rw [Set.indicator_apply]; split_ifs <;> norm_num
        have hcw : 0 ≤ configWeight p ω := Sharpness.configWeight_nonneg hp0 hp1 ω
        nlinarith [hind, hcw]
    _ = 1 := sth_sum_configWeight_eq_one p



theorem sth_prob_nonneg (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ prob p A := by
  unfold prob
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (Sharpness.configWeight_nonneg hp0 hp1 ω)











theorem sth_prob_monotoneOn (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    MonotoneOn (fun p => prob p A) (Set.Icc (0 : ℝ) 1) := by
  have hdiff : Differentiable ℝ (fun p => prob p A) := sth_prob_differentiable A
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn
  intro p hp
  rw [interior_Icc, Set.mem_Ioo] at hp
  exact deriv_prob_nonneg A hA hp.1.le hp.2.le















theorem sth_prob_sub_ge_of_deriv_ge (A : Set (ConfigSpace E)) {a b M : ℝ} (hab : a ≤ b)
    (hge : ∀ p ∈ interior (Set.Icc a b), M ≤ deriv (fun p => prob p A) p) :
    M * (b - a) ≤ prob b A - prob a A := by
  have hdiff : Differentiable ℝ (fun p => prob p A) := sth_prob_differentiable A
  exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn hge
    a (Set.left_mem_Icc.mpr hab) b (Set.right_mem_Icc.mpr hab) hab
























theorem sth_sharpThreshold (A : Set (ConfigSpace E)) (hA : IsIncreasing A) {q M : ℝ}
    (hq : (1 : ℝ) / 2 ≤ q)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e) :
    1 / 2 + M * (q - 1 / 2) ≤ prob q A := by
  have hge : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ deriv (fun p => prob p A) p := by
    intro p hp
    rw [deriv_eq_total_influence p A hA]
    exact hinfl p hp
  have hgrow : M * (q - 1 / 2) ≤ prob q A - prob (1 / 2) A :=
    sth_prob_sub_ge_of_deriv_ge A hq hge
  rw [hhalf] at hgrow
  linarith








theorem sth_sharpThreshold_eq_one (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q M : ℝ} (hq : (1 : ℝ) / 2 ≤ q) (hq1 : q ≤ 1)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e)
    (hsat : 1 ≤ 1 / 2 + M * (q - 1 / 2)) :
    prob q A = 1 := by
  have hq0 : (0 : ℝ) ≤ q := le_trans (by norm_num) hq
  have hlb : 1 / 2 + M * (q - 1 / 2) ≤ prob q A :=
    sth_sharpThreshold A hA hq hhalf hinfl
  have hub : prob q A ≤ 1 := sth_prob_le_one A hq0 hq1
  linarith


















theorem sth_sharpThreshold_window (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q M ε : ℝ} (hM : 0 < M) (hq : (1 : ℝ) / 2 ≤ q)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (hinfl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, influence p A e)
    (hnotyet : prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / M := by
  have hlb : 1 / 2 + M * (q - 1 / 2) ≤ prob q A :=
    sth_sharpThreshold A hA hq hhalf hinfl
  have hkey : M * (q - 1 / 2) ≤ 1 / 2 - ε := by linarith
  rw [le_div_iff₀ hM]
  linarith [hkey]








theorem sth_sharpThreshold_pivotal (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q M : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (hpiv : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), M ≤ ∑ e, pivotalProb p A e) :
    1 / 2 + M * (q - 1 / 2) ≤ prob q A :=
  sth_sharpThreshold A hA hq hhalf hpiv

end TwoDim

end StatMech
