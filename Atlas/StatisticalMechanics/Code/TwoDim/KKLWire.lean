/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.TwoDim.KestenThresholdRoute
import Code.Probability.RhoOptimiseClose2

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC
  StatMech.Probability StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]









omit [DecidableEq E] in


theorem kklw_weight_eq (p : ℝ) (ω : ConfigSpace E) :
    OSSS.weight (OSSS.bernoulliWeight p) ω = StatMech.configWeight p ω := by
  unfold OSSS.weight OSSS.bernoulliWeight StatMech.configWeight StatMech.edgeWeight
  rfl



theorem kklw_prob_eq_expect (p : ℝ) (A : Set (ConfigSpace E)) :
    StatMech.prob p A
      = OSSS.expect (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
  unfold StatMech.prob OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [kklw_weight_eq]; ring




theorem kklw_influence_eq_infl (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    StatMech.BeffaraDC.influence p A e
      = OSSS.infl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) e := by
  unfold StatMech.BeffaraDC.influence StatMech.pivotalProb
  rw [OSSS.infl_indicator_eq_pivotal]
  unfold OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [kklw_weight_eq]; ring



theorem kklw_sum_influence_eq_totalInfl (p : ℝ) (A : Set (ConfigSpace E)) :
    ∑ e, StatMech.BeffaraDC.influence p A e
      = totalInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))) := by
  unfold totalInfl
  exact Finset.sum_congr rfl (fun e _ => kklw_influence_eq_infl p A e)

omit [Fintype E] [DecidableEq E] in


theorem kklw_decide_eq_indicator (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    (fun ω => if (decide (ω ∈ A)) then (1:ℝ) else 0) = A.indicator (fun _ => (1:ℝ)) := by
  funext ω; rw [Set.indicator_apply]; by_cases h : ω ∈ A <;> simp [h]





theorem kklw_var_eq (p : ℝ) (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    OSSS.var (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ)))
      = StatMech.prob p A * (1 - StatMech.prob p A) := by
  rw [← kklw_decide_eq_indicator A, kkl_var_indicator_eq]
  rw [kklw_decide_eq_indicator A, ← kklw_prob_eq_expect]











noncomputable def kklw_logMaxInfl [Nonempty E] (p : ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))))









theorem kklw_hkkl_of_hypercontractive {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {p : ℝ}
    (H : KKLHypercontractive p 2) (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A
      ≤ ∑ e, StatMech.BeffaraDC.influence p A e := by
  
  have hH := H (E := E) (fun ω => decide (ω ∈ A))
  
  rw [kklw_decide_eq_indicator A] at hH
  
  
  rw [kklw_var_eq, ← kklw_logMaxInfl] at hH
  rw [kklw_sum_influence_eq_totalInfl]
  exact hH









theorem kklw_hkkl_half {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] :
    2 * (StatMech.prob (1/2) A * (1 - StatMech.prob (1/2) A)) * kklw_logMaxInfl (1/2) A
      ≤ ∑ e, StatMech.BeffaraDC.influence (1/2) A e :=
  kklw_hkkl_of_hypercontractive
    (StatMech.Probability.bph_KKL StatMech.Probability.cro2_rhoOptimise) A


















theorem kklw_hkkl {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] {q : ℝ}
    (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2) :
    ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q),
      2 * (StatMech.prob p A * (1 - StatMech.prob p A)) * kklw_logMaxInfl p A
        ≤ ∑ e, StatMech.BeffaraDC.influence p A e :=
  fun p hp => kklw_hkkl_of_hypercontractive (Hbkkkl p hp) A
























theorem kklw_sharpThreshold {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A :=
  ktr_sharpThreshold_via_kkl A hA hq (by norm_num) hv0 hL hhalf
    (kklw_logMaxInfl · A) (kklw_hkkl A Hbkkkl) hvar hLL'










theorem kklw_sharpThreshold_window {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) [DecidablePred (· ∈ A)] (hA : IsIncreasing A)
    {q v₀ L ε : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hM : 0 < 2 * v₀ * L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (Hbkkkl : ∀ p ∈ interior (Set.Icc (1/2 : ℝ) q), KKLHypercontractive p 2)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ kklw_logMaxInfl p A)
    (hnotyet : StatMech.prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) :=
  ktr_sharpThreshold_window_via_kkl A hA hq hM hhalf (by norm_num) hv0 hL
    (kklw_logMaxInfl · A) (kklw_hkkl A Hbkkkl) hvar hLL' hnotyet

end TwoDim

end StatMech
