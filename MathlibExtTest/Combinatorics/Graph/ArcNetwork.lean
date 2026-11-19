/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.ArcNetwork
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExtTest.Combinatorics.Graph.ArcNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

def t8 : Fin 8 → Fin 3 := ![0, 0, 1, 1, 0, 1, 2, 2]
def h8 : Fin 8 → Fin 3 := ![1, 1, 0, 2, 2, 1, 1, 0]
def u8 : Fin 8 → ℝ := ![2, 3, 1, 4, 1, 2, 0, 0]
def fstar : Fin 8 → ℝ := ![2, 3, 1, 4, 1, 2, 0, 0]
def fpart : Fin 8 → ℝ := ![1, 2, 1, 2, 1, 1, 0, 0]
def Fpart : Fin 3 → Fin 3 → ℝ := ![![0, 3, 1], ![1, 1, 2], ![0, 0, 0]]
def cost8 : Fin 8 → ℝ := ![1, 10, 0, 0, 0, 0, 0, 0]
def fa : Fin 8 → ℝ := ![1, 0, 0, 0, 0, 0, 0, 0]
def fb : Fin 8 → ℝ := ![0, 1, 0, 0, 0, 0, 0, 0]

private theorem cls00 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 0 ∧ h8 e = 0) = ∅ := by
  decide
private theorem cls01 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 0 ∧ h8 e = 1) = {0, 1} := by
  decide
private theorem cls02 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 0 ∧ h8 e = 2) = {4} := by
  decide
private theorem cls10 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 1 ∧ h8 e = 0) = {2} := by
  decide
private theorem cls11 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 1 ∧ h8 e = 1) = {5} := by
  decide
private theorem cls12 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 1 ∧ h8 e = 2) = {3} := by
  decide
private theorem cls20 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 2 ∧ h8 e = 0) = {7} := by
  decide
private theorem cls21 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 2 ∧ h8 e = 1) = {6} := by
  decide
private theorem cls22 : (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e = 2 ∧ h8 e = 2) = ∅ := by
  decide
private theorem head0 : (Finset.univ : Finset (Fin 8)).filter (fun e : Fin 8 => h8 e = 0) = {2, 7} := by
  decide
private theorem tail0 : (Finset.univ : Finset (Fin 8)).filter (fun e : Fin 8 => t8 e = 0) = {0, 1, 4} := by
  decide
private theorem head1 : (Finset.univ : Finset (Fin 8)).filter (fun e : Fin 8 => h8 e = 1) = {0, 1, 5, 6} := by
  decide
private theorem tail1 : (Finset.univ : Finset (Fin 8)).filter (fun e : Fin 8 => t8 e = 1) = {2, 3, 5} := by
  decide
private theorem cut01 : (Finset.univ : Finset (Fin 8)).filter
    (fun e : Fin 8 => t8 e ∈ ({0, 1} : Finset (Fin 3)) ∧ h8 e ∉ ({0, 1} : Finset (Fin 3))) = {3, 4} := by
  decide

theorem agg_cap_00 : aggregate t8 h8 u8 0 0 = 0 := by
  simp only [aggregate, cls00, Finset.sum_empty]
theorem agg_cap_01 : aggregate t8 h8 u8 0 1 = 5 := by
  simp only [aggregate, cls01]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  show (2 : ℝ) + 3 = 5
  norm_num
theorem agg_cap_02 : aggregate t8 h8 u8 0 2 = 1 := by
  simp only [aggregate, cls02]
  rw [Finset.sum_singleton]
  show (1 : ℝ) = 1
  norm_num
theorem agg_cap_10 : aggregate t8 h8 u8 1 0 = 1 := by
  simp only [aggregate, cls10]
  rw [Finset.sum_singleton]
  show (1 : ℝ) = 1
  norm_num
theorem agg_cap_11 : aggregate t8 h8 u8 1 1 = 2 := by
  simp only [aggregate, cls11]
  rw [Finset.sum_singleton]
  show (2 : ℝ) = 2
  norm_num
theorem agg_cap_12 : aggregate t8 h8 u8 1 2 = 4 := by
  simp only [aggregate, cls12]
  rw [Finset.sum_singleton]
  show (4 : ℝ) = 4
  norm_num
theorem agg_cap_20 : aggregate t8 h8 u8 2 0 = 0 := by
  simp only [aggregate, cls20]
  rw [Finset.sum_singleton]
  show (0 : ℝ) = 0
  norm_num
theorem agg_cap_21 : aggregate t8 h8 u8 2 1 = 0 := by
  simp only [aggregate, cls21]
  rw [Finset.sum_singleton]
  show (0 : ℝ) = 0
  norm_num
theorem agg_cap_22 : aggregate t8 h8 u8 2 2 = 0 := by
  simp only [aggregate, cls22, Finset.sum_empty]
theorem agg_flow_01 : aggregate t8 h8 fpart 0 1 = 3 := by
  simp only [aggregate, cls01]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  show (1 : ℝ) + 2 = 3
  norm_num
theorem agg_flow_11 : aggregate t8 h8 fpart 1 1 = 1 := by
  simp only [aggregate, cls11]
  rw [Finset.sum_singleton]
  show (1 : ℝ) = 1
  norm_num
theorem agg_flow_02 : aggregate t8 h8 fpart 0 2 = 1 := by
  simp only [aggregate, cls02]
  rw [Finset.sum_singleton]
  show (1 : ℝ) = 1
  norm_num
theorem parallel_vs_antiparallel : aggregate t8 h8 u8 0 1 ≠ aggregate t8 h8 u8 1 0 := by
  rw [agg_cap_01, agg_cap_10]
  norm_num
theorem cap_nonneg : ∀ e, 0 ≤ u8 e := by
  intro e
  fin_cases e <;> norm_num [u8]
theorem fstar_nonneg : ∀ e, 0 ≤ fstar e := by
  intro e
  fin_cases e <;> norm_num [fstar]
theorem fstar_cap : ∀ e, fstar e ≤ u8 e := by
  intro e
  fin_cases e <;> norm_num [fstar, u8]
theorem fpart_nonneg : ∀ e, 0 ≤ fpart e := by
  intro e
  fin_cases e <;> norm_num [fpart]
theorem fpart_cap : ∀ e, fpart e ≤ u8 e := by
  intro e
  fin_cases e <;> norm_num [fpart, u8]
theorem loop_column_vanishes : ∀ v, incidenceMatrix t8 h8 v 5 = 0 := by
  intro v
  exact incidence_loop_eq_zero t8 h8 5 (by decide) v
theorem loop_carries_flow : fstar 5 = 2 ∧ 0 < fstar 5 := by
  constructor
  · rfl
  · show (0 : ℝ) < 2
    norm_num
theorem zero_caps_zero_flow : fstar 6 = 0 ∧ fstar 7 = 0 := ⟨rfl, rfl⟩
theorem fstar_feasible : IsArcFeasible t8 h8 u8 0 2 fstar := by
  refine ⟨fstar_nonneg, fstar_cap, ?_⟩
  intro v hv0 hv2
  fin_cases v
  · simp_all
  · show (incidenceMatrix t8 h8).mulVec fstar 1 = 0
    rw [incidence_mulVec, head1, tail1,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    show ((2 : ℝ) + (3 + (2 + 0))) - (1 + (4 + 2)) = 0
    norm_num
  · simp_all
theorem fstar_value : -((incidenceMatrix t8 h8).mulVec fstar 0) = 5 := by
  rw [incidence_mulVec, head0, tail0,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  show -(((1 : ℝ) + 0) - (2 + (3 + 1))) = 5
  norm_num
theorem sstar_is_cut : IsSTCut 0 2 ({0, 1} : Finset (Fin 3)) := ⟨by decide, by decide⟩
theorem cut_arcsum_eq : (∑ e ∈ (Finset.univ : Finset (Fin 8)).filter
    (fun e : Fin 8 => t8 e ∈ ({0, 1} : Finset (Fin 3)) ∧ h8 e ∉ ({0, 1} : Finset (Fin 3))),
    u8 e) = 5 := by
  rw [cut01, Finset.sum_insert (by decide), Finset.sum_singleton]
  show (4 : ℝ) + 1 = 5
  norm_num
theorem every_competitor_bounded : ∀ f' : Fin 8 → ℝ,
    IsArcFeasible t8 h8 u8 0 2 f' → -((incidenceMatrix t8 h8).mulVec f' 0) ≤ 5 := by
  intro f' hf'
  have hagg := isFeasibleFlow_aggregate t8 h8 u8 f' 0 2 hf'
  have hle := flowValue_le_cutCapacity (aggregate t8 h8 u8) 0 2 (aggregate t8 h8 f') hagg
    ({0, 1} : Finset (Fin 3)) sstar_is_cut
  have hval := flowValue_aggregate_eq_neg_mulVec t8 h8 f' 0
  have hcut := cutCapacity_aggregate_eq_sum_leaving t8 h8 u8 ({0, 1} : Finset (Fin 3))
  rw [cut_arcsum_eq] at hcut
  rw [hcut] at hle
  rw [← hval]
  exact hle
theorem c6_applies : ∃ f : Fin 8 → ℝ, IsArcFeasible t8 h8 u8 0 2 f ∧
    (∀ f' : Fin 8 → ℝ, IsArcFeasible t8 h8 u8 0 2 f' →
      -((incidenceMatrix t8 h8).mulVec f' 0) ≤ -((incidenceMatrix t8 h8).mulVec f 0)) ∧
    (∀ S : Finset (Fin 3), IsSTCut 0 2 S →
      -((incidenceMatrix t8 h8).mulVec f 0) ≤
        ∑ e ∈ (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e ∈ S ∧ h8 e ∉ S), u8 e) ∧
    (∃ S : Finset (Fin 3), IsSTCut 0 2 S ∧
      -((incidenceMatrix t8 h8).mulVec f 0) =
        ∑ e ∈ (Finset.univ : Finset (Fin 8)).filter (fun e => t8 e ∈ S ∧ h8 e ∉ S), u8 e) :=
  arc_max_flow_min_cut t8 h8 u8 cap_nonneg 0 2 (by decide)
theorem dense_flow_nonneg : ∀ p q, 0 ≤ Fpart p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> norm_num [Fpart]
theorem dense_flow_cap : ∀ p q, Fpart p q ≤ aggregate t8 h8 u8 p q := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, cls00, cls01, cls02, cls10, cls11, cls12, cls20, cls21, cls22,
      Fpart, u8, Finset.sum_empty, Finset.sum_insert, Finset.sum_singleton];
  norm_num
theorem dense_flow_cons : ∀ v, v ≠ 0 → v ≠ 2 → (∑ u, Fpart u v) = ∑ w, Fpart v w := by
  intro v hv0 hv2
  fin_cases v
  · simp_all
  · simp only [Fin.sum_univ_three]
    norm_num [Fpart]
  · simp_all
theorem dense_flow_feasible : IsFeasibleFlow (aggregate t8 h8 u8) 0 2 Fpart :=
  ⟨dense_flow_nonneg, dense_flow_cap, dense_flow_cons⟩
theorem lift_val_0 : proportionalLift t8 h8 u8 Fpart 0 = 6 / 5 := by
  have ht : t8 0 = (0 : Fin 3) := rfl
  have hh : h8 0 = (1 : Fin 3) := rfl
  have e01 : Fpart 0 1 = (3 : ℝ) := by simp [Fpart]
  have ue0 : u8 0 = (2 : ℝ) := rfl
  have hT : aggregate t8 h8 u8 (t8 0) (h8 0) ≠ 0 := by
    rw [ht, hh, agg_cap_01]
    norm_num
  rw [proportionalLift_nonzero t8 h8 u8 Fpart 0 hT, ht, hh, agg_cap_01, e01, ue0]
  norm_num
theorem lift_val_1 : proportionalLift t8 h8 u8 Fpart 1 = 9 / 5 := by
  have ht : t8 1 = (0 : Fin 3) := rfl
  have hh : h8 1 = (1 : Fin 3) := rfl
  have e01 : Fpart 0 1 = (3 : ℝ) := by simp [Fpart]
  have ue1 : u8 1 = (3 : ℝ) := rfl
  have hT : aggregate t8 h8 u8 (t8 1) (h8 1) ≠ 0 := by
    rw [ht, hh, agg_cap_01]
    norm_num
  rw [proportionalLift_nonzero t8 h8 u8 Fpart 1 hT, ht, hh, agg_cap_01, e01, ue1]
  norm_num
theorem lift_val_zero_class : proportionalLift t8 h8 u8 Fpart 6 = 0 := by
  apply proportionalLift_zero
  have ht : t8 6 = (2 : Fin 3) := rfl
  have hh : h8 6 = (1 : Fin 3) := rfl
  rw [ht, hh]
  exact agg_cap_21
theorem lift_aggregates_back : ∀ p q,
    aggregate t8 h8 (proportionalLift t8 h8 u8 Fpart) p q = Fpart p q :=
  fun p q => aggregate_proportionalLift t8 h8 u8 cap_nonneg Fpart 0 2 dense_flow_feasible p q
theorem dense_value_pin : flowValue 0 Fpart = 3 := by
  show ((∑ v : Fin 3, Fpart 0 v) - ∑ u : Fin 3, Fpart u 0) = 3
  simp only [Fin.sum_univ_three]
  norm_num [Fpart]
theorem lift_value_eq :
    -((incidenceMatrix t8 h8).mulVec (proportionalLift t8 h8 u8 Fpart) 0) = 3 := by
  have h := flowValue_proportionalLift t8 h8 u8 cap_nonneg Fpart 0 2 dense_flow_feasible
  rw [h]
  exact dense_value_pin
theorem priced_same_aggregate : aggregate t8 h8 fa = aggregate t8 h8 fb := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, cls00, cls01, cls02, cls10, cls11, cls12, cls20, cls21, cls22,
      fa, fb, Finset.sum_empty, Finset.sum_insert, Finset.sum_singleton]
theorem priced_cost_a : (∑ e, cost8 e * fa e) = 1 := by
  simp only [Fin.sum_univ_eight]
  norm_num [cost8, fa]
theorem priced_cost_b : (∑ e, cost8 e * fb e) = 10 := by
  simp only [Fin.sum_univ_eight]
  norm_num [cost8, fb]
theorem priced_costs_differ : (∑ e, cost8 e * fa e) ≠ ∑ e, cost8 e * fb e := by
  rw [priced_cost_a, priced_cost_b]
  norm_num
theorem signed_parallel_loop_total_zero :
    ∑ v, (incidenceMatrix t8 h8).mulVec
      (![2, 3, -4, 0, 0, 9, 0, 0] : Fin 8 → ℝ) v = 0 :=
  sum_incidenceMatrix_mulVec_eq_zero t8 h8 ![2, 3, -4, 0, 0, 9, 0, 0]
theorem stock_balance_signed_parallel_loop :
    ∑ v, ((![1, -2, 5] : Fin 3 → ℝ) +
        (incidenceMatrix t8 h8).mulVec (![2, 3, -4, 0, 0, 9, 0, 0] : Fin 8 → ℝ) +
        (![1 / 2, 0, 3] : Fin 3 → ℝ) - (![0, 7, 1 / 3] : Fin 3 → ℝ)) v = 1 / 6 := by
  have h := stock_level_arc_balance t8 h8 ![2, 3, -4, 0, 0, 9, 0, 0]
    (m := ![1, -2, 5]) (s := ![1 / 2, 0, 3]) (r := ![0, 7, 1 / 3]) rfl
  have hsum : (∑ v, (![1, -2, 5] : Fin 3 → ℝ) v) +
      (∑ v, (![1 / 2, 0, 3] : Fin 3 → ℝ) v)
      - (∑ v, (![0, 7, 1 / 3] : Fin 3 → ℝ) v) = 1 / 6 := by
    norm_num [Fin.sum_univ_three]
  exact h.trans hsum
theorem stock_balance_one_way :
    ∑ v, ((![10, 20] : Fin 2 → ℝ) +
        (incidenceMatrix (![0] : Fin 1 → Fin 2) (![1] : Fin 1 → Fin 2)).mulVec
          (![5] : Fin 1 → ℝ) +
        (![1, 2] : Fin 2 → ℝ) - (![3, 4] : Fin 2 → ℝ)) v = 26 := by
  have h := stock_level_arc_balance (![0] : Fin 1 → Fin 2) (![1] : Fin 1 → Fin 2) ![5]
    (m := ![10, 20]) (s := ![1, 2]) (r := ![3, 4]) rfl
  have hsum : (∑ v, (![10, 20] : Fin 2 → ℝ) v) +
      (∑ v, (![1, 2] : Fin 2 → ℝ) v)
      - (∑ v, (![3, 4] : Fin 2 → ℝ) v) = 26 := by
    norm_num [Fin.sum_univ_two]
  exact h.trans hsum

def e0tail : Fin 0 → Fin 2 := fun e => e.elim0
def e0head : Fin 0 → Fin 2 := fun e => e.elim0
def e0flow : Fin 0 → ℝ := fun e => e.elim0
def e0cap : Fin 0 → ℝ := fun e => e.elim0

theorem empty_aggregate : ∀ p q, aggregate e0tail e0head e0cap p q = 0 := by
  intro p q
  simp [aggregate]
theorem empty_mulVec : ∀ v, (incidenceMatrix e0tail e0head).mulVec e0flow v = 0 := by
  intro v
  rw [incidence_mulVec]
  simp
theorem empty_feasible : IsArcFeasible e0tail e0head e0cap 0 1 e0flow :=
  ⟨fun e => e.elim0, fun e => e.elim0, fun v _ _ => empty_mulVec v⟩
theorem empty_cut_sum : ∀ S : Finset (Fin 2),
    (∑ e ∈ (Finset.univ : Finset (Fin 0)).filter (fun e => e0tail e ∈ S ∧ e0head e ∉ S),
      e0cap e) = 0 := by
  intro S
  simp
theorem empty_mfmc_value : ∃ f : Fin 0 → ℝ, IsArcFeasible e0tail e0head e0cap 0 1 f ∧
    -((incidenceMatrix e0tail e0head).mulVec f 0) = 0 := by
  refine ⟨e0flow, empty_feasible, ?_⟩
  simp [empty_mulVec]
theorem empty_all_zero_value : ∀ f : Fin 0 → ℝ,
    -((incidenceMatrix e0tail e0head).mulVec f 0) = 0 := by
  intro f
  have h : (incidenceMatrix e0tail e0head).mulVec f 0 = 0 := by
    rw [incidence_mulVec]
    simp
  rw [h]
  norm_num

end MathlibExtTest.Combinatorics.Graph.ArcNetwork
