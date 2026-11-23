/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ArcNetworkIntegral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral arc network tests

Concrete checks for the integral class split, the integral arc lift, and the
integral arc max-flow min-cut theorem on small `Fin` networks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.Graph.ArcNetworkIntegral

open MathlibExt.Combinatorics.Graph.ArcNetwork
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-! Parallel class with a non-integral proportional lift -/

private def pt : Fin 2 → Fin 2 := ![0, 0]
private def ph : Fin 2 → Fin 2 := ![1, 1]
private def pu : Fin 2 → ℕ := ![1, 1]
private def pF : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![0, 0]]
private def puc : Fin 2 → ℝ := fun e => (pu e : ℝ)
private def pFc : Fin 2 → Fin 2 → ℝ := fun p q => (pF p q : ℝ)
private def pg0 : Fin 2 → ℕ := ![1, 0]

private theorem pcls00 : (Finset.univ : Finset (Fin 2)).filter (fun e => pt e = 0 ∧ ph e = 0) = ∅ := by
  decide
private theorem pcls01 : (Finset.univ : Finset (Fin 2)).filter (fun e => pt e = 0 ∧ ph e = 1) = {0, 1} := by
  decide
private theorem pcls10 : (Finset.univ : Finset (Fin 2)).filter (fun e => pt e = 1 ∧ ph e = 0) = ∅ := by
  decide
private theorem pcls11 : (Finset.univ : Finset (Fin 2)).filter (fun e => pt e = 1 ∧ ph e = 1) = ∅ := by
  decide

theorem parallel_agg_cap_two : aggregate pt ph puc 0 1 = 2 := by
  simp only [aggregate, pcls01]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  show ((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) = (2 : ℝ)
  norm_num

theorem parallel_lift_fst_half : proportionalLift pt ph puc pFc 0 = 1 / 2 := by
  have ht : pt 0 = (0 : Fin 2) := rfl
  have hh : ph 0 = (1 : Fin 2) := rfl
  have e01 : pFc 0 1 = (1 : ℝ) := by simp [pFc, pF]
  have ue0 : puc 0 = (1 : ℝ) := by simp [puc, pu]
  have hT : aggregate pt ph puc (pt 0) (ph 0) ≠ 0 := by
    rw [ht, hh, parallel_agg_cap_two]
    norm_num
  rw [proportionalLift_nonzero pt ph puc pFc 0 hT, ht, hh, parallel_agg_cap_two, e01, ue0]
  norm_num

theorem parallel_lift_snd_half : proportionalLift pt ph puc pFc 1 = 1 / 2 := by
  have ht : pt 1 = (0 : Fin 2) := rfl
  have hh : ph 1 = (1 : Fin 2) := rfl
  have e01 : pFc 0 1 = (1 : ℝ) := by simp [pFc, pF]
  have ue1 : puc 1 = (1 : ℝ) := by simp [puc, pu]
  have hT : aggregate pt ph puc (pt 1) (ph 1) ≠ 0 := by
    rw [ht, hh, parallel_agg_cap_two]
    norm_num
  rw [proportionalLift_nonzero pt ph puc pFc 1 hT, ht, hh, parallel_agg_cap_two, e01, ue1]
  norm_num

theorem parallel_split_bound : ∀ p q, (pF p q : ℝ) ≤ aggregate pt ph puc p q := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, pcls00, pcls01, pcls10, pcls11, pF, pu, puc,
      Finset.sum_empty, Finset.sum_insert, Finset.sum_singleton]

theorem parallel_nat_split_exists :
    ∃ g : Fin 2 → ℕ, (∀ e, g e ≤ pu e) ∧
      aggregate pt ph (fun e => (g e : ℝ)) = fun p q => (pF p q : ℝ) :=
  exists_nat_split pt ph pu pF parallel_split_bound

theorem parallel_witness_le : ∀ e, pg0 e ≤ pu e := by
  intro e
  fin_cases e <;> norm_num [pg0, pu]

theorem parallel_witness_exact :
    aggregate pt ph (fun e => ((pg0 e : ℕ) : ℝ)) = fun p q => (pF p q : ℝ) := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, pcls00, pcls01, pcls10, pcls11, pg0, pF,
      Finset.sum_empty, Finset.sum_insert, Finset.sum_singleton]

/-! Antiparallel pair with both directions positive -/

private def apt : Fin 2 → Fin 2 := ![0, 1]
private def aph : Fin 2 → Fin 2 := ![1, 0]
private def au : Fin 2 → ℕ := ![2, 3]
private def aF : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![2, 0]]
private def auc : Fin 2 → ℝ := fun e => (au e : ℝ)
private def aFc : Fin 2 → Fin 2 → ℝ := fun p q => (aF p q : ℝ)

private theorem acls00 : (Finset.univ : Finset (Fin 2)).filter (fun e => apt e = 0 ∧ aph e = 0) = ∅ := by
  decide
private theorem acls01 : (Finset.univ : Finset (Fin 2)).filter (fun e => apt e = 0 ∧ aph e = 1) = {0} := by
  decide
private theorem acls10 : (Finset.univ : Finset (Fin 2)).filter (fun e => apt e = 1 ∧ aph e = 0) = {1} := by
  decide
private theorem acls11 : (Finset.univ : Finset (Fin 2)).filter (fun e => apt e = 1 ∧ aph e = 1) = ∅ := by
  decide

theorem antiparallel_dense_nonneg : ∀ p q, 0 ≤ (aF p q : ℝ) := by
  intro p q
  fin_cases p <;> fin_cases q <;> norm_num [aF]

theorem antiparallel_dense_cap : ∀ p q, (aF p q : ℝ) ≤ aggregate apt aph auc p q := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, acls00, acls01, acls10, acls11, aF, au, auc,
      Finset.sum_empty, Finset.sum_singleton]
  norm_num

theorem antiparallel_dense_cons :
    ∀ v, v ≠ 0 → v ≠ 1 → (∑ u, aFc u v) = ∑ w, aFc v w := by
  intro v hvs hvt
  fin_cases v <;> simp_all

theorem antiparallel_dense_feasible : IsFeasibleFlow (aggregate apt aph auc) 0 1 aFc :=
  ⟨antiparallel_dense_nonneg, antiparallel_dense_cap, antiparallel_dense_cons⟩

theorem antiparallel_dense_value : flowValue 0 aFc = -1 := by
  show ((∑ v : Fin 2, aFc 0 v) - ∑ u : Fin 2, aFc u 0) = -1
  simp only [Fin.sum_univ_two]
  norm_num [aFc, aF]

theorem antiparallel_integral_lift :
    ∃ g : Fin 2 → ℕ,
      IsArcFeasible apt aph auc 0 1 (fun e => (g e : ℝ)) ∧
      aggregate apt aph (fun e => (g e : ℝ)) = (fun p q => (aF p q : ℝ)) ∧
      -((incidenceMatrix apt aph).mulVec (fun e => (g e : ℝ)) 0) = -1 := by
  obtain ⟨g, hfeas, hagg, hval⟩ :=
    exists_nat_arc_lift apt aph au 0 1 aF antiparallel_dense_feasible
  refine ⟨g, hfeas, hagg, ?_⟩
  rw [hval]
  exact antiparallel_dense_value

/-! Loop carrying positive flow -/

private def lt : Fin 1 → Fin 2 := ![0]
private def lh : Fin 1 → Fin 2 := ![0]
private def lu : Fin 1 → ℕ := ![5]
private def lg : Fin 1 → ℕ := ![3]
private def lgc : Fin 1 → ℝ := fun e => (lg e : ℝ)

private theorem loop_head0 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => lh e = 0) = {0} := by
  decide
private theorem loop_tail0 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => lt e = 0) = {0} := by
  decide
private theorem loop_head1 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => lh e = 1) = ∅ := by
  decide
private theorem loop_tail1 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => lt e = 1) = ∅ := by
  decide

theorem loop_column_zero : ∀ v, incidenceMatrix lt lh v 0 = 0 := by
  intro v
  exact incidence_loop_eq_zero lt lh 0 (by decide) v

theorem loop_flow_positive : 0 < lg 0 := by
  decide

theorem loop_balance_zero : ∀ v, (incidenceMatrix lt lh).mulVec lgc v = 0 := by
  intro v
  fin_cases v
  · show (incidenceMatrix lt lh).mulVec lgc 0 = 0
    rw [incidence_mulVec, loop_head0, loop_tail0,
      Finset.sum_singleton]
    simp
  · show (incidenceMatrix lt lh).mulVec lgc 1 = 0
    rw [incidence_mulVec, loop_head1, loop_tail1,
      Finset.sum_empty]
    simp

theorem loop_source_value_zero : -((incidenceMatrix lt lh).mulVec lgc 0) = 0 := by
  rw [loop_balance_zero]
  norm_num

/-! Zero-capacity class forces zero flow -/

private def zt : Fin 1 → Fin 2 := ![0]
private def zh : Fin 1 → Fin 2 := ![1]
private def zu : Fin 1 → ℕ := ![0]
private def zuc : Fin 1 → ℝ := fun e => (zu e : ℝ)

private theorem zcls01 : (Finset.univ : Finset (Fin 1)).filter (fun e => zt e = 0 ∧ zh e = 1) = {0} := by
  decide

theorem zero_class_agg_zero : aggregate zt zh zuc 0 1 = 0 := by
  simp [aggregate, zu, zuc]

theorem zero_class_forces_zero : ∀ F : Fin 2 → Fin 2 → ℕ,
    (F 0 1 : ℝ) ≤ aggregate zt zh zuc 0 1 → F 0 1 = 0 := by
  intro F h
  rw [zero_class_agg_zero] at h
  have h0 : (F 0 1 : ℝ) ≤ ((0 : ℕ) : ℝ) := by simpa using h
  have hle : F 0 1 ≤ 0 := Nat.cast_le.mp h0
  omega

/-! Empty arc type -/

private def etail : Fin 0 → Fin 2 := fun e => e.elim0
private def ehead : Fin 0 → Fin 2 := fun e => e.elim0
private def ecap : Fin 0 → ℕ := fun e => e.elim0
private def eF : Fin 2 → Fin 2 → ℕ := fun _ _ => 0
private def ecapc : Fin 0 → ℝ := fun e => (ecap e : ℝ)
private def eFc : Fin 2 → Fin 2 → ℝ := fun p q => (eF p q : ℝ)

theorem empty_agg_zero : ∀ p q, aggregate etail ehead ecapc p q = 0 := by
  intro p q
  simp [aggregate]

theorem empty_mulVec_zero : ∀ (f : Fin 0 → ℝ) (v : Fin 2),
    (incidenceMatrix etail ehead).mulVec f v = 0 := by
  intro f v
  rw [incidence_mulVec]
  simp

theorem empty_arc_feasible :
    IsArcFeasible etail ehead ecapc 0 1 (fun e => ((ecap e : ℕ) : ℝ)) :=
  ⟨fun e => e.elim0, fun e => e.elim0, fun v _ _ => empty_mulVec_zero _ v⟩

theorem empty_split_bound : ∀ p q, (eF p q : ℝ) ≤ aggregate etail ehead ecapc p q := by
  intro p q
  rw [empty_agg_zero]
  simp [eF]

theorem empty_split_applies :
    ∃ g : Fin 0 → ℕ, (∀ e, g e ≤ ecap e) ∧
      aggregate etail ehead (fun e => (g e : ℝ)) = fun p q => (eF p q : ℝ) :=
  exists_nat_split etail ehead ecap eF empty_split_bound

theorem empty_dense_feasible : IsFeasibleFlow (aggregate etail ehead ecapc) 0 1 eFc :=
  ⟨fun p q => by simp [eFc, eF], fun p q => by simp [eFc, eF, empty_agg_zero],
    fun v _ _ => by simp [eFc, eF]⟩

theorem empty_dense_value_zero : flowValue 0 eFc = 0 := by
  simp [flowValue, eFc, eF]

theorem empty_lift_value_zero :
    ∃ g : Fin 0 → ℕ,
      IsArcFeasible etail ehead ecapc 0 1 (fun e => (g e : ℝ)) ∧
      -((incidenceMatrix etail ehead).mulVec (fun e => (g e : ℝ)) 0) = 0 := by
  obtain ⟨g, hfeas, -, hval⟩ :=
    exists_nat_arc_lift etail ehead ecap 0 1 eF empty_dense_feasible
  refine ⟨g, ?_, ?_⟩
  · exact hfeas
  · rw [hval]
    exact empty_dense_value_zero

/-! Concrete integral maximum flow of value three -/

private def mt : Fin 3 → Fin 3 := ![0, 1, 0]
private def mh : Fin 3 → Fin 3 := ![1, 2, 2]
private def mu : Fin 3 → ℕ := ![2, 2, 1]
private def muc : Fin 3 → ℝ := fun e => (mu e : ℝ)
private def mf : Fin 3 → ℝ := ![2, 2, 1]

private theorem mhead0 : (Finset.univ : Finset (Fin 3)).filter (fun e : Fin 3 => mh e = 0) = ∅ := by
  decide
private theorem mtail0 : (Finset.univ : Finset (Fin 3)).filter (fun e : Fin 3 => mt e = 0) = {0, 2} := by
  decide
private theorem mhead1 : (Finset.univ : Finset (Fin 3)).filter (fun e : Fin 3 => mh e = 1) = {0} := by
  decide
private theorem mtail1 : (Finset.univ : Finset (Fin 3)).filter (fun e : Fin 3 => mt e = 1) = {1} := by
  decide
private theorem mcut0 : (Finset.univ : Finset (Fin 3)).filter
    (fun e : Fin 3 => mt e ∈ ({0} : Finset (Fin 3)) ∧ mh e ∉ ({0} : Finset (Fin 3))) = {0, 2} := by
  decide

theorem maxflow_flow_nonneg : ∀ e, 0 ≤ mf e := by
  intro e
  fin_cases e <;> norm_num [mf]

theorem maxflow_flow_cap : ∀ e, mf e ≤ muc e := by
  intro e
  fin_cases e <;> norm_num [mf, muc, mu]

theorem maxflow_flow_cons : ∀ v, v ≠ 0 → v ≠ 2 →
    (incidenceMatrix mt mh).mulVec mf v = 0 := by
  intro v hvs hvt
  fin_cases v
  · simp_all
  · show (incidenceMatrix mt mh).mulVec mf 1 = 0
    rw [incidence_mulVec, mhead1, mtail1,
      Finset.sum_singleton, Finset.sum_singleton]
    show (2 : ℝ) - 2 = 0
    norm_num
  · simp_all

theorem maxflow_feasible_three :
    IsArcFeasible mt mh muc 0 2 mf ∧ -((incidenceMatrix mt mh).mulVec mf 0) = 3 := by
  refine ⟨⟨maxflow_flow_nonneg, maxflow_flow_cap, maxflow_flow_cons⟩, ?_⟩
  rw [incidence_mulVec, mhead0, mtail0,
    Finset.sum_empty, Finset.sum_insert (by decide), Finset.sum_singleton]
  show -((0 : ℝ) - ((2 : ℝ) + 1)) = 3
  norm_num

theorem maxflow_cut_zero :
    IsSTCut 0 2 ({0} : Finset (Fin 3)) ∧
    (∑ e ∈ (Finset.univ : Finset (Fin 3)).filter
      (fun e => mt e ∈ ({0} : Finset (Fin 3)) ∧ mh e ∉ ({0} : Finset (Fin 3))),
      (mu e : ℝ)) = 3 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  rw [mcut0, Finset.sum_insert (by decide), Finset.sum_singleton]
  show ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) = (3 : ℝ)
  norm_num

theorem integral_maxflow_pinned :
    ∃ g : Fin 3 → ℕ,
      IsArcFeasible mt mh muc 0 2 (fun e => (g e : ℝ)) ∧
      (∀ f' : Fin 3 → ℝ, IsArcFeasible mt mh muc 0 2 f' →
        -((incidenceMatrix mt mh).mulVec f' 0) ≤
        -((incidenceMatrix mt mh).mulVec (fun e => (g e : ℝ)) 0)) ∧
      (∃ S : Finset (Fin 3), IsSTCut 0 2 S ∧
        -((incidenceMatrix mt mh).mulVec (fun e => (g e : ℝ)) 0) =
        ∑ e ∈ (Finset.univ : Finset (Fin 3)).filter
          (fun e => mt e ∈ S ∧ mh e ∉ S), (mu e : ℝ)) ∧
      -((incidenceMatrix mt mh).mulVec (fun e => (g e : ℝ)) 0) = 3 := by
  obtain ⟨g, hgfeas, hmax, hcutle, hcutex⟩ :=
    exists_nat_arc_max_flow_min_cut mt mh mu 0 2 (by decide)
  have hcut := hcutle {0} maxflow_cut_zero.1
  rw [maxflow_cut_zero.2] at hcut
  have hge := hmax mf maxflow_feasible_three.1
  rw [maxflow_feasible_three.2] at hge
  have hval : -((incidenceMatrix mt mh).mulVec (fun e => (g e : ℝ)) 0) = 3 :=
    le_antisymm hcut hge
  exact ⟨g, hgfeas, hmax, hcutex, hval⟩

theorem every_arc_competitor_le_three : ∀ f' : Fin 3 → ℝ,
    IsArcFeasible mt mh muc 0 2 f' → -((incidenceMatrix mt mh).mulVec f' 0) ≤ 3 := by
  intro f' hf'
  obtain ⟨g, -, hmax, -, hval⟩ := integral_maxflow_pinned
  have h := hmax f' hf'
  rw [hval] at h
  exact h

theorem some_cut_sums_to_three :
    ∃ S : Finset (Fin 3), IsSTCut 0 2 S ∧
      (∑ e ∈ (Finset.univ : Finset (Fin 3)).filter
        (fun e => mt e ∈ S ∧ mh e ∉ S), (mu e : ℝ)) = 3 := by
  obtain ⟨g, -, -, ⟨S, hS, hSeq⟩, hval⟩ := integral_maxflow_pinned
  refine ⟨S, hS, ?_⟩
  rw [← hSeq]
  exact hval

/-! Negative examples: each drops exactly one hypothesis -/

private def nt : Fin 2 → Fin 2 := ![0, 0]
private def nh : Fin 2 → Fin 2 := ![1, 1]
private noncomputable def nw : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private theorem ncls01 : (Finset.univ : Finset (Fin 2)).filter (fun e => nt e = 0 ∧ nh e = 1) = {0, 1} := by
  decide

theorem half_caps_aggregate_one : aggregate nt nh nw 0 1 = 1 := by
  simp only [aggregate, ncls01]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  show (1 / 2 : ℝ) + 1 / 2 = 1
  norm_num

theorem no_nat_split_of_half_caps :
    ¬ ∃ g : Fin 2 → ℕ, (∀ e, (g e : ℝ) ≤ nw e) ∧
      aggregate nt nh (fun e => (g e : ℝ)) 0 1 = 1 := by
  rintro ⟨g, hle, hagg⟩
  have hz0 : g 0 = 0 := by
    by_contra hne
    have h1 : 1 ≤ g 0 := by omega
    have hc : (1 : ℝ) ≤ (g 0 : ℝ) := by exact_mod_cast h1
    have hw : (g 0 : ℝ) ≤ 1 / 2 := by
      have h2 := hle 0
      norm_num [nw] at h2
      exact h2
    have hcon : (1 : ℝ) ≤ 1 / 2 := le_trans hc hw
    norm_num at hcon
  have hz1 : g 1 = 0 := by
    by_contra hne
    have h1 : 1 ≤ g 1 := by omega
    have hc : (1 : ℝ) ≤ (g 1 : ℝ) := by exact_mod_cast h1
    have hw : (g 1 : ℝ) ≤ 1 / 2 := by
      have h2 := hle 1
      norm_num [nw] at h2
      exact h2
    have hcon : (1 : ℝ) ≤ 1 / 2 := le_trans hc hw
    norm_num at hcon
  have hsum : aggregate nt nh (fun e => ((g e : ℕ) : ℝ)) 0 1 =
      ((g 0 : ℕ) : ℝ) + ((g 1 : ℕ) : ℝ) := by
    simp only [aggregate, ncls01]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hsum, hz0, hz1] at hagg
  norm_num at hagg

private def ht : Fin 1 → Fin 2 := ![0]
private def hh : Fin 1 → Fin 2 := ![1]
private def hu : Fin 1 → ℕ := ![2]
private def huc : Fin 1 → ℝ := fun e => (hu e : ℝ)
private noncomputable def hFr : Fin 2 → Fin 2 → ℝ := ![![0, 1 / 2], ![0, 0]]

private theorem hcls00 : (Finset.univ : Finset (Fin 1)).filter (fun e => ht e = 0 ∧ hh e = 0) = ∅ := by
  decide
private theorem hcls01 : (Finset.univ : Finset (Fin 1)).filter (fun e => ht e = 0 ∧ hh e = 1) = {0} := by
  decide
private theorem hcls10 : (Finset.univ : Finset (Fin 1)).filter (fun e => ht e = 1 ∧ hh e = 0) = ∅ := by
  decide
private theorem hcls11 : (Finset.univ : Finset (Fin 1)).filter (fun e => ht e = 1 ∧ hh e = 1) = ∅ := by
  decide

theorem half_dense_flow_nonneg : ∀ p q, 0 ≤ hFr p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> norm_num [hFr]

theorem half_dense_flow_cap : ∀ p q, hFr p q ≤ aggregate ht hh huc p q := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, hcls00, hcls01, hcls10, hcls11, hFr, hu, huc]
  norm_num

theorem half_dense_flow_cons :
    ∀ v, v ≠ 0 → v ≠ 1 → (∑ u, hFr u v) = ∑ w, hFr v w := by
  intro v hvs hvt
  fin_cases v <;> simp_all

theorem half_dense_flow_feasible : IsFeasibleFlow (aggregate ht hh huc) 0 1 hFr :=
  ⟨half_dense_flow_nonneg, half_dense_flow_cap, half_dense_flow_cons⟩

theorem half_dense_flow_no_nat_preimage :
    ¬ ∃ G : Fin 2 → Fin 2 → ℕ, (fun p q => ((G p q : ℕ) : ℝ)) = hFr := by
  rintro ⟨G, hG⟩
  have h01 : ((G 0 1 : ℕ) : ℝ) = hFr 0 1 := congrFun (congrFun hG 0) 1
  have hFr01 : hFr 0 1 = 1 / 2 := by simp [hFr]
  rw [hFr01] at h01
  have hcases : G 0 1 = 0 ∨ 1 ≤ G 0 1 := by omega
  rcases hcases with hz | hpos
  · rw [hz] at h01
    norm_num at h01
  · have hc : (1 : ℝ) ≤ (G 0 1 : ℝ) := by exact_mod_cast hpos
    rw [h01] at hc
    norm_num at hc

private def dt : Fin 1 → Fin 2 := ![0]
private def dh : Fin 1 → Fin 2 := ![1]
private def du : Fin 1 → ℕ := ![2]
private def dF : Fin 2 → Fin 2 → ℕ := ![![0, 5], ![0, 0]]

private theorem dcls01 : (Finset.univ : Finset (Fin 1)).filter (fun e => dt e = 0 ∧ dh e = 1) = {0} := by
  decide

theorem no_split_above_capacity :
    ¬ ∃ g : Fin 1 → ℕ, (∀ e, g e ≤ du e) ∧
      aggregate dt dh (fun e => (g e : ℝ)) = fun p q => (dF p q : ℝ) := by
  rintro ⟨g, hle, hagg⟩
  have h01 : aggregate dt dh (fun e => ((g e : ℕ) : ℝ)) 0 1 = ((dF 0 1 : ℕ) : ℝ) :=
    congrFun (congrFun hagg 0) 1
  have hsum : aggregate dt dh (fun e => ((g e : ℕ) : ℝ)) 0 1 = ((g 0 : ℕ) : ℝ) := by
    simp only [aggregate, dcls01]
    rw [Finset.sum_singleton]
  rw [hsum] at h01
  have hgF : g 0 = dF 0 1 := Nat.cast_inj.mp h01
  have hdF : dF 0 1 = 5 := rfl
  have hdu : du 0 = 2 := rfl
  rw [hdF] at hgF
  have h2 := hle 0
  rw [hgF, hdu] at h2
  exact absurd h2 (by decide)

/-! Signed value and the `s = t` cut condition -/

private def rt : Fin 1 → Fin 2 := ![1]
private def rh : Fin 1 → Fin 2 := ![0]
private def ru : Fin 1 → ℕ := ![1]
private def ruc : Fin 1 → ℝ := fun e => (ru e : ℝ)
private def rf : Fin 1 → ℝ := ![1]

private theorem rhead0 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => rh e = 0) = {0} := by
  decide
private theorem rtail0 : (Finset.univ : Finset (Fin 1)).filter (fun e : Fin 1 => rt e = 0) = ∅ := by
  decide

theorem reverse_arc_feasible : IsArcFeasible rt rh ruc 0 1 rf := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    fin_cases e; norm_num [rf]
  · intro e
    fin_cases e; norm_num [rf, ruc, ru]
  · intro v hvs hvt
    fin_cases v <;> simp_all

theorem reverse_arc_value_neg_one : -((incidenceMatrix rt rh).mulVec rf 0) = -1 := by
  rw [incidence_mulVec, rhead0, rtail0,
    Finset.sum_singleton, Finset.sum_empty]
  show -((1 : ℝ) - 0) = -1
  norm_num

theorem no_self_cut_singleton : ¬ ∃ S : Finset (Fin 1), IsSTCut 0 0 S := by
  rintro ⟨S, hmem, hnotmem⟩
  exact hnotmem hmem

/-! Priced arcs -/

private def ct : Fin 2 → Fin 2 := ![0, 0]
private def ch : Fin 2 → Fin 2 := ![1, 1]
private def cfa : Fin 2 → ℝ := ![1, 0]
private def cfb : Fin 2 → ℝ := ![0, 1]
private def ccost : Fin 2 → ℝ := ![1, 10]

private theorem ccls00 : (Finset.univ : Finset (Fin 2)).filter (fun e => ct e = 0 ∧ ch e = 0) = ∅ := by
  decide
private theorem ccls01 : (Finset.univ : Finset (Fin 2)).filter (fun e => ct e = 0 ∧ ch e = 1) = {0, 1} := by
  decide
private theorem ccls10 : (Finset.univ : Finset (Fin 2)).filter (fun e => ct e = 1 ∧ ch e = 0) = ∅ := by
  decide
private theorem ccls11 : (Finset.univ : Finset (Fin 2)).filter (fun e => ct e = 1 ∧ ch e = 1) = ∅ := by
  decide

theorem priced_same_aggregate : aggregate ct ch cfa = aggregate ct ch cfb := by
  funext p q
  fin_cases p <;> fin_cases q <;>
    simp [aggregate, ccls00, ccls01, ccls10, ccls11, cfa, cfb,
      Finset.sum_empty, Finset.sum_insert, Finset.sum_singleton]

theorem priced_cost_a : (∑ e, ccost e * cfa e) = 1 := by
  simp only [Fin.sum_univ_two]
  norm_num [ccost, cfa]

theorem priced_cost_b : (∑ e, ccost e * cfb e) = 10 := by
  simp only [Fin.sum_univ_two]
  norm_num [ccost, cfb]

theorem priced_costs_differ : (∑ e, ccost e * cfa e) ≠ ∑ e, ccost e * cfb e := by
  rw [priced_cost_a, priced_cost_b]
  norm_num

#print axioms parallel_agg_cap_two
#print axioms parallel_lift_fst_half
#print axioms parallel_lift_snd_half
#print axioms parallel_split_bound
#print axioms parallel_nat_split_exists
#print axioms parallel_witness_le
#print axioms parallel_witness_exact
#print axioms antiparallel_dense_nonneg
#print axioms antiparallel_dense_cap
#print axioms antiparallel_dense_cons
#print axioms antiparallel_dense_feasible
#print axioms antiparallel_dense_value
#print axioms antiparallel_integral_lift
#print axioms loop_column_zero
#print axioms loop_flow_positive
#print axioms loop_balance_zero
#print axioms loop_source_value_zero
#print axioms zero_class_agg_zero
#print axioms zero_class_forces_zero
#print axioms empty_agg_zero
#print axioms empty_mulVec_zero
#print axioms empty_arc_feasible
#print axioms empty_split_bound
#print axioms empty_split_applies
#print axioms empty_dense_feasible
#print axioms empty_dense_value_zero
#print axioms empty_lift_value_zero
#print axioms maxflow_flow_nonneg
#print axioms maxflow_flow_cap
#print axioms maxflow_flow_cons
#print axioms maxflow_feasible_three
#print axioms maxflow_cut_zero
#print axioms integral_maxflow_pinned
#print axioms every_arc_competitor_le_three
#print axioms some_cut_sums_to_three
#print axioms half_caps_aggregate_one
#print axioms no_nat_split_of_half_caps
#print axioms half_dense_flow_nonneg
#print axioms half_dense_flow_cap
#print axioms half_dense_flow_cons
#print axioms half_dense_flow_feasible
#print axioms half_dense_flow_no_nat_preimage
#print axioms no_split_above_capacity
#print axioms reverse_arc_feasible
#print axioms reverse_arc_value_neg_one
#print axioms no_self_cut_singleton
#print axioms priced_same_aggregate
#print axioms priced_cost_a
#print axioms priced_cost_b
#print axioms priced_costs_differ

end Cslib.Algorithms.Lean.Graph.ArcNetworkIntegral
