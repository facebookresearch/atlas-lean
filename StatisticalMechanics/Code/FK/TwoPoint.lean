/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































import Code.FK.RandomCluster
import Code.FK.FKG
import Code.Inequalities.IncreasingEvent

open scoped BigOperators
open SimpleGraph

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem openSub_mono {a b : ConfigSpace (Sym2 V)} (hab : a ≤ b) :
    openSub G a ≤ openSub G b := by
  intro x y h
  refine ⟨h.1, ?_⟩
  have hle := hab s(x, y)
  rw [h.2] at hle
  exact le_antisymm (Bool.le_true _) hle






def connEvent (x y : V) : Set (ConfigSpace (Sym2 V)) :=
  {ω | (openSub G ω).Reachable x y}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_connEvent {x y : V} {ω : ConfigSpace (Sym2 V)} :
    ω ∈ connEvent G x y ↔ (openSub G ω).Reachable x y := Iff.rfl



instance instDecidablePredMemConnEvent (x y : V) :
    DecidablePred (· ∈ connEvent G x y) := by
  intro ω
  change Decidable ((openSub G ω).Reachable x y)
  infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


@[simp]
theorem connEvent_self (x : V) : connEvent G x x = Set.univ := by
  ext ω
  simp only [mem_connEvent, Set.mem_univ, iff_true]
  exact SimpleGraph.Reachable.refl x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in




theorem connEvent_isIncreasing (x y : V) : IsIncreasing (connEvent G x y) := by
  intro a b hab ha
  simp only [mem_connEvent] at ha ⊢
  exact ha.mono (openSub_mono G hab)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem allOpen_mem_connEvent {x y : V} (h : G.Reachable x y) :
    (fun _ => true) ∈ connEvent G x y := by
  have hG : openSub G (fun _ => true) = G := by ext a b; simp [openSub_adj]
  rw [mem_connEvent, hG]
  exact h






noncomputable def twoPointFun (p q : ℝ) (x y : V) : ℝ :=
  ∑ ω, fkProb G p q ω * (connEvent G x y).indicator (fun _ => (1 : ℝ)) ω



theorem twoPointFun_eq_sum_filter (p q : ℝ) (x y : V) :
    twoPointFun G p q x y =
      ∑ ω ∈ Finset.univ.filter (· ∈ connEvent G x y), fkProb G p q ω := by
  classical
  unfold twoPointFun
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ connEvent G x y
  · rw [Set.indicator_of_mem hω, mul_one, if_pos hω]
  · rw [Set.indicator_of_notMem hω, mul_zero, if_neg hω]


theorem twoPointFun_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : V) : 0 ≤ twoPointFun G p q x y := by
  unfold twoPointFun
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (fkProb_nonneg G hp hp1 hq ω)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)



theorem twoPointFun_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : V) : twoPointFun G p q x y ≤ 1 := by
  have hsum : twoPointFun G p q x y ≤ ∑ ω, fkProb G p q ω := by
    unfold twoPointFun
    apply Finset.sum_le_sum
    intro ω _
    have hind : (connEvent G x y).indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
      by_cases hω : ω ∈ connEvent G x y
      · rw [Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω]; exact zero_le_one
    calc fkProb G p q ω * (connEvent G x y).indicator (fun _ => (1 : ℝ)) ω
        ≤ fkProb G p q ω * 1 :=
          mul_le_mul_of_nonneg_left hind (fkProb_nonneg G hp hp1 hq ω)
      _ = fkProb G p q ω := mul_one _
  rwa [fkProb_sum_eq_one G hp hp1 hq] at hsum





theorem twoPointFun_pos_of_reachable {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {x y : V} (h : G.Reachable x y) : 0 < twoPointFun G p q x y := by
  unfold twoPointFun
  apply Finset.sum_pos'
  · intro ω _
    exact mul_nonneg (fkProb_nonneg G hp hp1 hq ω)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem (allOpen_mem_connEvent G h)]
    exact mul_pos (fkProb_pos G hp hp1 hq _) one_pos



theorem twoPointFun_self_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x : V) : 0 < twoPointFun G p q x x :=
  twoPointFun_pos_of_reachable G hp hp1 hq (SimpleGraph.Reachable.refl x)












theorem twoPointFun_fkg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x y u v : V) :
    twoPointFun G p q x y * twoPointFun G p q u v
      ≤ ∑ ω, fkProb G p q ω *
          (connEvent G x y ∩ connEvent G u v).indicator (fun _ => (1 : ℝ)) ω := by
  exact fkProb_positively_associated_events G hp hp1 hq
    (connEvent_isIncreasing G x y) (connEvent_isIncreasing G u v)

end FK

end StatMech
