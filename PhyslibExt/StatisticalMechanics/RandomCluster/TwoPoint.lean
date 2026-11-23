/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKG
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent
/-!
# Connection events and the two-point function of finite FK measures

The event `{x ↔ y}`, its monotonicity, and the two-point function `τ(x, y) = φ(x ↔ y)` of the
free random-cluster measure on a finite graph.

## i. Overview

`connEvent G x y` is the set of configurations in which `x` and `y` are joined by a path of
open edges of `G`. It is increasing, so under the free random-cluster measure the two-point
function `twoPointFun G p q x y` is positive whenever `x` and `y` are connected in `G` (the
all-open configuration has positive mass), and two connection events are positively correlated
for `q ≥ 1` by the FKG inequality.

## ii. Key results

- `connEvent`, `connEvent_isIncreasing` : the connection event and its monotonicity.
- `twoPointFun` : the two-point function, with `twoPointFun_nonneg`, `twoPointFun_le_one`,
  `twoPointFun_pos_of_reachable`.
- `twoPointFun_fkg` : FKG for two connection events.

## iii. Table of contents

- A. Connection events
- B. The two-point function

## iv. References

- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!
## A. Connection events
-/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The open subgraph is monotone in the configuration. The same statement is
`StatMech.Sharpness.openSub_mono` in `BkCriterion`. -/
lemma openSub_mono {a b : ConfigSpace (Sym2 V)} (hab : a ≤ b) :
    openSub G a ≤ openSub G b := by
  intro x y h
  refine ⟨h.1, ?_⟩
  have hle := hab s(x, y)
  rw [h.2] at hle
  exact le_antisymm (Bool.le_true _) hle

/-- The event that `x` and `y` are joined by a path of open edges of `G`. -/
def connEvent (x y : V) : Set (ConfigSpace (Sym2 V)) :=
  {ω | (openSub G ω).Reachable x y}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma mem_connEvent {x y : V} {ω : ConfigSpace (Sym2 V)} :
    ω ∈ connEvent G x y ↔ (openSub G ω).Reachable x y := Iff.rfl

/-- Membership in a connection event is decidable. -/
instance instDecidablePredMemConnEvent (x y : V) :
    DecidablePred (· ∈ connEvent G x y) := by
  intro ω
  change Decidable ((openSub G ω).Reachable x y)
  infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma connEvent_self (x : V) : connEvent G x x = Set.univ := by
  ext ω
  simp only [mem_connEvent, Set.mem_univ, iff_true]
  exact SimpleGraph.Reachable.refl x

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma connEvent_isIncreasing (x y : V) : IsIncreasing (connEvent G x y) := by
  intro a b hab ha
  simp only [mem_connEvent] at ha ⊢
  exact ha.mono (openSub_mono G hab)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma allOpen_mem_connEvent {x y : V} (h : G.Reachable x y) :
    (fun _ => true) ∈ connEvent G x y := by
  have hG : openSub G (fun _ => true) = G := by ext a b; simp [openSub_adj]
  rw [mem_connEvent, hG]
  exact h

/-!
## B. The two-point function
-/

/-- The two-point function of the free random-cluster measure on a finite graph: the probability
`φ(x ↔ y)` that `x` and `y` are connected by open edges. -/
noncomputable def twoPointFun (p q : ℝ) (x y : V) : ℝ :=
  ∑ ω, fkProb G p q ω * (connEvent G x y).indicator (fun _ => (1 : ℝ)) ω

lemma twoPointFun_eq_sum_filter (p q : ℝ) (x y : V) :
    twoPointFun G p q x y =
      ∑ ω ∈ Finset.univ.filter (· ∈ connEvent G x y), fkProb G p q ω := by
  classical
  unfold twoPointFun
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ connEvent G x y
  · rw [Set.indicator_of_mem hω, mul_one, ite_eq_left hω]
  · rw [Set.indicator_of_notMem hω, mul_zero, ite_eq_right hω]

lemma twoPointFun_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : V) : 0 ≤ twoPointFun G p q x y := by
  unfold twoPointFun
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (fkProb_nonneg G hp hp1 hq ω)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)

lemma twoPointFun_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
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

lemma twoPointFun_pos_of_reachable {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {x y : V} (h : G.Reachable x y) : 0 < twoPointFun G p q x y := by
  unfold twoPointFun
  apply Finset.sum_pos'
  · intro ω _
    exact mul_nonneg (fkProb_nonneg G hp hp1 hq ω)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem (allOpen_mem_connEvent G h)]
    exact mul_pos (fkProb_pos G hp hp1 hq _) one_pos

lemma twoPointFun_self_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x : V) : 0 < twoPointFun G p q x x :=
  twoPointFun_pos_of_reachable G hp hp1 hq (SimpleGraph.Reachable.refl x)

/-- FKG for connection events: for `q ≥ 1`, `φ(x ↔ y) φ(u ↔ v) ≤ φ(x ↔ y, u ↔ v)`. -/
lemma twoPointFun_fkg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x y u v : V) :
    twoPointFun G p q x y * twoPointFun G p q u v
      ≤ ∑ ω, fkProb G p q ω *
          (connEvent G x y ∩ connEvent G u v).indicator (fun _ => (1 : ℝ)) ω := by
  exact fkProb_positively_associated_events G hp hp1 hq
    (connEvent_isIncreasing G x y) (connEvent_isIncreasing G u v)

end FK

end StatMech
