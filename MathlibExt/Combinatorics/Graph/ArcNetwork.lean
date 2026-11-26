/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Real arc networks and dense capacity flow

The real-valued arc-ID adapter. Integral splitting is a later claim.

- C1 defines the signed incidence matrix and its flow interpretation, and proves that every
  incidence transfer has zero node sum, yielding the stock-level arc balance.
- C2 defines endpoint-pair aggregation and the arc-feasibility predicate.
- C3 transfers arc feasibility to dense feasibility with matching flow value.
- C4 provides the explicit proportional lift converse for nonnegative capacities.
- C5 identifies dense cut capacity with arc out-cut sums.
- C6 transfers the dense max-flow min-cut theorem to arc networks.
- C7 is exercised by the present companion tests (parallel/antiparallel arcs, loops,
  zero capacities, empty arcs, priced-arc non-preservation), which claim no dense cost
  preservation, positive lower-bound support, integrality, or complexity bound here.
-/

/-- Signed incidence matrix (C1): `B v e = 1[head e = v] - 1[tail e = v]`.
Incoming arcs contribute `+1`, outgoing arcs `-1`. Loop columns vanish (see
`incidence_loop_eq_zero`). The sign is fixed so `B.mulVec f` is incoming minus
outgoing flow and the source flow value is `-B.mulVec f s` (C3). -/
def incidenceMatrix {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) : Matrix V E ℝ :=
  fun v e => (if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0)

/-- C1: `B.mulVec f` at `v` equals incoming arc flow minus outgoing arc flow. -/
theorem incidence_mulVec {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (f : E → ℝ) (v : V) :
    (incidenceMatrix tail head).mulVec f v =
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e) -
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e) := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [incidenceMatrix]
  have hexpand : ∀ e : E, ((if head e = v then (1 : ℝ) else 0) -
      (if tail e = v then (1 : ℝ) else 0)) * f e =
      (if head e = v then f e else 0) - (if tail e = v then f e else 0) := by
    intro e
    split_ifs <;> ring
  simp only [hexpand, Finset.sum_sub_distrib, Finset.sum_filter]

/-- C1: loop columns vanish; a loop never contributes to net inflow. -/
theorem incidence_loop_eq_zero {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (e : E) (hloop : tail e = head e) (v : V) :
    incidenceMatrix tail head v e = 0 := by
  simp only [incidenceMatrix]
  rw [hloop]
  exact sub_self _

/-- The node sum of an incidence transfer is zero: every arc
contributes its transfer once at its head and once with the
opposite sign at its tail, including parallel arcs and loops. -/
theorem sum_incidenceMatrix_mulVec_eq_zero {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (F : E → ℝ) :
    ∑ v, (incidenceMatrix tail head).mulVec F v = 0 := by
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp only [sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  rw [Fintype.sum_ite_eq (head e) (fun _ => F e)]
  rw [Fintype.sum_ite_eq (tail e) (fun _ => F e)]
  exact sub_self (F e)

/-- Shared finite stock-level arc balance. If node inventories
update by `m' = m + B *ᵥ F + s - r` over one interval, where
`F` is a signed arc transfer and `s`, `r` are external source
and retirement vectors in the same selected stock unit, then
the total inventory changes only by the external terms. No
nonnegativity or physical admission hypothesis is used. -/
theorem stock_level_arc_balance {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (F : E → ℝ) {m m' s r : V → ℝ}
    (h : m' = m + (incidenceMatrix tail head).mulVec F + s - r) :
    ∑ v, m' v = ∑ v, m v + ∑ v, s v - ∑ v, r v := by
  rw [h]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_incidenceMatrix_mulVec_eq_zero]
  ring

/-- Endpoint-pair aggregation (C2): `aggregate f p q` is the sum of `f e` over arcs
with `tail e = p` and `head e = q`. The same operation aggregates capacities and flows. -/
def aggregate {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (f : E → ℝ) (p q : V) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = p ∧ head e = q), f e

/-- Reusable arc-feasibility predicate (C2): pointwise `0 ≤ f e ≤ u e` and zero net
inflow (`B.mulVec f v = 0`) at every vertex other than `s` and `t`. -/
def IsArcFeasible {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (u : E → ℝ) (s t : V) (f : E → ℝ) : Prop :=
  (∀ e, 0 ≤ f e) ∧ (∀ e, f e ≤ u e) ∧
    (∀ v, v ≠ s → v ≠ t → (incidenceMatrix tail head).mulVec f v = 0)

private theorem aggregate_nonneg {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (u : E → ℝ) (hcap : ∀ e, 0 ≤ u e)
    (p q : V) : 0 ≤ aggregate tail head u p q := by
  simp only [aggregate]
  exact Finset.sum_nonneg (fun e _ => hcap e)

private theorem aggregate_sum_incoming {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (f : E → ℝ) (v : V) :
    (∑ p : V, aggregate tail head f p v) =
      ∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e := by
  have hpt : ∀ e : E, (∑ p : V, (if tail e = p ∧ head e = v then f e else (0 : ℝ))) =
      (if head e = v then f e else 0) := by
    intro e
    by_cases he : head e = v
    · rw [ite_eq_left he]
      have hcond : ∀ p : V, (tail e = p ∧ head e = v) ↔ (tail e = p) :=
        fun p => and_iff_left he
      simp only [hcond]
      rw [Finset.sum_ite_eq]
      simp
    · rw [ite_eq_right he]
      apply Finset.sum_eq_zero
      intro p _
      exact ite_eq_right (fun hc => he hc.2)
  simp only [aggregate, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => hpt e)

private theorem aggregate_sum_outgoing {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (f : E → ℝ) (v : V) :
    (∑ q : V, aggregate tail head f v q) =
      ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e := by
  have hpt : ∀ e : E, (∑ q : V, (if tail e = v ∧ head e = q then f e else (0 : ℝ))) =
      (if tail e = v then f e else 0) := by
    intro e
    by_cases he : tail e = v
    · rw [ite_eq_left he]
      have hcond : ∀ q : V, (tail e = v ∧ head e = q) ↔ (head e = q) :=
        fun q => and_iff_right he
      simp only [hcond]
      rw [Finset.sum_ite_eq]
      simp
    · rw [ite_eq_right he]
      apply Finset.sum_eq_zero
      intro q _
      exact ite_eq_right (fun hc => he hc.1)
  simp only [aggregate, Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun e _ => hpt e)

/-- C3: arc feasibility implies dense feasibility for the aggregated capacity and flow. -/
theorem isFeasibleFlow_aggregate {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u f : E → ℝ) (s t : V)
    (hf : IsArcFeasible tail head u s t f) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (aggregate tail head u) s t (aggregate tail head f) := by
  obtain ⟨h0, hle, hcons⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    simp only [aggregate]
    exact Finset.sum_nonneg (fun e _ => h0 e)
  · intro p q
    simp only [aggregate]
    exact Finset.sum_le_sum (fun e _ => hle e)
  · intro v hvs hvt
    rw [aggregate_sum_incoming, aggregate_sum_outgoing]
    have h := hcons v hvs hvt
    rw [incidence_mulVec] at h
    exact sub_eq_zero.mp h

/-- C3: the dense flow value of an aggregate equals minus the net inflow at the source.
Holds for any arc vector, hence in particular under arc feasibility. -/
theorem flowValue_aggregate_eq_neg_mulVec {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (f : E → ℝ) (s : V) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s (aggregate tail head f) =
      -((incidenceMatrix tail head).mulVec f s) := by
  change (∑ v_1 : V, aggregate tail head f s v_1) - (∑ u : V, aggregate tail head f u s) =
    -((incidenceMatrix tail head).mulVec f s)
  rw [aggregate_sum_outgoing, aggregate_sum_incoming, incidence_mulVec]
  ring

/-- Explicit proportional real lift (C4): on an endpoint class of nonzero total capacity,
`F (tail e) (head e) * u e / aggregate u (tail e) (head e)`; on a zero-total-capacity class,
`0` explicitly. The lift therefore splits the flow `F p q` among the arcs from `p` to `q` only on
pairs of nonzero (for nonnegative capacities, positive) total capacity, and carries no flow on a
pair of zero total capacity whatever `F p q` is. No positivity, parallel-arc, loop, or
surjectivity assumptions. -/
noncomputable def proportionalLift {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (F : V → V → ℝ) (e : E) : ℝ :=
  if aggregate tail head u (tail e) (head e) = 0 then 0
  else F (tail e) (head e) * u e / aggregate tail head u (tail e) (head e)

/-- C4: the lift vanishes on zero-total-capacity endpoint classes. -/
theorem proportionalLift_zero {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (F : V → V → ℝ) (e : E)
    (h0 : aggregate tail head u (tail e) (head e) = 0) :
    proportionalLift tail head u F e = 0 := by
  unfold proportionalLift
  exact ite_eq_left h0

/-- C4: the lift formula on nonzero-total-capacity endpoint classes. -/
theorem proportionalLift_nonzero {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (F : V → V → ℝ) (e : E)
    (h0 : aggregate tail head u (tail e) (head e) ≠ 0) :
    proportionalLift tail head u F e =
      F (tail e) (head e) * u e / aggregate tail head u (tail e) (head e) := by
  unfold proportionalLift
  exact ite_eq_right h0

private theorem aggregate_proportionalLift_aux {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (u : E → ℝ)
    (_hcap : ∀ e, 0 ≤ u e) (F : V → V → ℝ) (s t : V)
    (hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (aggregate tail head u) s t F) (p q : V) :
    aggregate tail head (proportionalLift tail head u F) p q = F p q := by
  obtain ⟨hF0, hFle, hFcons⟩ := hF
  simp only [aggregate]
  by_cases hT : aggregate tail head u p q = 0
  · have hle0 : F p q ≤ 0 := by
      have h := hFle p q
      rw [hT] at h
      exact h
    have hF0' : F p q = 0 := le_antisymm hle0 (hF0 p q)
    rw [hF0']
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    have he1 : tail e = p := he.2.1
    have he2 : head e = q := he.2.2
    have h0 : aggregate tail head u (tail e) (head e) = 0 := by
      rw [he1, he2]
      exact hT
    exact proportionalLift_zero tail head u F e h0
  · have hsum : ∀ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = p ∧ head e = q),
        proportionalLift tail head u F e =
          (F p q / aggregate tail head u p q) * u e := by
      intro e he
      rw [Finset.mem_filter] at he
      have he1 : tail e = p := he.2.1
      have he2 : head e = q := he.2.2
      have h0 : aggregate tail head u (tail e) (head e) ≠ 0 := by
        rw [he1, he2]
        exact hT
      rw [proportionalLift_nonzero tail head u F e h0, he1, he2]
      ring
    rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]
    change (F p q / aggregate tail head u p q) * aggregate tail head u p q = F p q
    exact div_mul_cancel₀ _ hT

/-- C4: for nonnegative arc capacities, the proportional lift of a dense feasible flow
is arc-feasible. Conservation is proved, not assumed. -/
theorem isArcFeasible_proportionalLift {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (u : E → ℝ) (hcap : ∀ e, 0 ≤ u e)
    (F : V → V → ℝ) (s t : V)
    (hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (aggregate tail head u) s t F) :
    IsArcFeasible tail head u s t (proportionalLift tail head u F) := by
  obtain ⟨hF0, hFle, hFcons⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · intro e
    by_cases hT : aggregate tail head u (tail e) (head e) = 0
    · rw [proportionalLift_zero tail head u F e hT]
    · rw [proportionalLift_nonzero tail head u F e hT]
      have hTnn : 0 ≤ aggregate tail head u (tail e) (head e) :=
        aggregate_nonneg tail head u hcap _ _
      exact div_nonneg (mul_nonneg (hF0 _ _) (hcap e)) hTnn
  · intro e
    by_cases hT : aggregate tail head u (tail e) (head e) = 0
    · rw [proportionalLift_zero tail head u F e hT]
      exact hcap e
    · rw [proportionalLift_nonzero tail head u F e hT]
      have hTnn : 0 ≤ aggregate tail head u (tail e) (head e) :=
        aggregate_nonneg tail head u hcap _ _
      have hFle' : F (tail e) (head e) ≤ aggregate tail head u (tail e) (head e) :=
        hFle _ _
      calc F (tail e) (head e) * u e / aggregate tail head u (tail e) (head e)
          = F (tail e) (head e) * (u e / aggregate tail head u (tail e) (head e)) := by ring
        _ ≤ aggregate tail head u (tail e) (head e) *
            (u e / aggregate tail head u (tail e) (head e)) :=
            mul_le_mul_of_nonneg_right hFle' (div_nonneg (hcap e) hTnn)
        _ = u e := mul_div_cancel₀ _ hT
  · intro v hvs hvt
    have hin : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v),
          proportionalLift tail head u F e) = ∑ p : V, F p v := by
      rw [← aggregate_sum_incoming tail head]
      apply Finset.sum_congr rfl
      intro p _
      exact aggregate_proportionalLift_aux tail head u hcap F s t ⟨hF0, hFle, hFcons⟩ p v
    have hout : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v),
          proportionalLift tail head u F e) = ∑ q : V, F v q := by
      rw [← aggregate_sum_outgoing tail head]
      apply Finset.sum_congr rfl
      intro q _
      exact aggregate_proportionalLift_aux tail head u hcap F s t ⟨hF0, hFle, hFcons⟩ v q
    rw [incidence_mulVec, hin, hout]
    exact sub_eq_zero.mpr (hFcons v hvs hvt)

/-- C4: the lift aggregates back to exactly the dense flow it came from. -/
theorem aggregate_proportionalLift {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (hcap : ∀ e, 0 ≤ u e)
    (F : V → V → ℝ) (s t : V)
    (hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (aggregate tail head u) s t F) (p q : V) :
    aggregate tail head (proportionalLift tail head u F) p q = F p q := by
  exact aggregate_proportionalLift_aux tail head u hcap F s t hF p q

/-- C4: the lift preserves flow value: arc value `-B.mulVec` equals dense `flowValue`. -/
theorem flowValue_proportionalLift {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (hcap : ∀ e, 0 ≤ u e)
    (F : V → V → ℝ) (s t : V)
    (hF : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow
      (aggregate tail head u) s t F) :
    -((incidenceMatrix tail head).mulVec (proportionalLift tail head u F) s) =
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue s F := by
  have h := flowValue_aggregate_eq_neg_mulVec tail head (proportionalLift tail head u F) s
  have hcongr : aggregate tail head (proportionalLift tail head u F) = F := by
    funext p q
    exact aggregate_proportionalLift_aux tail head u hcap F s t hF p q
  rw [hcongr] at h
  exact h.symm

/-- C5: dense cut capacity of aggregated capacities equals the sum of arc capacities
leaving `S`. Loops never cross a cut; antiparallel arcs remain distinct. -/
theorem cutCapacity_aggregate_eq_sum_leaving {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (u : E → ℝ) (S : Finset V) :
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.cutCapacity (aggregate tail head u) S =
      ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), u e := by
  have hpt : ∀ e : E, (∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S,
      (if tail e = p ∧ head e = q then u e else (0 : ℝ))) =
      (if tail e ∈ S ∧ head e ∉ S then u e else 0) := by
    intro e
    by_cases h : tail e ∈ S ∧ head e ∉ S
    · rw [ite_eq_left h]
      obtain ⟨htS, hhS⟩ := h
      have hq : ∀ p ∈ S, (∑ q ∈ (Finset.univ : Finset V) \ S,
          (if tail e = p ∧ head e = q then u e else (0 : ℝ))) =
          (if tail e = p then u e else 0) := by
        intro p _
        by_cases htp : tail e = p
        · rw [ite_eq_left htp]
          have hcond : ∀ q : V, (tail e = p ∧ head e = q) ↔ (head e = q) :=
            fun q => and_iff_right htp
          simp only [hcond]
          rw [Finset.sum_ite_eq]
          have hmem : head e ∈ (Finset.univ : Finset V) \ S :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hhS⟩
          rw [ite_eq_left hmem]
        · rw [ite_eq_right htp]
          apply Finset.sum_eq_zero
          intro q _
          exact ite_eq_right (fun hc => htp hc.1)
      have hstep : (∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S,
          (if tail e = p ∧ head e = q then u e else (0 : ℝ))) =
          ∑ p ∈ S, (if tail e = p then u e else 0) :=
        Finset.sum_congr rfl hq
      rw [hstep, Finset.sum_ite_eq, ite_eq_left htS]
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q hq
      rw [Finset.mem_sdiff] at hq
      exact ite_eq_right (fun hc => h ⟨by rw [hc.1]; exact hp, by rw [hc.2]; exact hq.2⟩)
  have hLHS : (∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S, aggregate tail head u p q) =
      ∑ e : E, (if tail e ∈ S ∧ head e ∉ S then u e else 0) := by
    simp only [aggregate, Finset.sum_filter]
    calc (∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S, ∑ e : E,
            (if tail e = p ∧ head e = q then u e else (0 : ℝ)))
        = ∑ p ∈ S, ∑ e : E, ∑ q ∈ (Finset.univ : Finset V) \ S,
            (if tail e = p ∧ head e = q then u e else 0) :=
          Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
      _ = ∑ e : E, ∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S,
            (if tail e = p ∧ head e = q then u e else 0) := Finset.sum_comm
      _ = ∑ e : E, (if tail e ∈ S ∧ head e ∉ S then u e else 0) :=
          Finset.sum_congr rfl (fun e _ => hpt e)
  have hRHS : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), u e) =
      ∑ e : E, (if tail e ∈ S ∧ head e ∉ S then u e else 0) := by
    rw [Finset.sum_filter]
  have hcut : MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.cutCapacity
      (aggregate tail head u) S =
      ∑ p ∈ S, ∑ q ∈ (Finset.univ : Finset V) \ S, aggregate tail head u p q := rfl
  rw [hcut, hLHS, hRHS]

/-- C6: max-flow min-cut for real arc networks, transferred from the dense theorem via
C3-C5. Holds for nonnegative capacities and `s ≠ t`, including empty arc types and
zero-capacity classes. No new duality proof. -/
theorem arc_max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (u : E → ℝ) (hcap : ∀ e, 0 ≤ u e)
    (s t : V) (hst : s ≠ t) :
    ∃ f : E → ℝ, IsArcFeasible tail head u s t f ∧
      (∀ f' : E → ℝ, IsArcFeasible tail head u s t f' →
        -((incidenceMatrix tail head).mulVec f' s) ≤
        -((incidenceMatrix tail head).mulVec f s)) ∧
      (∀ S : Finset V,
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsSTCut s t S →
        -((incidenceMatrix tail head).mulVec f s) ≤
        ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), u e) ∧
      (∃ S : Finset V,
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsSTCut s t S ∧
        -((incidenceMatrix tail head).mulVec f s) =
        ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e ∈ S ∧ head e ∉ S), u e) := by
  have hcap' : ∀ p q : V, 0 ≤ aggregate tail head u p q :=
    fun p q => aggregate_nonneg tail head u hcap p q
  obtain ⟨F, hF, hmax, hcut_le, S, hScut, heq⟩ :=
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.max_flow_min_cut
      (aggregate tail head u) hcap' s t hst
  refine ⟨proportionalLift tail head u F, ?_, ?_, ?_, ?_⟩
  · exact isArcFeasible_proportionalLift tail head u hcap F s t hF
  · intro f' hf'
    have h1 := flowValue_aggregate_eq_neg_mulVec tail head f' s
    have h2 := hmax (aggregate tail head f')
      (isFeasibleFlow_aggregate tail head u f' s t hf')
    have h3 := flowValue_proportionalLift tail head u hcap F s t hF
    rw [← h1, h3]
    exact h2
  · intro S' hS'
    have h3 := flowValue_proportionalLift tail head u hcap F s t hF
    have h4 := hcut_le S' hS'
    have h5 := cutCapacity_aggregate_eq_sum_leaving tail head u S'
    rw [h3, ← h5]
    exact h4
  · refine ⟨S, hScut, ?_⟩
    have h3 := flowValue_proportionalLift tail head u hcap F s t hF
    have h5 := cutCapacity_aggregate_eq_sum_leaving tail head u S
    rw [h3, ← h5]
    exact heq

end MathlibExt.Combinatorics.Graph.ArcNetwork
