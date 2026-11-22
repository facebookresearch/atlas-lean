/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
public import Mathlib.Logic.Relation

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# OD demand assignment on supplied routes

For supplied routes with arc-list edge volumes
(`MathlibExt.Combinatorics.Graph.ArcNetwork.edgeVolume`), this file states the demand
side of static assignment: OD node balance and which demand tables the supplied routes
can meet. Path flows `f : P → ℝ`, OD demands `r : V × V → ℝ`, edge volumes and node
balances share one flow unit (for example vehicles per hour). Node balance is inflow
minus outflow, the sign of `incidenceMatrix`.

## i. Overview

A path flow meets `r` when `∑ p with (orig p, dest p) = w, f p = r w` for every OD pair
`w` (the demand clause of `RoutingInstance.IsFeasible` for commodity
`p ↦ (orig p, dest p)`, written inline). An OD pair is unserved when no supplied route
has it as its OD pair. The results: OD node balance (attraction minus production) for
any meeting flow; a demand table is met by some nonnegative path flow exactly when it
is nonnegative and vanishes on every unserved pair; positive demand on an unserved pair
is rejected by every path flow; and with valid routes every unreachable OD pair is
unserved.

Scope: static demand admission on supplied routes only. No link costs or travel times,
no Wardrop or Beckmann statement, no equilibrium or uniqueness claim, no capacities,
no time-dependent flows, and no shortest-path, route-enumeration, reachability, flow or
feasibility algorithm.

## ii. Key results

- `FluidDynamics.Traffic.AssignmentBridge.incidenceMatrix_mulVec_edgeVolume_of_demand`:
  OD node balance.
- `FluidDynamics.Traffic.AssignmentBridge.exists_feasible_pathFlow_iff`: demand
  admission.
- `FluidDynamics.Traffic.AssignmentBridge.not_exists_pathFlow_of_unserved`: rejection of
  positive unserved demand.
- `FluidDynamics.Traffic.AssignmentBridge.unserved_of_not_reachable`: unreachable OD
  pairs are unserved.

## iii. Table of contents

- A. OD balance and admission

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetworkWalk`: arc walks and edge volumes.
- `MathlibExt.GameTheory.SelfishRouting`: the set-based routing model whose feasibility
  demand clause is written inline here.

## A. OD balance and admission
-/

@[expose] public section

namespace FluidDynamics.Traffic.AssignmentBridge

open MathlibExt.Combinatorics.Graph.ArcNetwork

private lemma arcWalk_reachable_aux {V E : Type*} {tail head : E → V} (l : List E) :
    ∀ (o d : V),
      IsArcWalk tail head o d l →
        Relation.ReflTransGen (fun u v => ∃ e, tail e = u ∧ head e = v) o d := by
  induction l with
  | nil =>
      intro o d hl
      have hod : o = d := hl.1 rfl
      subst hod
      exact Relation.ReflTransGen.refl
  | cons a l' ih =>
      intro o d hl
      cases l' with
      | nil =>
          have htail : tail a = o := arcWalk_tail_head hl
          have hhead : head a = d := arcWalk_single_head hl
          subst htail
          subst hhead
          exact Relation.ReflTransGen.single ⟨a, rfl, rfl⟩
      | cons b l'' =>
          have htail : tail a = o := arcWalk_tail_head hl
          have hwalk' : IsArcWalk tail head (head a) d (b :: l'') :=
            arcWalk_tail_of_cons hl
          have h2 := ih (head a) d hwalk'
          have h1 : Relation.ReflTransGen (fun u v => ∃ e, tail e = u ∧ head e = v) o (head a) := by
            subst htail
            exact Relation.ReflTransGen.single ⟨a, rfl, rfl⟩
          exact h1.trans h2

/-- OD node balance: if every supplied route is valid and the path flow meets the demand table
`r` on every OD pair, then inflow minus outflow of the edge volumes at `v` is the demand
attracted to `v` minus the demand produced at `v`; intrazonal demand `r (v, v)` cancels.
Nonnegativity of `f` is not used. -/
theorem incidenceMatrix_mulVec_edgeVolume_of_demand {V E P : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P] {tail head : E → V}
    {orig dest : P → V} {edges : P → List E}
    (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p)) {f : P → ℝ}
    {r : V × V → ℝ} (hdem : ∀ w, ∑ p with (orig p, dest p) = w, f p = r w) (v : V) :
    (incidenceMatrix tail head).mulVec (edgeVolume edges f) v =
      ∑ o, r (o, v) - ∑ d, r (v, d) := by
  have h3 := incidenceMatrix_mulVec_edgeVolume hwalk f v
  rw [h3]
  have hD : (∑ p, f p * (if dest p = v then (1 : ℝ) else 0)) =
      ∑ p with dest p = v, f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : dest p = v <;> simp [h]
  have hO : (∑ p, f p * (if orig p = v then (1 : ℝ) else 0)) =
      ∑ p with orig p = v, f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : orig p = v <;> simp [h]
  have hsplit : (∑ p,
        f p * ((if dest p = v then (1 : ℝ) else 0) - (if orig p = v then 1 else 0))) =
        (∑ p with dest p = v, f p) - (∑ p with orig p = v, f p) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, hD, hO]
  have hdest : ∑ o, r (o, v) = ∑ p with dest p = v, f p := by
    have hrw : ∀ o, r (o, v) = ∑ p with (orig p, dest p) = (o, v), f p :=
      fun o => (hdem _).symm
    simp_rw [hrw, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : dest p = v
    · subst h
      simp only [Prod.mk.injEq, and_true]
      rw [Finset.sum_eq_single (orig p)
        (fun o _ ho => by rw [ite_eq_right (Ne.symm ho)])
        (fun hcon => absurd (Finset.mem_univ _) hcon)]
      simp
    · have hterm : ∀ o, (if (orig p, dest p) = (o, v) then f p else 0) = 0 := by
        intro o
        apply ite_eq_right
        intro hcon
        exact h (congrArg Prod.snd hcon)
      simp_rw [hterm]
      rw [Finset.sum_const_zero, ite_eq_right h]
  have horig : ∑ d, r (v, d) = ∑ p with orig p = v, f p := by
    have hrw : ∀ d, r (v, d) = ∑ p with (orig p, dest p) = (v, d), f p :=
      fun d => (hdem _).symm
    simp_rw [hrw, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : orig p = v
    · subst h
      simp only [Prod.mk.injEq, true_and]
      rw [Finset.sum_eq_single (dest p)
        (fun d _ hd => by rw [ite_eq_right (Ne.symm hd)])
        (fun hcon => absurd (Finset.mem_univ _) hcon)]
      simp
    · have hterm : ∀ d, (if (orig p, dest p) = (v, d) then f p else 0) = 0 := by
        intro d
        apply ite_eq_right
        intro hcon
        exact h (congrArg Prod.fst hcon)
      simp_rw [hterm]
      rw [Finset.sum_const_zero, ite_eq_right h]
  rw [hsplit, hdest, horig]

/-- Demand admission: a demand table `r` is met by some nonnegative path flow on the supplied
routes iff it is nonnegative and vanishes on every OD pair that no supplied route serves.
Unserved OD pairs (with valid routes, every unreachable pair, by `unserved_of_not_reachable`)
are admitted exactly at zero demand. -/
theorem exists_feasible_pathFlow_iff {V P : Type*} [DecidableEq V] [Fintype P]
    (orig dest : P → V) (r : V × V → ℝ) :
    (∃ f : P → ℝ, (∀ p, 0 ≤ f p) ∧ ∀ w, ∑ p with (orig p, dest p) = w, f p = r w) ↔
      (∀ w, 0 ≤ r w) ∧ ∀ w, (∀ p, (orig p, dest p) ≠ w) → r w = 0 := by
  constructor
  · rintro ⟨f, hf, hdem⟩
    constructor
    · intro w
      rw [← hdem w]
      exact Finset.sum_nonneg (fun p _ => hf p)
    · intro w hw
      rw [← hdem w]
      have hempty : Finset.univ.filter (fun p => (orig p, dest p) = w) = ∅ :=
        Finset.filter_false_of_mem (fun p _ h => hw p h)
      rw [hempty, Finset.sum_empty]
  · rintro ⟨hrnonneg, hrzero⟩
    have hnonneg : ∀ p,
        0 ≤ r (orig p, dest p) /
          (((Finset.univ.filter
            (fun q => (orig q, dest q) = (orig p, dest p))).card : ℕ) : ℝ) := by
      intro p
      exact div_nonneg (hrnonneg _) (Nat.cast_nonneg _)
    have hdem : ∀ w, (∑ p with (orig p, dest p) = w,
        r (orig p, dest p) /
          (((Finset.univ.filter
            (fun q => (orig q, dest q) = (orig p, dest p))).card : ℕ) : ℝ)) = r w := by
      intro w
      have hterm : ∀ p ∈ Finset.univ.filter (fun p => (orig p, dest p) = w),
          r (orig p, dest p) /
              (((Finset.univ.filter
                (fun q => (orig q, dest q) = (orig p, dest p))).card : ℕ) : ℝ) =
            r w /
              (((Finset.univ.filter
                (fun q => (orig q, dest q) = w)).card : ℕ) : ℝ) := by
        intro p hp
        have hmem : (orig p, dest p) = w := (Finset.mem_filter.mp hp).2
        rw [hmem]
      rw [Finset.sum_congr rfl hterm]
      by_cases hcard : (Finset.univ.filter (fun q => (orig q, dest q) = w)).card = 0
      · have hS0 : Finset.univ.filter (fun q => (orig q, dest q) = w) = ∅ :=
          Finset.card_eq_zero.mp hcard
        have hwunserved : ∀ p, (orig p, dest p) ≠ w := by
          intro p hp
          have hmem : p ∈ Finset.univ.filter (fun q => (orig q, dest q) = w) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
          rw [hS0] at hmem
          exact Finset.notMem_empty p hmem
        rw [hS0, Finset.sum_empty]
        exact (hrzero w hwunserved).symm
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm,
          div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hcard)]
    exact ⟨_, hnonneg, hdem⟩

/-- Rejection: positive demand on an OD pair that no supplied route serves cannot be met by
any path flow, nonnegative or not. -/
theorem not_exists_pathFlow_of_unserved {V P : Type*} [DecidableEq V] [Fintype P]
    {orig dest : P → V} {r : V × V → ℝ} {w : V × V} (hw : ∀ p, (orig p, dest p) ≠ w)
    (hr : 0 < r w) :
    ¬∃ f : P → ℝ, ∀ w', ∑ p with (orig p, dest p) = w', f p = r w' := by
  rintro ⟨f, hdem⟩
  have h1 := hdem w
  have hempty : Finset.univ.filter (fun p => (orig p, dest p) = w) = ∅ :=
    Finset.filter_false_of_mem (fun p _ h => hw p h)
  rw [hempty, Finset.sum_empty] at h1
  exact (ne_of_gt hr) h1.symm

/-- Unreachable OD pairs are unserved: if every supplied route is a valid walk and `d` is not
reachable from `o` along arcs (tail to head), then no supplied route has OD pair `(o, d)`, so
the admission statements above apply to `(o, d)`. -/
theorem unserved_of_not_reachable {V E P : Type*} {tail head : E → V} {orig dest : P → V}
    {edges : P → List E} (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p))
    {o d : V} (hod : ¬Relation.ReflTransGen (fun u v => ∃ e, tail e = u ∧ head e = v) o d) :
    ∀ p, (orig p, dest p) ≠ (o, d) := by
  intro p hcon
  have ho : orig p = o := congrArg Prod.fst hcon
  have hd : dest p = d := congrArg Prod.snd hcon
  have hw := hwalk p
  rw [ho, hd] at hw
  exact hod (arcWalk_reachable_aux (edges p) o d hw)

end FluidDynamics.Traffic.AssignmentBridge
