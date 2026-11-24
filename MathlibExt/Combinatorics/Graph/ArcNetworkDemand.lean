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

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# OD demand on supplied arc-walk routes

Demand-side consequences of the arc-walk edge volumes of
`MathlibExt.Combinatorics.Graph.ArcNetworkWalk`: OD node balance for a path flow
meeting a demand table, and unreachability implying that an OD pair is unserved.

Path flows `f : P → ℝ`, OD demands `r : V × V → ℝ`, edge volumes and node balances
share one flow unit (for example vehicles per hour). Node balance is inflow minus
outflow, the sign of `incidenceMatrix`. A path flow meets `r` when
`∑ p with (orig p, dest p) = w, f p = r w` for every OD pair `w`; demand admission
and rejection for that condition are the routing-instance results
`RoutingInstance.exists_isFeasible_iff` and
`RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne` at the commodity map
`p ↦ (orig p, dest p)`, so they are not restated here.

Scope: static OD balance and unserved-pair detection on supplied routes only. No
link costs or travel times, no equilibrium statement, no capacities, and no
algorithm.
-/

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

/-- Unreachable OD pairs are unserved: if every supplied route is a valid walk and `d` is not
reachable from `o` along arcs (tail to head), then no supplied route has OD pair `(o, d)`, so
so the admission results `RoutingInstance.exists_isFeasible_iff` and
`RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne` at the commodity map
`p ↦ (orig p, dest p)` apply to `(o, d)`. -/
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

end MathlibExt.Combinatorics.Graph.ArcNetwork
