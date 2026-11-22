/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.WardropExistence
public import MathlibExt.GameTheory.SelfishRoutingArcWalkBridge
public import MathlibExt.Combinatorics.Graph.ArcNetworkDemand
public import Mathlib.Tactic.FunProp

open MathlibExt.GameTheory.SelfishRouting

/-- Pigou's network has a Wardrop flow for every nonnegative demand. -/
example (t : ℝ) (ht : 0 ≤ t) : ∃ f, pigou.IsFeasible (fun _ => t) f ∧ pigou.IsWardrop f :=
  pigou.exists_isWardrop (fun e => by
      fin_cases e
      · exact continuousOn_const
      · exact continuousOn_id)
    (fun _ => ht) (fun _ => ⟨0, rfl⟩)

/-- Without a path, a commodity with positive demand has no feasible flow, so the path
hypothesis of `exists_isWardrop` cannot be dropped outright; it weakens to zero demand on
pathless commodities (`exists_isWardrop_iff`). -/
example (N : RoutingInstance (Fin 1) Unit Empty) :
    ¬ ∃ f, N.IsFeasible (fun _ => 1) f := by
  rintro ⟨f, -, h⟩
  simpa using h ()

/-! ### Admission form of existence -/

open MathlibExt.Combinatorics.Graph.ArcNetwork

example : ∀ {E ι P : Type*} [Fintype P] [DecidableEq E] [DecidableEq ι]
    (N : RoutingInstance E ι P) [Finite E], (∀ e, ContinuousOn (N.latency e) (Set.Ici 0)) →
    ∀ r : ι → ℝ, (∃ f, N.IsFeasible r f ∧ N.IsWardrop f) ↔
      (∀ i, 0 ≤ r i) ∧ ∀ i, (∀ p, N.commodity p ≠ i) → r i = 0 :=
  @RoutingInstance.exists_isWardrop_iff

/-- Under continuity an equilibrium exists exactly when a feasible flow does. -/
example {E ι P : Type*} [Fintype P] [DecidableEq E] [DecidableEq ι] (N : RoutingInstance E ι P)
    [Finite E] (hℓ : ∀ e, ContinuousOn (N.latency e) (Set.Ici 0)) (r : ι → ℝ) :
    (∃ f, N.IsFeasible r f ∧ N.IsWardrop f) ↔ ∃ f, N.IsFeasible r f := by
  rw [N.exists_isWardrop_iff hℓ r, N.exists_isFeasible_iff r]

/-- the recorded hypothesis form: positive demand only on served commodities. -/
example {E ι P : Type*} [Fintype P] [DecidableEq E] [DecidableEq ι] (N : RoutingInstance E ι P)
    [Finite E] (hℓ : ∀ e, ContinuousOn (N.latency e) (Set.Ici 0)) {r : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hpos : ∀ i, 0 < r i → ∃ p, N.commodity p = i) :
    ∃ f, N.IsFeasible r f ∧ N.IsWardrop f :=
  (N.exists_isWardrop_iff hℓ r).2 ⟨hr, fun i hi => le_antisymm
    (not_lt.1 fun h => (hpos i h).elim fun p hp => hi p hp) (hr i)⟩

/-- The OD instance of given arc-list routes with link travel times `t`. -/
abbrev odInst {V E P : Type*} [DecidableEq E] (orig dest : P → V) (edges : P → List E)
    (t : E → ℝ → ℝ) :
    RoutingInstance E (V × V) P :=
  { commodity := fun p => (orig p, dest p), edges := fun p => (edges p).toFinset, latency := t }

/-- on link-simple routes `IsWardrop` is Wardrop's first principle in route travel times at
the induced traversal-count volumes. -/
example {V E P : Type*} [Fintype P] [DecidableEq E] (orig dest : P → V) (edges : P → List E)
    (t : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup) (f : P → ℝ) :
    (odInst orig dest edges t).IsWardrop f ↔
      ∀ p q, orig p = orig q → dest p = dest q → 0 < f p →
        ((edges p).map fun e => t e (edgeVolume edges f e)).sum ≤
          ((edges q).map fun e => t e (edgeVolume edges f e)).sum := by
  simp only [RoutingInstance.IsWardrop, odInst,
    RoutingInstance.pathLatency_eq_sum_map orig dest edges t hsimple, Prod.mk.injEq, and_imp]

/-- two equilibria of one OD table have equal link travel times at the edge volumes. -/
example {V E P : Type*} [Finite V] [Fintype P] [Finite E] [DecidableEq V] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (t : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup)
    (hmono : ∀ e, MonotoneOn (t e) (Set.Ici 0)) {r : V × V → ℝ} {f g : P → ℝ}
    (hWf : (odInst orig dest edges t).IsWardrop f) (hf : (odInst orig dest edges t).IsFeasible r f)
    (hWg : (odInst orig dest edges t).IsWardrop g) (hg : (odInst orig dest edges t).IsFeasible r g)
    (e : E) : t e (edgeVolume edges f e) = t e (edgeVolume edges g e) := by
  have h := RoutingInstance.IsWardrop.latency_edgeFlow_eq hmono hWf hf hWg hg e
  rwa [RoutingInstance.edgeFlow_eq_edgeVolume orig dest edges t hsimple,
    RoutingInstance.edgeFlow_eq_edgeVolume orig dest edges t hsimple] at h

/-- two equilibria of one OD table have equal total travel time `∑ e, x e * t e (x e)`. -/
example {V E P : Type*} [Finite V] [Fintype P] [Fintype E] [DecidableEq V] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (t : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup)
    (hmono : ∀ e, MonotoneOn (t e) (Set.Ici 0)) {r : V × V → ℝ} {f g : P → ℝ}
    (hWf : (odInst orig dest edges t).IsWardrop f) (hf : (odInst orig dest edges t).IsFeasible r f)
    (hWg : (odInst orig dest edges t).IsWardrop g) (hg : (odInst orig dest edges t).IsFeasible r g) :
    ∑ e, edgeVolume edges f e * t e (edgeVolume edges f e) =
      ∑ e, edgeVolume edges g e * t e (edgeVolume edges g e) := by
  have hc : ∀ h : P → ℝ, (odInst orig dest edges t).cost h =
      ∑ e, edgeVolume edges h e * t e (edgeVolume edges h e) := fun h =>
    Finset.sum_congr rfl fun e _ => by
      rw [RoutingInstance.edgeFlow_eq_edgeVolume orig dest edges t hsimple, mul_comm]
  rw [← hc, ← hc, RoutingInstance.IsWardrop.cost_eq hmono hWf hf hWg hg]

/-- Kept separate from path flows: strictly increasing link times make the edge volumes of two
equilibria equal, by equality of their link travel times; path flows stay non-unique (final example). -/
example {V E P : Type*} [Finite V] [Fintype P] [Finite E] [DecidableEq V] [DecidableEq E]
    (orig dest : P → V) (edges : P → List E) (t : E → ℝ → ℝ) (hsimple : ∀ p, (edges p).Nodup)
    (hstrict : ∀ e, StrictMonoOn (t e) (Set.Ici 0)) {r : V × V → ℝ} {f g : P → ℝ}
    (hWf : (odInst orig dest edges t).IsWardrop f) (hf : (odInst orig dest edges t).IsFeasible r f)
    (hWg : (odInst orig dest edges t).IsWardrop g) (hg : (odInst orig dest edges t).IsFeasible r g)
    (e : E) : edgeVolume edges f e = edgeVolume edges g e := by
  have h := RoutingInstance.IsWardrop.latency_edgeFlow_eq (fun e => (hstrict e).monotoneOn)
    hWf hf hWg hg e
  rw [RoutingInstance.edgeFlow_eq_edgeVolume orig dest edges t hsimple,
    RoutingInstance.edgeFlow_eq_edgeVolume orig dest edges t hsimple] at h
  exact (hstrict e).injOn (edgeVolume_nonneg edges hf.1 e) (edgeVolume_nonneg edges hg.1 e) h

/-- positive demand on an OD pair that the arcs cannot reach admits no equilibrium. -/
example {V E P : Type*} [Fintype P] [DecidableEq V] [DecidableEq E] [Finite E]
    {tail head : E → V} {orig dest : P → V} {edges : P → List E}
    (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p)) (t : E → ℝ → ℝ)
    (ht : ∀ e, ContinuousOn (t e) (Set.Ici 0)) {r : V × V → ℝ} {o d : V}
    (hod : ¬Relation.ReflTransGen (fun u v => ∃ e, tail e = u ∧ head e = v) o d)
    (hr : 0 < r (o, d)) :
    ¬∃ f, (odInst orig dest edges t).IsFeasible r f ∧ (odInst orig dest edges t).IsWardrop f := by
  rw [(odInst orig dest edges t).exists_isWardrop_iff ht r]
  rintro ⟨-, h⟩
  exact hr.ne' (h (o, d) (unserved_of_not_reachable hwalk hod))

/-! ### A declared physical instance
Nodes `A, B, C = 0, 1, 2`; links `0, 1 : A → B` (parallel), `2 : B → C`, `3 : A → C`;
link-simple routes `[0, 2]`, `[1, 2]`, `[3]` from `A` to `C`; travel times in minutes
`2 x`, `x + 3`, `x`, `x + 13` at link flow `x` in vehicles per minute; 6 vehicles per minute
from `A` to `C`, nothing on the other eight OD pairs. -/

abbrev wTail : Fin 4 → Fin 3 := ![0, 0, 1, 0]
abbrev wHead : Fin 4 → Fin 3 := ![1, 1, 2, 2]
abbrev wRoutes : Fin 3 → List (Fin 4) := ![[0, 2], [1, 2], [3]]
def wTime : Fin 4 → ℝ → ℝ := ![fun x => 2 * x, fun x => x + 3, fun x => x, fun x => x + 13]
noncomputable def wDemand (w : Fin 3 × Fin 3) : ℝ := if w = (0, 2) then 6 else 0

theorem w_walk : ∀ p, IsArcWalk wTail wHead ((fun _ => 0 : Fin 3 → Fin 3) p)
    ((fun _ => 2 : Fin 3 → Fin 3) p) (wRoutes p) := by
  intro p
  fin_cases p
  · exact walk_cons_mk rfl (walk_singleton rfl rfl)
  · exact walk_cons_mk rfl (walk_singleton rfl rfl)
  · exact walk_singleton rfl rfl

theorem w_simple : ∀ p, (wRoutes p).Nodup := by decide

theorem w_volume (f : Fin 3 → ℝ) : edgeVolume wRoutes f = ![f 0, f 1, f 0 + f 1, f 2] := by
  funext e
  fin_cases e <;> simp [edgeVolume, Fin.sum_univ_three]

theorem w_routeTime (f : Fin 3 → ℝ) (p : Fin 3) :
    (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).pathLatency f p =
      ![2 * f 0 + (f 0 + f 1), f 1 + 3 + (f 0 + f 1), f 2 + 13] p := by
  rw [RoutingInstance.pathLatency_eq_sum_map _ _ wRoutes wTime w_simple, w_volume]
  fin_cases p <;> simp [wTime]

theorem w_continuous : ∀ e, ContinuousOn (wTime e) (Set.Ici 0) := by
  intro e
  apply Continuous.continuousOn
  fin_cases e
  · exact continuous_const.mul continuous_id
  · exact continuous_id.add continuous_const
  · exact continuous_id
  · exact continuous_id.add continuous_const

/-- Existence by the admission form, where the path hypothesis of `exists_isWardrop` fails. -/
example : ¬ (∀ i, ∃ p, (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).commodity p = i) ∧
    ∃ f, (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsFeasible wDemand f ∧
      (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsWardrop f := by
  refine ⟨fun h => ?_, ((odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).exists_isWardrop_iff
    w_continuous wDemand).2
    ⟨fun i => by unfold wDemand; split_ifs <;> norm_num, fun i hi => ?_⟩⟩
  · obtain ⟨p, hp⟩ := h ((2 : Fin 3), (0 : Fin 3))
    simp at hp
  · unfold wDemand
    split_ifs with hi0
    · subst hi0
      exact (hi 0 rfl).elim
    · rfl

/-- The equilibrium `(3, 3, 0)`: volumes `(3, 3, 6, 0)`, route times `(12, 12, 13)` minutes,
total travel time `72 = 6 * 12` vehicle-minutes per minute. -/
example : (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsFeasible wDemand ![3, 3, 0] ∧
    (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsWardrop ![3, 3, 0] ∧
    edgeVolume wRoutes ![3, 3, 0] = ![3, 3, 6, 0] ∧
    (∑ e, edgeVolume wRoutes ![3, 3, 0] e * wTime e (edgeVolume wRoutes ![3, 3, 0] e)) = 72 := by
  refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun i => ?_⟩, fun p q _ hp => ?_, ?_, ?_⟩
  · unfold wDemand
    split_ifs with hi
    · subst hi
      simp [Fin.sum_univ_three]
      norm_num
    · have : Finset.univ.filter
          (fun p => (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).commodity p = i) = ∅ :=
        Finset.filter_false_of_mem fun p _ hp => hi hp.symm
      rw [this, Finset.sum_empty]
  · rw [w_routeTime, w_routeTime]
    revert hp
    fin_cases p <;> fin_cases q <;> norm_num
  · rw [w_volume]
    funext e
    fin_cases e <;> norm_num
  · rw [w_volume]
    simp [Fin.sum_univ_four, wTime]
    norm_num

/-- Units: the same equilibrium in vehicles per hour, `t' e y = t e (y / 60)`. -/
example : (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes
      (fun e y => wTime e (y / 60))).IsWardrop ![180, 180, 0] := by
  intro p q _ hp
  rw [RoutingInstance.pathLatency_eq_sum_map _ _ wRoutes _ w_simple,
    RoutingInstance.pathLatency_eq_sum_map _ _ wRoutes _ w_simple, w_volume]
  revert hp
  fin_cases p <;> fin_cases q <;> norm_num [wTime]

/-- `C` has no outgoing link, so `A` is unreachable from `C`. -/
theorem w_unreachable : ¬Relation.ReflTransGen (fun u v => ∃ e, wTail e = u ∧ wHead e = v) 2 0 := by
  intro h
  have key : ∀ v, Relation.ReflTransGen (fun u v => ∃ e, wTail e = u ∧ wHead e = v) 2 v →
      v = 2 := by
    intro v hv
    induction hv with
    | refl => rfl
    | tail _ hbc ih =>
      obtain ⟨e, he, -⟩ := hbc
      subst ih
      fin_cases e <;> simp at he
  exact absurd (key 0 h) (by decide)

/-- One vehicle per minute from `C` to `A` on top of `wDemand`: no equilibrium. -/
example : ¬∃ f, (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsFeasible
      (fun w => wDemand w + if w = (2, 0) then 1 else 0) f ∧
    (odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).IsWardrop f := by
  rw [(odInst (fun _ => (0 : Fin 3)) (fun _ => (2 : Fin 3)) wRoutes wTime).exists_isWardrop_iff w_continuous]
  rintro ⟨-, h⟩
  have := h ((2 : Fin 3), (0 : Fin 3)) (unserved_of_not_reachable w_walk w_unreachable)
  simp [wDemand] at this

/-! ### Focused checks -/

/-- Nondecreasing but non-strict costs: two parallel links of constant time 1, demand 1. The
flows `(1, 0)` and `(1/2, 1/2)` are both equilibria with different link volumes but equal link
times and equal cost. -/
example : let N : RoutingInstance (Fin 2) Unit (Fin 2) := ⟨fun _ => (), fun p => {p}, fun _ _ => 1⟩
    (N.IsFeasible (fun _ => 1) ![1, 0] ∧ N.IsWardrop ![1, 0]) ∧
    (N.IsFeasible (fun _ => 1) ![1 / 2, 1 / 2] ∧ N.IsWardrop ![1 / 2, 1 / 2]) ∧
    N.edgeFlow ![1, 0] 0 ≠ N.edgeFlow ![1 / 2, 1 / 2] 0 ∧
    N.cost ![1, 0] = N.cost ![1 / 2, 1 / 2] := by
  intro N
  have hef : ∀ (f : Fin 2 → ℝ) e, N.edgeFlow f e = f e := fun f e => by
    simp [N, RoutingInstance.edgeFlow, Finset.sum_filter]
  refine ⟨⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => by simp [N, Fin.sum_univ_two]⟩,
      fun p q _ _ => by simp [RoutingInstance.pathLatency, N]⟩,
    ⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => by simp [N, Fin.sum_univ_two]; norm_num⟩,
      fun p q _ _ => by simp [RoutingInstance.pathLatency, N]⟩, ?_, ?_⟩
  · rw [hef, hef]; norm_num
  · simp only [RoutingInstance.cost, hef]
    simp [N, Fin.sum_univ_two]
    norm_num

/-- Distinct routes with identical link use: route ids `0` and `1` both use link `0` with
strictly increasing time `x`; `(1, 0)` and `(0, 1)` are equilibria with the same volume. -/
abbrev sameLinkRoutes : Fin 2 → List (Fin 1) := ![[0], [0]]

example : let N := odInst (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => (1 : Fin 2)) sameLinkRoutes (fun _ x => x)
    (N.IsFeasible (fun w => if w = (0, 1) then 1 else 0) ![1, 0] ∧ N.IsWardrop ![1, 0]) ∧
    (N.IsFeasible (fun w => if w = (0, 1) then 1 else 0) ![0, 1] ∧ N.IsWardrop ![0, 1]) ∧
    edgeVolume sameLinkRoutes ![1, 0] = edgeVolume sameLinkRoutes ![0, 1] ∧
    (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  intro N
  have hs : ∀ p, (sameLinkRoutes p).Nodup := by decide
  have hv : ∀ f : Fin 2 → ℝ, edgeVolume sameLinkRoutes f =
      fun _ => f 0 + f 1 := fun f => by
    funext e; fin_cases e; simp [edgeVolume, Fin.sum_univ_two]
  have hL : ∀ (f : Fin 2 → ℝ) p, N.pathLatency f p = f 0 + f 1 := fun f p => by
    rw [RoutingInstance.pathLatency_eq_sum_map _ _ _ _ hs, hv]
    fin_cases p <;> simp
  have hfeas : ∀ f : Fin 2 → ℝ, (∀ p, 0 ≤ f p) → f 0 + f 1 = 1 →
      N.IsFeasible (fun w => if w = (0, 1) then 1 else 0) f := by
    intro f hf h1
    refine ⟨hf, fun w => ?_⟩
    show _ = if w = (0, 1) then 1 else 0
    split_ifs with hw
    · subst hw
      simp [N, Fin.sum_univ_two, h1]
    · have : Finset.univ.filter (fun p => N.commodity p = w) = ∅ :=
        Finset.filter_false_of_mem fun p _ hp => hw hp.symm
      rw [this, Finset.sum_empty]
  refine ⟨⟨hfeas _ (fun p => by fin_cases p <;> norm_num) (by norm_num),
      fun p q _ _ => by rw [hL, hL]⟩,
    ⟨hfeas _ (fun p => by fin_cases p <;> norm_num) (by norm_num),
      fun p q _ _ => by rw [hL, hL]⟩, by rw [hv, hv]; norm_num, ?_⟩
  intro h
  have := congrFun h 0
  norm_num at this

#print axioms RoutingInstance.exists_isWardrop
#print axioms RoutingInstance.exists_isWardrop_iff
