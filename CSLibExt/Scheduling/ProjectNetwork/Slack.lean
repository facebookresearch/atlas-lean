/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Bounds.Defs

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Slack and total float in a project network

An activity-on-arc project network has an event type `V`, a finite arc (activity) type `E` with
`tail head : E → V`, and arc durations `d : E → R` in a linearly ordered additive commutative
group `R` (such as `ℝ`). Walks are arc lists (`IsArcWalk`) and the duration of a walk `l` is
`(l.map d).sum`. The network is acyclic when its only closed walk is the empty one; no walk then
visits an event twice, so walks are paths.

- `longestDuration tail head d u v` is the duration `ℓ(u, v)` of a longest walk from `u` to `v`.
- For a source `s` and a sink `t`, the earliest start of an event is `ES(v) = ℓ(s, v)`
  (`earliestStart`), its latest start is `LS(v) = ℓ(s, t) - ℓ(v, t)` (`latestStart`), and the
  total float of an arc `e` is `TF(e) = LS(head e) - ES(tail e) - d e` (`totalFloat`).
- `critical_path_slack`: for a finite acyclic network in which every event lies on a walk from
  `s` to `t`, `ℓ(s, t)` is the least project duration `τ t - τ s` of an event schedule `τ`
  meeting every arc's duration, the slack `LS(v) - ES(v)` of every event is nonnegative and
  vanishes exactly on the events of a longest `s`–`t` walk, and the total float of every arc is
  nonnegative and vanishes exactly on the arcs of a longest `s`–`t` walk. None of this needs a
  sign condition on the durations, but for durations of any sign an event schedule may put
  events before `τ s`. With nonnegative durations every event of an event schedule lies between
  `τ s` and `τ t`, and `ℓ(s, t)` is also the least `τ t` over event schedules with `τ s = 0` and
  no negative event time, as in the linear-programming formulation of the minimum project
  duration.
- `slack_eq_zero_totalFloat_eq_one`: zero slack at both endpoints does not make an arc critical.

`longestDuration` takes the junk value `0` when the walk durations from `u` to `v` have no
greatest element, as when no walk runs from `u` to `v`; the hypotheses of `critical_path_slack`
rule this out for every value it uses.

Reference: J. E. Beasley, *OR-Notes: Network analysis — activity on arc examples*, worked
examples of earliest and latest start times and float times.
-/

namespace Cslib.Scheduling.ProjectNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork

variable {V E R : Type*} [AddCommGroup R] [LinearOrder R]

open scoped Classical in
/-- **Longest walk duration.** The duration `ℓ(u, v)` of a longest walk from `u` to `v` in the
activity-on-arc network `tail head : E → V` with arc durations `d : E → R`: the greatest element
of the set of durations `(l.map d).sum` of the walks `l` from `u` to `v`. When that set has no
greatest element, as when no walk runs from `u` to `v`, the value is `0`, a junk value. -/
noncomputable def longestDuration (tail head : E → V) (d : E → R) (u v : V) : R :=
  if h : ∃ x, IsGreatest ((fun l : List E => (l.map d).sum) '' {l | IsArcWalk tail head u v l}) x
  then h.choose else 0

/-- **Earliest start of an event.** For a project network `tail head : E → V` with arc durations
`d` and source `s`, the earliest start of the event `v` is the duration of a longest walk from `s`
to `v`, `ES(v) = ℓ(s, v)` (`longestDuration`). -/
noncomputable def earliestStart (tail head : E → V) (d : E → R) (s v : V) : R :=
  longestDuration tail head d s v

/-- **Latest start of an event.** For a project network `tail head : E → V` with arc durations
`d`, source `s` and sink `t`, the latest start of the event `v` is the project length
`L = ℓ(s, t)` minus the duration of a longest walk from `v` to `t`,
`LS(v) = ℓ(s, t) - ℓ(v, t)` (`longestDuration`). -/
noncomputable def latestStart (tail head : E → V) (d : E → R) (s t v : V) : R :=
  longestDuration tail head d s t - longestDuration tail head d v t

/-- **Total float of an activity.** For a project network `tail head : E → V` with arc durations
`d`, source `s` and sink `t`, the total float of the arc `e` is the latest start of its head
event minus the earliest start of its tail event minus its duration,
`TF(e) = LS(head e) - ES(tail e) - d e`. -/
noncomputable def totalFloat (tail head : E → V) (d : E → R) (s t : V) (e : E) : R :=
  latestStart tail head d s t (head e) - earliestStart tail head d s (tail e) - d e

section Walks

variable {tail head : E → V} {d : E → R}

-- Event times meeting every arc's duration bound every walk's duration by the difference of
-- the times of its ends.
theorem add_sum_map_le_of_forall_add_le [IsOrderedAddMonoid R] {τ : V → R}
    (hτ : ∀ e, τ (tail e) + d e ≤ τ (head e))
    {o o' : V} {l : List E} (hl : IsArcWalk tail head o o' l) : τ o + (l.map d).sum ≤ τ o' := by
  induction l generalizing o with
  | nil =>
    rw [hl.1 rfl]
    simp
  | cons a rest ih =>
    obtain ⟨htail, hrest⟩ := walk_cons_pair hl
    have h1 := ih hrest
    have h2 := hτ a
    rw [htail] at h2
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact (add_le_add_left h2 _).trans h1

/-- In a network whose only closed walk is the empty one, no walk repeats an arc. -/
private theorem nodup_of_isArcWalk (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = [])
    {o o' : V} {l : List E} (hl : IsArcWalk tail head o o' l) : l.Nodup := by
  induction l generalizing o with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    obtain ⟨-, hrest⟩ := walk_cons_pair hl
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih hrest⟩
    obtain ⟨b, c, rfl⟩ := List.append_of_mem hmem
    obtain ⟨m, hb, hc⟩ := walk_append hrest
    obtain ⟨hm, -⟩ := walk_cons_pair hc
    rw [← hm] at hb
    exact List.cons_ne_nil a b (hacyc _ _ (walk_cons_mk rfl hb))

/-- In a finite network whose only closed walk is the empty one, there are finitely many walks
between two events. -/
private theorem finite_setOf_isArcWalk [Finite E]
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) (u v : V) :
    {l | IsArcWalk tail head u v l}.Finite := by
  have := Fintype.ofFinite E
  refine (List.finite_length_le E (Fintype.card E)).subset fun l hl => ?_
  exact (nodup_of_isArcWalk hacyc hl).length_le_card

theorem isGreatest_longestDuration [Finite E]
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) {u v : V}
    (h : ∃ l, IsArcWalk tail head u v l) :
    IsGreatest ((fun l : List E => (l.map d).sum) '' {l | IsArcWalk tail head u v l})
      (longestDuration tail head d u v) := by
  obtain ⟨l₀, hl₀, hmax⟩ :=
    Set.exists_max_image _ (fun l : List E => (l.map d).sum) (finite_setOf_isArcWalk hacyc u v) h
  have hex : ∃ x, IsGreatest ((fun l : List E => (l.map d).sum) '' {l | IsArcWalk tail head u v l})
      x := ⟨_, ⟨l₀, hl₀, rfl⟩, by rintro _ ⟨l, hl, rfl⟩; exact hmax l hl⟩
  rw [longestDuration, dite_eq_left hex]
  exact hex.choose_spec

theorem sum_map_le_longestDuration [Finite E]
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) {u v : V} {l : List E}
    (hl : IsArcWalk tail head u v l) : (l.map d).sum ≤ longestDuration tail head d u v :=
  (isGreatest_longestDuration hacyc ⟨l, hl⟩).2 ⟨l, hl, rfl⟩

theorem exists_sum_map_eq_longestDuration [Finite E]
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) {u v : V}
    (h : ∃ l, IsArcWalk tail head u v l) :
    ∃ l, IsArcWalk tail head u v l ∧ (l.map d).sum = longestDuration tail head d u v := by
  obtain ⟨l, hl, heq⟩ := (isGreatest_longestDuration (d := d) hacyc h).1
  exact ⟨l, hl, heq⟩

theorem longestDuration_self [Finite E]
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) (u : V) :
    longestDuration tail head d u u = 0 := by
  obtain ⟨l, hl, heq⟩ := exists_sum_map_eq_longestDuration (d := d) hacyc ⟨[], walk_nil⟩
  rw [← heq, hacyc u l hl]
  simp

end Walks

/-- **Slack and the critical path of a project network.** Let `tail head : E → V` be an
activity-on-arc network with finitely many arcs, arc durations `d : E → R` in a linearly ordered
additive commutative group, of any sign, and no nonempty closed walk, and let `s t : V` be such
that every event `v` lies on a walk from `s` to `t`: some walk runs from `s` to `v` and some walk
from `v` to `t`. Write `ℓ = longestDuration tail head d`, `L = ℓ s t`,
`ES = earliestStart tail head d s`, `LS = latestStart tail head d s t` and
`TF = totalFloat tail head d s t`. Then:

* `ℓ u v` is the greatest duration of a walk from `u` to `v` whenever some walk runs from `u`
  to `v`;
* `L` is the least project duration `τ t - τ s` of an event schedule `τ : V → R` meeting every
  arc's duration, `τ (tail e) + d e ≤ τ (head e)` for every arc `e`; for durations of any sign
  such a schedule may put events before `τ s`;
* if every duration is nonnegative, every event of an event schedule lies between `τ s` and
  `τ t`, and `L` is also the least `τ t` over event schedules with `τ s = 0` and `0 ≤ τ v` for
  every event `v` (no event before the start), as in the linear-programming formulation of the
  minimum project duration;
* every event `v` has slack `LS v - ES v ≥ 0`, with equality exactly when some walk of duration
  `L` from `s` to `t` passes through `v`, that is, is a walk from `s` to `v` followed by a walk
  from `v` to `t`;
* every arc `e` has total float `TF e ≥ 0`, with equality exactly when `e` is an arc of some walk
  of duration `L` from `s` to `t`. -/
theorem critical_path_slack [IsOrderedAddMonoid R] [Finite E] {tail head : E → V} {d : E → R}
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = []) {s t : V}
    (hcover : ∀ v, (∃ l, IsArcWalk tail head s v l) ∧ ∃ l, IsArcWalk tail head v t l) :
    (∀ u v, (∃ l, IsArcWalk tail head u v l) →
      IsGreatest ((fun l : List E => (l.map d).sum) '' {l | IsArcWalk tail head u v l})
        (longestDuration tail head d u v)) ∧
    IsLeast {x | ∃ τ : V → R, (∀ e, τ (tail e) + d e ≤ τ (head e)) ∧ τ t - τ s = x}
      (longestDuration tail head d s t) ∧
    ((∀ e, 0 ≤ d e) →
      (∀ τ : V → R, (∀ e, τ (tail e) + d e ≤ τ (head e)) → ∀ v, τ s ≤ τ v ∧ τ v ≤ τ t) ∧
      IsLeast {x | ∃ τ : V → R, (∀ e, τ (tail e) + d e ≤ τ (head e)) ∧ τ s = 0 ∧
        (∀ v, 0 ≤ τ v) ∧ τ t = x} (longestDuration tail head d s t)) ∧
    (∀ v, 0 ≤ latestStart tail head d s t v - earliestStart tail head d s v) ∧
    (∀ v, latestStart tail head d s t v - earliestStart tail head d s v = 0 ↔
      ∃ l₁ l₂, IsArcWalk tail head s v l₁ ∧ IsArcWalk tail head v t l₂ ∧
        ((l₁ ++ l₂).map d).sum = longestDuration tail head d s t) ∧
    (∀ e, 0 ≤ totalFloat tail head d s t e) ∧
    (∀ e, totalFloat tail head d s t e = 0 ↔
      ∃ l, IsArcWalk tail head s t l ∧ (l.map d).sum = longestDuration tail head d s t ∧
        e ∈ l) := by
  refine ⟨fun u v h => isGreatest_longestDuration hacyc h, ?_⟩
  have hle : ∀ {u v : V} {l : List E}, IsArcWalk tail head u v l →
      (l.map d).sum ≤ longestDuration tail head d u v :=
    fun hl => sum_map_le_longestDuration hacyc hl
  have hfrom : ∀ v, ∃ l, IsArcWalk tail head s v l ∧
      (l.map d).sum = longestDuration tail head d s v :=
    fun v => exists_sum_map_eq_longestDuration hacyc (hcover v).1
  have hto : ∀ v, ∃ l, IsArcWalk tail head v t l ∧
      (l.map d).sum = longestDuration tail head d v t :=
    fun v => exists_sum_map_eq_longestDuration hacyc (hcover v).2
  have hself : longestDuration tail head d s s = 0 := longestDuration_self hacyc s
  simp only [totalFloat, latestStart, earliestStart]
  generalize longestDuration tail head d = ℓ at hle hfrom hto hself ⊢
  -- The slack of an event and the float of an arc, as bounds on walk durations.
  have hslack : ∀ v, ℓ s t - ℓ v t - ℓ s v = ℓ s t - (ℓ s v + ℓ v t) := fun v => by abel
  have hfloat : ∀ e, ℓ s t - ℓ (head e) t - ℓ s (tail e) - d e =
      ℓ s t - (ℓ s (tail e) + d e + ℓ (head e) t) := fun e => by abel
  have hvertex : ∀ v, ℓ s v + ℓ v t ≤ ℓ s t := fun v => by
    obtain ⟨l₁, h₁, e₁⟩ := hfrom v
    obtain ⟨l₂, h₂, e₂⟩ := hto v
    have := hle (walk_append_mk h₁ h₂)
    rwa [List.map_append, List.sum_append, e₁, e₂] at this
  have harc : ∀ e, ℓ s (tail e) + d e + ℓ (head e) t ≤ ℓ s t := fun e => by
    obtain ⟨l₁, h₁, e₁⟩ := hfrom (tail e)
    obtain ⟨l₂, h₂, e₂⟩ := hto (head e)
    have := hle (walk_append_mk h₁ (walk_cons_mk rfl h₂))
    rwa [List.map_append, List.sum_append, List.map_cons, List.sum_cons, e₁, e₂,
      ← add_assoc] at this
  -- The earliest starts meet every arc's duration.
  have hES : ∀ e, ℓ s (tail e) + d e ≤ ℓ s (head e) := fun e => by
    obtain ⟨l, hl, hsum⟩ := hfrom (tail e)
    have := hle (walk_snoc hl rfl)
    rwa [List.map_append, List.sum_append, hsum, List.map_singleton, List.sum_singleton] at this
  -- No event schedule meeting every arc's duration is shorter than `L`.
  have hlower : ∀ τ : V → R, (∀ e, τ (tail e) + d e ≤ τ (head e)) → ℓ s t ≤ τ t - τ s :=
    fun τ hτ => by
      obtain ⟨l, hl, hsum⟩ := hfrom t
      have := add_sum_map_le_of_forall_add_le hτ hl
      rw [hsum] at this
      exact le_sub_iff_add_le'.2 this
  refine ⟨⟨⟨fun v => ℓ s v, hES, by simp only [hself, sub_zero]⟩,
    by rintro _ ⟨τ, hτ, rfl⟩; exact hlower τ hτ⟩, fun hd => ?_, fun v => ?_,
    fun v => ⟨fun h0 => ?_, ?_⟩, fun e => ?_, fun e => ⟨fun h0 => ?_, ?_⟩⟩
  · -- With nonnegative durations every event of a schedule lies between the source and the sink.
    have hsum : ∀ l : List E, 0 ≤ (l.map d).sum := fun l =>
      List.sum_nonneg fun x hx => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
        exact hd e
    have hbetween : ∀ τ : V → R, (∀ e, τ (tail e) + d e ≤ τ (head e)) →
        ∀ v, τ s ≤ τ v ∧ τ v ≤ τ t := fun τ hτ v => by
      obtain ⟨l₁, h₁⟩ := (hcover v).1
      obtain ⟨l₂, h₂⟩ := (hcover v).2
      exact ⟨(le_add_of_nonneg_right (hsum l₁)).trans (add_sum_map_le_of_forall_add_le hτ h₁),
        (le_add_of_nonneg_right (hsum l₂)).trans (add_sum_map_le_of_forall_add_le hτ h₂)⟩
    refine ⟨hbetween, ⟨⟨fun v => ℓ s v, hES, hself, fun v => ?_, rfl⟩, ?_⟩⟩
    · rw [← hself]
      exact (hbetween _ hES v).1
    · rintro _ ⟨τ, hτ, h0, -, rfl⟩
      simpa [h0] using hlower τ hτ
  · rw [hslack, sub_nonneg]
    exact hvertex v
  · rw [hslack, sub_eq_zero] at h0
    obtain ⟨l₁, h₁, e₁⟩ := hfrom v
    obtain ⟨l₂, h₂, e₂⟩ := hto v
    exact ⟨l₁, l₂, h₁, h₂, by rw [List.map_append, List.sum_append, e₁, e₂, h0]⟩
  · rintro ⟨l₁, l₂, h₁, h₂, hsum⟩
    rw [List.map_append, List.sum_append] at hsum
    rw [hslack, sub_eq_zero]
    refine le_antisymm ?_ (hvertex v)
    rw [← hsum]
    exact add_le_add (hle h₁) (hle h₂)
  · rw [hfloat, sub_nonneg]
    exact harc e
  · rw [hfloat, sub_eq_zero] at h0
    obtain ⟨l₁, h₁, e₁⟩ := hfrom (tail e)
    obtain ⟨l₂, h₂, e₂⟩ := hto (head e)
    refine ⟨l₁ ++ e :: l₂, walk_append_mk h₁ (walk_cons_mk rfl h₂), ?_, by simp⟩
    rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, e₁, e₂, h0, add_assoc]
  · rintro ⟨l, hl, hsum, hmem⟩
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
    obtain ⟨m, h₁, h₂⟩ := walk_append hl
    obtain ⟨hm, h₂⟩ := walk_cons_pair h₂
    rw [← hm] at h₁
    rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hsum
    rw [hfloat, sub_eq_zero]
    refine le_antisymm ?_ (harc e)
    rw [← hsum, add_assoc]
    exact add_le_add (hle h₁) (add_le_add le_rfl (hle h₂))

/-- **Zero slack at both endpoints does not make an activity critical.** In the project network
with events `0` (the source `s`), `1` and `2` (the sink `t`) and arcs `s → t`, `s → 1` and
`1 → t` (arcs `0`, `1` and `2`), each of real duration `1`, the endpoints `s` and `t` of the arc
`s → t` both have slack `LS - ES = 0` (`latestStart`, `earliestStart`), but the total float
(`totalFloat`) of the arc `s → t` is `1`, not `0`. -/
theorem slack_eq_zero_totalFloat_eq_one :
    latestStart (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 0 -
        earliestStart (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 0 =
      0 ∧
    latestStart (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 2 -
        earliestStart (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 =
      0 ∧
    totalFloat (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 0 = 1 := by
  -- The event times `0, 1, 2` meet every arc's duration, so every walk from `u` to `v` has at
  -- most `v - u` arcs.
  have hτ : ∀ e : Fin 3, (((![0, 0, 1] : Fin 3 → Fin 3) e : ℕ) : ℝ) + 1 ≤
      (((![2, 1, 2] : Fin 3 → Fin 3) e : ℕ) : ℝ) := by
    intro e
    fin_cases e <;> norm_num
  have hwalk : ∀ {u v : Fin 3} {l : List (Fin 3)},
      IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] u v l →
        ((u : ℕ) : ℝ) + l.length ≤ ((v : ℕ) : ℝ) := fun hl => by
    simpa using add_sum_map_le_of_forall_add_le (τ := fun v : Fin 3 => ((v : ℕ) : ℝ))
      (d := fun _ : Fin 3 => (1 : ℝ)) hτ hl
  have hacyc : ∀ v (l : List (Fin 3)),
      IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] v v l → l = [] := by
    intro v l hl
    have h := (add_le_iff_nonpos_right _).1 (hwalk hl)
    exact List.eq_nil_of_length_eq_zero (Nat.cast_nonpos.1 h)
  have hst :
      longestDuration (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 =
        2 := by
    have h12 : IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] 0 2 [1, 2] :=
      walk_cons_mk rfl (walk_cons_mk rfl walk_nil)
    refine (isGreatest_longestDuration hacyc ⟨_, h12⟩).unique ⟨⟨_, h12, by norm_num⟩, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    simpa using hwalk hl
  refine ⟨?_, ?_, ?_⟩
  · simp [latestStart, earliestStart, longestDuration_self hacyc]
  · simp [latestStart, earliestStart, longestDuration_self hacyc]
  · simp [totalFloat, latestStart, earliestStart, longestDuration_self hacyc, hst]
    norm_num

end Cslib.Scheduling.ProjectNetwork
