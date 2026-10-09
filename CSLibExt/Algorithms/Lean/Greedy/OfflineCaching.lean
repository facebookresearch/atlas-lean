/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.List.MinMax

import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-!
# Finite offline caching

The furthest-in-future manager from CLRS, fourth edition, section 15.4, pages 440-445.
The finite request list supplies each resident's first strict-future occurrence;
absence is the top element of `WithTop Nat`. Canonical `List.argmax` chooses the
first maximal resident, so ties are deterministic in the saved cache order.

Legal competitors may permute cache representations, but cannot prefetch, discard
on a hit, or evict while space remains. Misses are counted from actual emitted
events, not a separate counter. Zero capacity emits a miss for every real request.
Invalid initial lists are outside the semantic hypotheses, not normalized.

This scan implementation does not establish preprocessing or RAM/word/bit cost.
Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.OfflineCaching

universe u

/-- One actual request, with an eviction only on a miss. -/
public inductive CacheEvent (α : Type u) where
  | hit (request : α)
  | miss (request : α) (evicted : Option α)
  deriving Repr, DecidableEq

/-- Source-legal transitions, independent of the order representing cache contents. -/
@[expose] public def cacheLTS {α : Type u} [DecidableEq α] (capacity : Nat) :
    Cslib.LTS (List α) (CacheEvent α) where
  Tr before event after := match event with
    | .hit request => request ∈ before ∧ after.Perm before
    | .miss request none => request ∉ before ∧
        ((capacity = 0 ∧ before = [] ∧ after = []) ∨
          (before.length < capacity ∧ after.Perm (request :: before)))
    | .miss request (some victim) =>
        0 < capacity ∧ request ∉ before ∧ before.length = capacity ∧
          victim ∈ before ∧ after.Perm (request :: before.erase victim)

@[no_expose] private def step {α : Type u} [DecidableEq α]
    (capacity : Nat) (request : α) (future cache : List α) : CacheEvent α × List α :=
  if request ∈ cache then (.hit request, cache)
  else if capacity = 0 then (.miss request none, [])
  else if cache.length < capacity then (.miss request none, request :: cache)
  else match List.argmax (β := WithTop Nat) (fun block => future.idxOf? block) cache with
    | some victim => (.miss request (some victim), request :: cache.erase victim)
    | none => (.miss request none, cache)

@[no_expose] private def run {α : Type u} [DecidableEq α] (capacity : Nat) :
    List α → List α → List (CacheEvent α) × List α
  | [], cache => ([], cache)
  | request :: future, cache =>
      let current := step capacity request future cache
      let suffix := run capacity future current.2
      (current.1 :: suffix.1, suffix.2)

/-- Scan the real requests and evict the first resident used furthest in the strict future. -/
public def furthestInFuture {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests initialCache : List α) : List (CacheEvent α) × List α :=
  run capacity requests initialCache

@[expose] public section

private theorem transition_valid {α : Type u} [DecidableEq α] {capacity : Nat}
    {before after : List α} {event : CacheEvent α}
    (hstep : (cacheLTS capacity).Tr before event after)
    (hnodup : before.Nodup) (hcapacity : before.length ≤ capacity) :
    after.Nodup ∧ after.length ≤ capacity := by
  cases event with
  | hit request =>
      rcases hstep with ⟨_, hperm⟩
      exact ⟨hnodup.perm hperm.symm, hperm.length_eq ▸ hcapacity⟩
  | miss request victim =>
      cases victim with
      | none =>
          rcases hstep with ⟨hmiss, hzero | hspare⟩
          · rcases hzero with ⟨_, _, rfl⟩
            simp
          · rcases hspare with ⟨hspace, hperm⟩
            have hnew : (request :: before).Nodup := List.nodup_cons.mpr ⟨hmiss, hnodup⟩
            exact ⟨hnew.perm hperm.symm, by rw [hperm.length_eq]; simp; omega⟩
      | some victim =>
          rcases hstep with ⟨hpositive, hmiss, hfull, hvictim, hperm⟩
          have hnew : (request :: before.erase victim).Nodup :=
            List.nodup_cons.mpr ⟨fun h => hmiss (List.mem_of_mem_erase h), hnodup.erase victim⟩
          refine ⟨hnew.perm hperm.symm, ?_⟩
          rw [hperm.length_eq, List.length_cons, List.length_erase_of_mem hvictim]
          omega

private theorem step_legal {α : Type u} [DecidableEq α]
    (capacity : Nat) (request : α) (future cache : List α)
    (hcapacity : cache.length ≤ capacity) :
    (cacheLTS capacity).Tr cache (step capacity request future cache).1
      (step capacity request future cache).2 := by
  by_cases hhit : request ∈ cache
  · simp [step, hhit, cacheLTS]
  by_cases hzero : capacity = 0
  · have hempty : cache = [] := List.length_eq_zero_iff.mp (by omega)
    simp [step, hzero, hempty, cacheLTS]
  by_cases hspare : cache.length < capacity
  · simp [step, hhit, hzero, hspare, cacheLTS]
  have hfull : cache.length = capacity := by omega
  cases hvictim : List.argmax (β := WithTop Nat)
      (fun block => future.idxOf? block) cache with
  | none =>
      have hempty : cache = [] := List.argmax_eq_none.mp hvictim
      simp [hempty] at hfull
      exact False.elim (hzero hfull.symm)
  | some victim =>
      have hmem : victim ∈ cache := List.argmax_mem (β := WithTop Nat)
        (f := fun block => future.idxOf? block) (by rw [hvictim]; simp)
      simp [step, hhit, hzero, hvictim, cacheLTS, hfull, hmem, Nat.pos_of_ne_zero hzero]

private theorem step_request {α : Type u} [DecidableEq α]
    (capacity : Nat) (request : α) (future cache : List α) :
    (match (step capacity request future cache).1 with
      | .hit r => r | .miss r _ => r) = request := by
  by_cases hhit : request ∈ cache
  · simp only [step, ite_eq_left hhit]
  by_cases hzero : capacity = 0
  · simp only [step, ite_eq_right hhit, ite_eq_left hzero]
  by_cases hspare : cache.length < capacity
  · simp only [step, ite_eq_right hhit, ite_eq_right hzero, ite_eq_left hspare]
  cases hvictim : List.argmax (β := WithTop Nat)
      (fun block => future.idxOf? block) cache <;>
    simp only [step, ite_eq_right hhit, ite_eq_right hzero, ite_eq_right hspare, hvictim]

private theorem run_legal {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests cache : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity) :
    (cacheLTS capacity).MTr cache (run capacity requests cache).1
      (run capacity requests cache).2 ∧
      (run capacity requests cache).1.map (fun event => match event with
        | .hit r => r | .miss r _ => r) = requests := by
  induction requests generalizing cache with
  | nil => exact ⟨.refl, rfl⟩
  | cons request future ih =>
      have hstep := step_legal capacity request future cache hcapacity
      have hvalid := transition_valid hstep hnodup hcapacity
      have hsuffix := ih (step capacity request future cache).2 hvalid.1 hvalid.2
      refine ⟨.stepL hstep hsuffix.1, ?_⟩
      simp only [run, List.map_cons, step_request, hsuffix.2]

private theorem run_zero {α : Type u} [DecidableEq α] (requests : List α) :
    run 0 requests [] = (requests.map (fun request => CacheEvent.miss request none), []) := by
  induction requests with
  | nil => rfl
  | cons request future ih => simp [run, step, ih]

private theorem run_nil {α : Type u} [DecidableEq α]
    (capacity : Nat) (initialCache : List α) :
    furthestInFuture capacity [] initialCache = ([], initialCache) := rfl

private theorem transition_perm {α : Type u} [DecidableEq α] {capacity : Nat}
    {before before' after after' : List α} {event : CacheEvent α}
    (hbefore : before'.Perm before) (hafter : after'.Perm after)
    (hstep : (cacheLTS capacity).Tr before event after) :
    (cacheLTS capacity).Tr before' event after' := by
  cases event with
  | hit request =>
      rcases hstep with ⟨hrequest, hperm⟩
      exact ⟨hbefore.mem_iff.mpr hrequest, hafter.trans (hperm.trans hbefore.symm)⟩
  | miss request victim =>
      cases victim with
      | none =>
          rcases hstep with ⟨hmiss, hzero | hspare⟩
          · rcases hzero with ⟨hcapacity, hbeforeNil, hafterNil⟩
            refine ⟨fun h => hmiss (hbefore.mem_iff.mp h), Or.inl ⟨hcapacity, ?_, ?_⟩⟩
            · exact List.length_eq_zero_iff.mp (by simpa [hbeforeNil] using hbefore.length_eq)
            · exact List.length_eq_zero_iff.mp (by simpa [hafterNil] using hafter.length_eq)
          · rcases hspare with ⟨hspace, hperm⟩
            refine ⟨fun h => hmiss (hbefore.mem_iff.mp h), Or.inr ⟨?_, ?_⟩⟩
            · rw [hbefore.length_eq]
              exact hspace
            · exact hafter.trans (hperm.trans (hbefore.symm.cons request))
      | some victim =>
          rcases hstep with ⟨hpositive, hmiss, hfull, hvictim, hperm⟩
          refine ⟨hpositive, fun h => hmiss (hbefore.mem_iff.mp h),
            hbefore.length_eq.trans hfull, hbefore.mem_iff.mpr hvictim, ?_⟩
          exact hafter.trans (hperm.trans ((hbefore.symm.erase victim).cons request))

private theorem trace_perm {α : Type u} [DecidableEq α] {capacity : Nat}
    {before before' after : List α} {events : List (CacheEvent α)}
    (hbefore : before'.Perm before) (htrace : (cacheLTS capacity).MTr before events after) :
    ∃ after', (cacheLTS capacity).MTr before' events after' ∧ after'.Perm after := by
  cases htrace with
  | refl => exact ⟨before', .refl, hbefore⟩
  | stepL hstep hsuffix =>
      exact ⟨_, .stepL (transition_perm hbefore (List.Perm.refl _) hstep) hsuffix,
        List.Perm.refl _⟩

@[no_expose] private def debt {α : Type u} [DecidableEq α]
    (requests : List α) (z y : α) : Nat :=
  @ite Nat (LT.lt (α := WithTop Nat) (requests.idxOf? z) (requests.idxOf? y))
    (LinearOrder.toDecidableLT (α := WithTop Nat) (requests.idxOf? z) (requests.idxOf? y)) 1 0


private theorem debt_le_one {α : Type u} [DecidableEq α]
    (requests : List α) (z y : α) : debt requests z y ≤ 1 := by
  unfold debt
  split <;> omega

private theorem debt_of_maximal {α : Type u} [DecidableEq α]
    (requests : List α) (z y : α)
    (hmax : LE.le (α := WithTop Nat) (requests.idxOf? y) (requests.idxOf? z)) :
    debt requests z y = 0 := by
  exact ite_eq_right (not_lt_of_ge (α := WithTop Nat) hmax)

private theorem debt_request_protected {α : Type u} [DecidableEq α]
    (future : List α) (z y : α) (hne : z ≠ y) : debt (z :: future) z y = 1 := by
  unfold debt
  rw [List.idxOf?_cons, List.idxOf?_cons]
  rw [ite_eq_left (show (z == z) = true from by simp),
    ite_eq_right (show ¬(z == y) = true from by simpa only [beq_iff_eq] using hne)]
  apply ite_eq_left
  cases hy : future.idxOf? y with
  | none =>
      change ((0 : Nat) : WithTop Nat) < ⊤
      exact WithTop.coe_lt_top _
  | some index =>
      change ((0 : Nat) : WithTop Nat) < (↑(index + 1) : WithTop Nat)
      exact WithTop.coe_lt_coe.mpr (Nat.zero_lt_succ _)

private theorem debt_request_other {α : Type u} [DecidableEq α]
    (future : List α) (request z y : α) (hz : request ≠ z) (hy : request ≠ y) :
    debt (request :: future) z y = debt future z y := by
  unfold debt
  rw [List.idxOf?_cons, List.idxOf?_cons]
  rw [ite_eq_right (show ¬(request == z) = true from by simpa only [beq_iff_eq] using hz),
    ite_eq_right (show ¬(request == y) = true from by simpa only [beq_iff_eq] using hy)]
  cases hzi : future.idxOf? z <;> cases hyi : future.idxOf? y
  · change (if (⊤ : WithTop Nat) < ⊤ then 1 else 0) =
      if (⊤ : WithTop Nat) < ⊤ then 1 else 0
    rfl
  · rename_i iy
    change (if (⊤ : WithTop Nat) < (↑(iy + 1) : WithTop Nat) then 1 else 0) =
      if (⊤ : WithTop Nat) < (↑iy : WithTop Nat) then 1 else 0
    simp
  · rename_i iz
    change (if (↑(iz + 1) : WithTop Nat) < ⊤ then 1 else 0) =
      if (↑iz : WithTop Nat) < ⊤ then 1 else 0
    simp
  · rename_i iz iy
    change (if (↑(iz + 1) : WithTop Nat) < (↑(iy + 1) : WithTop Nat) then 1 else 0) =
      if (↑iz : WithTop Nat) < (↑iy : WithTop Nat) then 1 else 0
    simp

private theorem common_update {α : Type u} [DecidableEq α]
    (common : List α) (request victim : α) (hnodup : common.Nodup)
    (hrequest : request ∉ common) (hvictim : victim ∈ common) :
    (request :: common.erase victim).Nodup ∧
      (request :: common.erase victim).length = common.length ∧
      victim ∉ request :: common.erase victim := by
  have hne : victim ≠ request := fun h => hrequest (h ▸ hvictim)
  refine ⟨List.nodup_cons.mpr
    ⟨fun h => hrequest (List.mem_of_mem_erase h), hnodup.erase victim⟩, ?_, ?_⟩
  · rw [List.length_cons, List.length_erase_of_mem hvictim]
    have hpositive : 0 < common.length := List.length_pos_of_mem hvictim
    omega
  · simp [hne, hnodup.not_mem_erase]

private theorem replace_common_perm {α : Type u} [DecidableEq α]
    (common : List α) (held request victim : α) (hne : held ≠ victim) :
    (held :: request :: common.erase victim).Perm
      (request :: (held :: common).erase victim) := by
  rw [List.erase_cons_tail (show ¬(held == victim) = true from
    fun h => hne (beq_iff_eq.mp h))]
  exact List.Perm.swap _ _ _

private theorem exchange_trace {α : Type u} [DecidableEq α]
    (capacity : Nat) (events : List (CacheEvent α)) (z y : α) (common final : List α)
    (hnodup : common.Nodup) (hz : z ∉ common) (hy : y ∉ common) (hne : z ≠ y)
    (hfull : (z :: common).length = capacity)
    (htrace : (cacheLTS capacity).MTr (z :: common) events final) :
    ∃ alternateEvents alternateFinal,
      (cacheLTS capacity).MTr (y :: common) alternateEvents alternateFinal ∧
      alternateEvents.map (fun event => match event with
        | .hit request => request | .miss request _ => request) =
        events.map (fun event => match event with
          | .hit request => request | .miss request _ => request) ∧
      alternateEvents.countP (fun event => match event with
        | .hit _ => false | .miss _ _ => true) ≤
        events.countP (fun event => match event with
          | .hit _ => false | .miss _ _ => true) +
          debt (events.map (fun event => match event with
            | .hit request => request | .miss request _ => request)) z y := by
  induction events generalizing z y common final with
  | nil => exact ⟨[], y :: common, .refl, rfl, Nat.zero_le _⟩
  | cons event events ih =>
      obtain ⟨after, hstep, hsuffix⟩ := Cslib.LTS.MTr.cons_iff.mp htrace
      have hpositive : 0 < capacity := by simpa only [List.length_cons] using
        (show 0 < common.length + 1 from Nat.zero_lt_succ _).trans_eq hfull
      cases event with
      | hit request =>
          rcases hstep with ⟨hrequest, hperm⟩
          by_cases hrequestz : request = z
          · subst request
            have halt : (cacheLTS capacity).Tr (y :: common) (.miss z (some y)) after :=
              ⟨hpositive, by simp [hne, hz], hfull, by simp,
                by simpa only [List.erase_cons_head] using hperm⟩
            refine ⟨.miss z (some y) :: events, final, .stepL halt hsuffix, rfl, ?_⟩
            have hdebt := debt_request_protected
              (events.map (fun event => match event with
                | .hit r => r | .miss r _ => r)) z y hne
            simp [hdebt]
          · have hrequestCommon : request ∈ common :=
              (List.mem_cons.mp hrequest).resolve_left hrequestz
            have hrequesty : request ≠ y := fun h => hy (h ▸ hrequestCommon)
            obtain ⟨normalizedFinal, hremaining, _⟩ := trace_perm hperm.symm hsuffix
            obtain ⟨alternateEvents, alternateFinal, halt, hmap, hcount⟩ :=
              ih z y common normalizedFinal hnodup hz hy hne hfull hremaining
            have hfirst : (cacheLTS capacity).Tr (y :: common) (.hit request) (y :: common) :=
              ⟨List.mem_cons_of_mem y hrequestCommon, List.Perm.refl _⟩
            refine ⟨.hit request :: alternateEvents, alternateFinal,
              .stepL hfirst halt, ?_, ?_⟩
            · simpa only [List.map_cons] using congrArg (List.cons request) hmap
            · have hdebt := debt_request_other
                (events.map (fun event => match event with
                  | .hit r => r | .miss r _ => r)) request z y hrequestz hrequesty
              simpa [List.countP_cons, hdebt] using hcount
      | miss request victim =>
          cases victim with
          | none =>
              rcases hstep with ⟨_, hzero | hspare⟩
              · omega
              · have := hspare.1
                omega
          | some victim =>
              rcases hstep with ⟨_, hmiss, _, hvictim, hperm⟩
              have hrequestz : request ≠ z := fun h => hmiss (by simp [h])
              have hrequestCommon : request ∉ common :=
                fun h => hmiss (List.mem_cons_of_mem z h)
              by_cases hvictimz : victim = z
              · subst victim
                by_cases hrequesty : request = y
                · subst request
                  have halt : (cacheLTS capacity).Tr (y :: common) (.hit y) after :=
                    ⟨by simp, by simpa only [List.erase_cons_head] using hperm⟩
                  refine ⟨.hit y :: events, final, .stepL halt hsuffix, rfl, ?_⟩
                  simp only [List.countP_cons, List.map_cons, Bool.false_eq_true, ↓reduceIte]
                  omega
                · have halt : (cacheLTS capacity).Tr (y :: common)
                      (.miss request (some y)) after :=
                    ⟨hpositive, by simp [hrequesty, hrequestCommon], hfull, by simp,
                      by simpa only [List.erase_cons_head] using hperm⟩
                  refine ⟨.miss request (some y) :: events, final,
                    .stepL halt hsuffix, rfl, ?_⟩
                  simp only [List.countP_cons, List.map_cons, ↓reduceIte]
                  omega
              · have hvictimCommon : victim ∈ common :=
                  (List.mem_cons.mp hvictim).resolve_left hvictimz
                have hupdate := common_update common request victim
                  hnodup hrequestCommon hvictimCommon
                have hznew : z ∉ request :: common.erase victim := by
                  simp only [List.mem_cons, not_or]
                  exact ⟨Ne.symm hrequestz, fun h => hz (List.mem_of_mem_erase h)⟩
                have hnewfull : (z :: request :: common.erase victim).length = capacity := by
                  simpa only [List.length_cons, hupdate.2.1] using hfull
                have hnormalize : (z :: request :: common.erase victim).Perm after :=
                  (replace_common_perm common z request victim (Ne.symm hvictimz)).trans hperm.symm
                obtain ⟨normalizedFinal, hremaining, _⟩ := trace_perm hnormalize hsuffix
                by_cases hrequesty : request = y
                · subst request
                  obtain ⟨alternateEvents, alternateFinal, halt, hmap, hcount⟩ :=
                    ih z victim (y :: common.erase victim) normalizedFinal
                      hupdate.1 hznew hupdate.2.2 (Ne.symm hvictimz) hnewfull hremaining
                  have hfirst : (cacheLTS capacity).Tr (y :: common) (.hit y)
                      (victim :: y :: common.erase victim) :=
                    ⟨by simp, (List.Perm.swap y victim _).trans
                      ((List.perm_cons_erase hvictimCommon).symm.cons y)⟩
                  refine ⟨.hit y :: alternateEvents, alternateFinal,
                    .stepL hfirst halt, ?_, ?_⟩
                  · simpa only [List.map_cons] using congrArg (List.cons y) hmap
                  · have hbound := debt_le_one
                      (events.map (fun event => match event with
                        | .hit r => r | .miss r _ => r)) z victim
                    simp only [List.countP_cons, List.map_cons, Bool.false_eq_true, ↓reduceIte]
                    omega
                · have hynew : y ∉ request :: common.erase victim := by
                    simp only [List.mem_cons, not_or]
                    exact ⟨Ne.symm hrequesty, fun h => hy (List.mem_of_mem_erase h)⟩
                  obtain ⟨alternateEvents, alternateFinal, halt, hmap, hcount⟩ :=
                    ih z y (request :: common.erase victim) normalizedFinal
                      hupdate.1 hznew hynew hne hnewfull hremaining
                  have hyvictim : y ≠ victim :=
                    fun h => hy (h.symm ▸ hvictimCommon)
                  have hfirst : (cacheLTS capacity).Tr (y :: common)
                      (.miss request (some victim)) (y :: request :: common.erase victim) :=
                    ⟨hpositive, by simp [hrequesty, hrequestCommon], hfull,
                      List.mem_cons_of_mem y hvictimCommon,
                      replace_common_perm common y request victim hyvictim⟩
                  refine ⟨.miss request (some victim) :: alternateEvents, alternateFinal,
                    .stepL hfirst halt, ?_, ?_⟩
                  · simpa only [List.map_cons] using congrArg (List.cons request) hmap
                  · have hdebt := debt_request_other
                      (events.map (fun event => match event with
                        | .hit r => r | .miss r _ => r)) request z y hrequestz hrequesty
                    simp only [List.countP_cons, List.map_cons, ↓reduceIte]
                    rw [hdebt]
                    omega

private theorem post_eviction {α : Type u} [DecidableEq α]
    (capacity : Nat) (cache : List α) (request z x : α)
    (hnodup : cache.Nodup) (hfull : cache.length = capacity)
    (hrequest : request ∉ cache) (hz : z ∈ cache) (hx : x ∈ cache) (hne : z ≠ x) :
    let common := request :: (cache.erase x).erase z
    common.Nodup ∧ z ∉ common ∧ x ∉ common ∧ (z :: common).length = capacity ∧
      (request :: cache.erase x).Perm (z :: common) ∧
      (request :: cache.erase z).Perm (x :: common) := by
  have hzErase : z ∈ cache.erase x := (hnodup.mem_erase_iff).mpr ⟨hne, hz⟩
  have hxErase : x ∈ cache.erase z := (hnodup.mem_erase_iff).mpr ⟨Ne.symm hne, hx⟩
  have hzRequest : z ≠ request := fun h => hrequest (h ▸ hz)
  have hxRequest : x ≠ request := fun h => hrequest (h ▸ hx)
  refine ⟨List.nodup_cons.mpr ⟨?_, (hnodup.erase x).erase z⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hrequest (List.mem_of_mem_erase (List.mem_of_mem_erase h))
  · simp [hzRequest, (hnodup.erase x).not_mem_erase]
  · simp only [List.mem_cons, not_or]
    exact ⟨hxRequest, fun h => hnodup.not_mem_erase (List.mem_of_mem_erase h)⟩
  · rw [List.length_cons, List.length_cons, List.length_erase_of_mem hzErase,
      List.length_erase_of_mem hx]
    have hpositive := List.length_pos_of_mem hzErase
    rw [List.length_erase_of_mem hx] at hpositive
    omega
  · exact (List.perm_cons_erase hzErase).cons request |>.trans (List.Perm.swap z request _)
  · rw [List.erase_comm x z]
    exact (List.perm_cons_erase hxErase).cons request |>.trans (List.Perm.swap x request _)

private theorem replacement_exchange {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests cache : List α) (request z x : α)
    (hnodup : cache.Nodup) (hfull : cache.length = capacity)
    (hrequest : request ∉ cache) (hx : x ∈ cache)
    (hselected : List.argmax (β := WithTop Nat) (fun block => requests.idxOf? block) cache =
      some z)
    (events : List (CacheEvent α)) (final : List α)
    (htrace : (cacheLTS capacity).MTr (request :: cache.erase x) events final)
    (hrequests : events.map (fun event => match event with
      | .hit r => r | .miss r _ => r) = requests) :
    ∃ alternateEvents alternateFinal,
      (cacheLTS capacity).MTr (request :: cache.erase z) alternateEvents alternateFinal ∧
      alternateEvents.map (fun event => match event with
        | .hit r => r | .miss r _ => r) = requests ∧
      alternateEvents.countP (fun event => match event with
        | .hit _ => false | .miss _ _ => true) ≤
        events.countP (fun event => match event with
          | .hit _ => false | .miss _ _ => true) := by
  by_cases heq : z = x
  · subst x
    exact ⟨events, final, htrace, hrequests, le_rfl⟩
  have hz : z ∈ cache := List.argmax_mem (β := WithTop Nat)
    (f := fun block => requests.idxOf? block) (by rw [hselected]; simp)
  obtain ⟨hcommon, hzcommon, hxcommon, hcommonfull, hcompetitor, halternate⟩ :=
    post_eviction capacity cache request z x hnodup hfull hrequest hz hx heq
  obtain ⟨normalizedFinal, hnormalized, _⟩ := trace_perm hcompetitor.symm htrace
  obtain ⟨alternateEvents, alternateFinal, hexchanged, hmap, hcount⟩ :=
    exchange_trace capacity events z x (request :: (cache.erase x).erase z) normalizedFinal
      hcommon hzcommon hxcommon heq hcommonfull hnormalized
  obtain ⟨savedFinal, hsaved, _⟩ := trace_perm halternate hexchanged
  have hmax := List.le_of_mem_argmax (β := WithTop Nat) (m := z)
    (f := fun block => requests.idxOf? block) hx (by rw [hselected]; simp)
  have hzero := debt_of_maximal requests z x hmax
  exact ⟨alternateEvents, savedFinal, hsaved, hmap.trans hrequests,
    by simpa only [hrequests, hzero, Nat.add_zero] using hcount⟩

private theorem run_cons {α : Type u} [DecidableEq α]
    (capacity : Nat) (request : α) (future cache : List α)
    (_hnodup : cache.Nodup) (_hcapacity : cache.length ≤ capacity) :
    (request ∈ cache →
      furthestInFuture capacity (request :: future) cache =
        (.hit request :: (furthestInFuture capacity future cache).1,
          (furthestInFuture capacity future cache).2)) ∧
    (capacity = 0 →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future []).1,
          (furthestInFuture capacity future []).2)) ∧
    (request ∉ cache → cache.length < capacity →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future (request :: cache)).1,
          (furthestInFuture capacity future (request :: cache)).2)) ∧
    (request ∉ cache → 0 < capacity → cache.length = capacity →
      ∀ victim, List.argmax (β := WithTop Nat) (fun block => future.idxOf? block) cache =
          some victim →
        furthestInFuture capacity (request :: future) cache =
          (.miss request (some victim) ::
            (furthestInFuture capacity future (request :: cache.erase victim)).1,
            (furthestInFuture capacity future (request :: cache.erase victim)).2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hhit
    simp only [furthestInFuture, run, step, ite_eq_left hhit]
  · intro hzero
    have hempty : cache = [] := List.length_eq_zero_iff.mp (by omega)
    simp [furthestInFuture, run, step, hzero, hempty]
  · intro hmiss hspare
    have hpositive : capacity ≠ 0 := by omega
    simp only [furthestInFuture, run, step, ite_eq_right hmiss,
      ite_eq_right hpositive, ite_eq_left hspare]
  · intro hmiss hpositive hfull victim hvictim
    have hnonzero : capacity ≠ 0 := by omega
    have hspare : ¬cache.length < capacity := by omega
    simp only [furthestInFuture, run, step, ite_eq_right hmiss,
      ite_eq_right hnonzero, ite_eq_right hspare, hvictim]

private theorem manager_legal {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests initialCache : List α)
    (hnodup : initialCache.Nodup) (hcapacity : initialCache.length ≤ capacity) :
    let output := furthestInFuture capacity requests initialCache
    (cacheLTS capacity).MTr initialCache output.1 output.2 ∧
      output.1.map (fun event => match event with
        | .hit request => request | .miss request _ => request) = requests ∧
      output.2.Nodup ∧ output.2.length ≤ capacity := by
  have htrace := run_legal capacity requests initialCache hnodup hcapacity
  have hvalid := Cslib.LTS.mtrInv_of_trInv
    (p := fun cache : List α => cache.Nodup ∧ cache.length ≤ capacity)
    (fun _ _ _ hstep hbefore => transition_valid hstep hbefore.1 hbefore.2)
    _ _ _ htrace.1 ⟨hnodup, hcapacity⟩
  exact ⟨htrace.1, htrace.2, hvalid⟩

private theorem manager_zero {α : Type u} [DecidableEq α] (requests : List α) :
    furthestInFuture 0 requests [] =
      (requests.map (fun request => CacheEvent.miss request none), []) :=
  run_zero requests

private theorem manager_min {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests cache : List α) (events : List (CacheEvent α)) (final : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity)
    (htrace : (cacheLTS capacity).MTr cache events final)
    (hrequests : events.map (fun event => match event with
      | .hit request => request | .miss request _ => request) = requests) :
    (furthestInFuture capacity requests cache).1.countP (fun event => match event with
      | .hit _ => false | .miss _ _ => true) ≤
      events.countP (fun event => match event with
        | .hit _ => false | .miss _ _ => true) := by
  induction requests generalizing cache events final with
  | nil => simp [furthestInFuture, run]
  | cons request future ih =>
      cases events with
      | nil => simp at hrequests
      | cons event events =>
          obtain ⟨after, hstep, hsuffix⟩ := Cslib.LTS.MTr.cons_iff.mp htrace
          cases event with
          | hit requested =>
              simp only [List.map_cons] at hrequests
              obtain ⟨rfl, htail⟩ := List.cons.inj hrequests
              rcases hstep with ⟨hrequest, hperm⟩
              obtain ⟨normalizedFinal, hnormalized, _⟩ := trace_perm hperm.symm hsuffix
              have hbound := ih cache events normalizedFinal hnodup hcapacity hnormalized htail
              rw [(run_cons capacity requested future cache hnodup hcapacity).1 hrequest]
              simpa [List.countP_cons] using hbound
          | miss requested victim =>
              simp only [List.map_cons] at hrequests
              obtain ⟨rfl, htail⟩ := List.cons.inj hrequests
              cases victim with
              | none =>
                  rcases hstep with ⟨hmiss, hzero | hspare⟩
                  · rcases hzero with ⟨rfl, rfl, rfl⟩
                    have hbound := ih [] events final (by simp) (by simp) hsuffix htail
                    rw [(run_cons 0 requested future [] (by simp) (by simp)).2.1 rfl]
                    simpa [List.countP_cons] using Nat.add_le_add_right hbound 1
                  · rcases hspare with ⟨hspare, hperm⟩
                    obtain ⟨normalizedFinal, hnormalized, _⟩ := trace_perm hperm.symm hsuffix
                    have hvalid : (requested :: cache).Nodup := List.nodup_cons.mpr ⟨hmiss, hnodup⟩
                    have hsize : (requested :: cache).length ≤ capacity := by
                      simp only [List.length_cons]
                      omega
                    have hbound := ih (requested :: cache) events normalizedFinal
                      hvalid hsize hnormalized htail
                    rw [(run_cons capacity requested future cache hnodup hcapacity).2.2.1
                      hmiss hspare]
                    simpa [List.countP_cons] using Nat.add_le_add_right hbound 1
              | some victim =>
                  rcases hstep with ⟨hpositive, hmiss, hfull, hvictim, hperm⟩
                  cases hselected : List.argmax (β := WithTop Nat)
                      (fun block => future.idxOf? block) cache with
                  | none =>
                      have hempty : cache = [] := List.argmax_eq_none.mp hselected
                      simp [hempty] at hfull
                      omega
                  | some selected =>
                      obtain ⟨normalizedFinal, hnormalized, _⟩ := trace_perm hperm.symm hsuffix
                      obtain ⟨alternateEvents, alternateFinal, halt, hmap, hcount⟩ :=
                        replacement_exchange capacity future cache requested selected victim
                          hnodup hfull hmiss hvictim hselected events normalizedFinal
                          hnormalized htail
                      have hresident : selected ∈ cache := List.argmax_mem (β := WithTop Nat)
                        (f := fun block => future.idxOf? block) (by rw [hselected]; simp)
                      have hfirst : (cacheLTS capacity).Tr cache (.miss requested (some selected))
                          (requested :: cache.erase selected) :=
                        ⟨hpositive, hmiss, hfull, hresident, List.Perm.refl _⟩
                      have hvalid := transition_valid hfirst hnodup hcapacity
                      have hbound := ih (requested :: cache.erase selected) alternateEvents
                        alternateFinal hvalid.1 hvalid.2 halt hmap
                      rw [(run_cons capacity requested future cache hnodup hcapacity).2.2.2
                        hmiss hpositive hfull selected hselected]
                      simpa [List.countP_cons] using Nat.add_le_add_right (hbound.trans hcount) 1

/-- An empty request list preserves the exact initial cache representation. -/
theorem furthestInFuture_nil {α : Type u} [DecidableEq α]
    (capacity : Nat) (initialCache : List α) :
    furthestInFuture capacity [] initialCache = ([], initialCache) :=
  run_nil capacity initialCache

/-- The four source branches, on the actual saved suffix result and valid initial cache. -/
theorem furthestInFuture_cons {α : Type u} [DecidableEq α]
    (capacity : Nat) (request : α) (future cache : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity) :
    (request ∈ cache →
      furthestInFuture capacity (request :: future) cache =
        (.hit request :: (furthestInFuture capacity future cache).1,
          (furthestInFuture capacity future cache).2)) ∧
    (capacity = 0 →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future []).1,
          (furthestInFuture capacity future []).2)) ∧
    (request ∉ cache → cache.length < capacity →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future (request :: cache)).1,
          (furthestInFuture capacity future (request :: cache)).2)) ∧
    (request ∉ cache → 0 < capacity → cache.length = capacity →
      ∀ victim, List.argmax (β := WithTop Nat) (fun block => future.idxOf? block) cache =
          some victim →
        furthestInFuture capacity (request :: future) cache =
          (.miss request (some victim) ::
            (furthestInFuture capacity future (request :: cache.erase victim)).1,
            (furthestInFuture capacity future (request :: cache.erase victim)).2)) :=
  run_cons capacity request future cache hnodup hcapacity

/-- The emitted events form a source-legal trace for exactly the input requests;
the saved final cache is duplicate-free and within capacity. -/
theorem furthestInFuture_legal {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests initialCache : List α)
    (hnodup : initialCache.Nodup) (hcapacity : initialCache.length ≤ capacity) :
    let output := furthestInFuture capacity requests initialCache
    (cacheLTS capacity).MTr initialCache output.1 output.2 ∧
      output.1.map (fun event => match event with
        | .hit request => request | .miss request _ => request) = requests ∧
      output.2.Nodup ∧ output.2.length ≤ capacity :=
  manager_legal capacity requests initialCache hnodup hcapacity

/-- With no storage, each real request produces exactly one miss and the cache stays empty. -/
theorem furthestInFuture_zero_capacity {α : Type u} [DecidableEq α] (requests : List α) :
    furthestInFuture 0 requests [] =
      (requests.map (fun request => CacheEvent.miss request none), []) :=
  manager_zero requests

/-- The actual manager emits no more misses than any source-legal trace on the same requests
from the same valid initial cache. Competitors may permute representations. -/
theorem furthestInFuture_min_misses {α : Type u} [DecidableEq α]
    (capacity : Nat) (requests initialCache : List α)
    (hnodup : initialCache.Nodup) (hcapacity : initialCache.length ≤ capacity)
    (events : List (CacheEvent α)) (finalCache : List α)
    (hlegal : (cacheLTS capacity).MTr initialCache events finalCache)
    (hrequests : events.map (fun event => match event with
      | .hit request => request | .miss request _ => request) = requests) :
    (furthestInFuture capacity requests initialCache).1.countP
      (fun event => match event with | .hit _ => false | .miss _ _ => true) ≤
      events.countP (fun event => match event with | .hit _ => false | .miss _ _ => true) :=
  manager_min capacity requests initialCache events finalCache hnodup hcapacity hlegal hrequests

end

end Cslib.Algorithms.Lean.OfflineCaching
