/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.CongTyping
import CSLibExt.Languages.SessionTypes.Endpoint.RankedCong

/-!
# Populated consumers of full canonical structural typing transport

The bound guard fixture follows the same-repository Endpoint/BoundTests
pattern. No alternative syntax or congruence closure typing rule is used.
-/

namespace Cslib.SessionTypes.Endpoint.CongTypingTests

open PiCalculus

def sending : Capability := ⟨2, .sendName .done⟩
def boundBody : Proc := .par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)

/-- A live output and input on the two roles of the actual bound name. -/
theorem live_bound_typed : HasType 0 ∅ (.nu boundBody) := by
  apply HasType.nu (c := sending)
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply HasType.outName (e := ⟨.var 0, .positive⟩) (c := sending) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact HasType.nil_singleton (Nat.zero_lt_succ 0)
  · apply HasType.inpName (e := ⟨.var 0, .negative⟩) (c := sending.dual) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact HasType.nil_singleton (by change 1 < 2; decide)

def idlePair : Capability := ⟨9, .done⟩
def nested : Proc := .nu (.nu boundBody)

/-- An idle outer pair and a live inner pair give distinct protocols to swap. -/
theorem nested_typed : HasType 0 ∅ nested := by
  have hl : HasType 1 ∅ (.nu boundBody) := by
    simpa only [Context.lift_empty, liftProc, boundBody, liftName, Nat.reduceAdd,
      Nat.reduceLeDiff, ↓reduceIte] using live_bound_typed.lift 0
  have hp := hl.weaken_completed (z := ⟨.var 0, .positive⟩)
    (u := idlePair) Finmap.notMem_empty rfl (Nat.zero_lt_succ 0)
  have hn := hp.weaken_completed (z := ⟨.var 0, .negative⟩)
    (u := idlePair.dual) (by
      intro he
      rcases Finmap.mem_insert.mp he with he | he
      · cases he
      · exact Finmap.notMem_empty he) rfl (Nat.zero_lt_succ 0)
  exact HasType.nu (c := idlePair) hn

/-- The generic congruence theorem swaps the live inner and idle outer pair. -/
theorem nested_swap_typed : HasType 0 ∅ (.nu (.nu (swapProc 0 boundBody))) :=
  (HasType.cong_iff (Cong.nu_swap boundBody)).mp nested_typed

/-- The same generic theorem handles the reverse constructor direction. -/
theorem nested_swap_back_typed : HasType 0 ∅ nested :=
  (HasType.cong_iff (Cong.symm (Cong.nu_swap boundBody))).mp nested_swap_typed

def outer : Key := ⟨.const 4, .positive⟩
def outerContext : Context := Finmap.singleton outer sending
def prefixed : Proc := .out outer.name (.const 6) nested

/-- A nonempty outer subject guards the nested restricted live network. -/
theorem prefixed_typed : HasType 0 outerContext prefixed := by
  apply HasType.outName (e := outer) (c := sending) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [outerContext, Finmap.insert_singleton_eq]
    have ht := nested_typed.weaken_completed (z := outer) (u := ⟨sending.rank, .done⟩)
      Finmap.notMem_empty rfl trivial
    have heq : (∅ : Context).insert outer ⟨sending.rank, .done⟩ =
        Finmap.singleton outer ⟨sending.rank, .done⟩ := by
      apply Finmap.ext
      rfl
    rw [heq] at ht
    exact ht

/-- Full congruence induction transports a nested swap under a real prefix. -/
theorem swap_under_output_typed :
    HasType 0 outerContext (.out outer.name (.const 6) (.nu (.nu (swapProc 0 boundBody)))) :=
  (HasType.cong_iff (Cong.out_cong _ _ (Cong.nu_swap boundBody))).mp prefixed_typed

/-- A composed congruence enters both restrictions, introduces nil, then
uses reverse scope beneath a live output prefix with nonempty ownership. -/
theorem reverse_scope_under_output_typed :
    HasType 0 outerContext (.out outer.name (.const 6) (.nu (.par (.nu boundBody) .nil))) := by
  have hc : Cong nested (.nu (.par (.nu boundBody) .nil)) :=
    Cong.trans (Cong.nu_cong (Cong.nu_cong (Cong.symm (Cong.par_nil boundBody))))
      (Cong.nu_cong (Cong.symm (Cong.scope boundBody .nil)))
  exact (HasType.cong_iff (Cong.out_cong _ _ hc)).mp prefixed_typed

/-- Congruence cannot hide replication inside its folded or unfolded form. -/
theorem unfolded_replication_typing_rejected {n : Nat} {Δ : Context} :
    ¬ HasType n Δ (.par (.nu boundBody) (.repl (.nu boundBody))) := by
  intro h
  have hr := (HasType.cong_iff (Cong.repl_unfold (.nu boundBody))).mpr h
  exact hr.finiteLinear

/-- Even arbitrary further canonical congruence cannot make choice typable. -/
theorem congruent_sum_typing_rejected {n : Nat} {Δ : Context} {q : Proc}
    (hc : Cong (.sum (.nu boundBody) .nil) q) : ¬ HasType n Δ q := by
  intro h
  exact ((HasType.cong_iff hc).mpr h).finiteLinear

def threadKey (i : Nat) : Key := ⟨.const i, .positive⟩
def threadContext (i : Nat) : Context := Finmap.singleton (threadKey i) sending
def thread (i : Nat) : Proc := .out (.const i) (.const 7) .nil

private theorem thread_typed (i : Nat) : HasType 0 (threadContext i) (thread i) := by
  apply HasType.outName (e := threadKey i) (c := sending) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [threadContext, Finmap.insert_singleton_eq]
    exact HasType.nil_singleton trivial

/-- Reassociation is exercised on three active, distinct subject capabilities. -/
theorem three_active_associated :
    HasType 0 ((threadContext 4 ∪ threadContext 5) ∪ threadContext 6)
      (.par (thread 4) (.par (thread 5) (thread 6))) := by
  have h45 : Finmap.Disjoint (threadContext 4) (threadContext 5) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, threadContext, threadKey]
  have h456 : Finmap.Disjoint (threadContext 4 ∪ threadContext 5) (threadContext 6) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, Finmap.mem_union, threadContext, threadKey]
  have ht := HasType.par h456 (HasType.par h45 (thread_typed 4) (thread_typed 5))
    (thread_typed 6)
  exact (HasType.cong_iff (Cong.par_assoc (thread 4) (thread 5) (thread 6))).mp ht

/-- The original live fixture has ranked singleton guards, not a bare
HasType witness silently promoted to refined typing. -/
theorem live_bound_ranked : RankedType 0 ∅ (.nu boundBody) := by
  apply RankedType.nu (c := sending)
  rw [Context.bind_empty]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply RankedType.outName (e := ⟨.var 0, .positive⟩) (c := sending) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  · apply RankedType.inpName (e := ⟨.var 0, .negative⟩) (c := sending.dual) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 2; decide))

/-- Refined completed weakening installs the distinct idle rank9 outer pair. -/
theorem nested_ranked : RankedType 0 ∅ nested := by
  have hl : RankedType 1 ∅ (.nu boundBody) := by
    simpa only [Context.lift_empty, liftProc, boundBody, liftName, Nat.reduceAdd,
      Nat.reduceLeDiff, ↓reduceIte] using live_bound_ranked.lift 0
  have hp := hl.weaken_completed (z := ⟨.var 0, .positive⟩) (u := idlePair)
    Finmap.notMem_empty rfl (Nat.zero_lt_succ 0)
  have hn := hp.weaken_completed (z := ⟨.var 0, .negative⟩) (u := idlePair.dual) (by
    intro he
    rcases Finmap.mem_insert.mp he with he | he
    · cases he
    · exact Finmap.notMem_empty he) rfl (Nat.zero_lt_succ 0)
  exact RankedType.nu (c := idlePair) hn

/-- GENERAL ranked Cong transport exchanges the distinct live/idle pairs. -/
theorem nested_swap_ranked : RankedType 0 ∅ (.nu (.nu (swapProc 0 boundBody))) :=
  (RankedType.cong_iff (Cong.nu_swap boundBody)).mp nested_ranked

/-- The nested fixture sits behind an actual rank2 output subject; the
only other ownership reattached to its continuation is completed. -/
theorem prefixed_ranked : RankedType 0 outerContext prefixed := by
  apply RankedType.outName (e := outer) (c := sending) (s := .done)
  · exact guardMin_singleton _ _
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [outerContext, Finmap.insert_singleton_eq]
    have ht := nested_ranked.weaken_completed (z := outer) (u := ⟨sending.rank, .done⟩)
      Finmap.notMem_empty rfl trivial
    have he : (∅ : Context).insert outer ⟨sending.rank, .done⟩ =
        Finmap.singleton outer ⟨sending.rank, .done⟩ := by apply Finmap.ext; rfl
    rw [he] at ht
    exact ht

/-- GENERAL ranked prefix congruence transports all internal guard constraints. -/
theorem swapped_prefix_ranked : RankedType 0 outerContext
    (.out outer.name (.const 6) (.nu (.nu (swapProc 0 boundBody)))) :=
  (RankedType.cong_iff (Cong.out_cong _ _ (Cong.nu_swap boundBody))).mp prefixed_ranked

/-- Composition and reverse scope work under the same nonempty active prefix. -/
theorem reverse_scoped_prefix_ranked : RankedType 0 outerContext
    (.out outer.name (.const 6) (.nu (.par (.nu boundBody) .nil))) := by
  have hc : Cong nested (.nu (.par (.nu boundBody) .nil)) :=
    Cong.trans (Cong.nu_cong (Cong.nu_cong (Cong.symm (Cong.par_nil boundBody))))
      (Cong.nu_cong (Cong.symm (Cong.scope boundBody .nil)))
  exact (RankedType.cong_iff (Cong.out_cong _ _ hc)).mp prefixed_ranked

private theorem thread_ranked (i : Nat) : RankedType 0 (threadContext i) (thread i) := by
  apply RankedType.outName (e := threadKey i) (c := sending) (s := .done)
  · exact guardMin_singleton _ _
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [threadContext, Finmap.insert_singleton_eq]
    exact RankedType.nil_of_hasType (HasType.nil_singleton trivial)

/-- Three actual active contexts retain their ranked subthreads after reassociation. -/
theorem three_active_ranked_associated :
    RankedType 0 ((threadContext 4 ∪ threadContext 5) ∪ threadContext 6)
      (.par (thread 4) (.par (thread 5) (thread 6))) := by
  have h45 : Finmap.Disjoint (threadContext 4) (threadContext 5) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, threadContext, threadKey]
  have h456 : Finmap.Disjoint (threadContext 4 ∪ threadContext 5) (threadContext 6) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, Finmap.mem_union, threadContext, threadKey]
  have ht := RankedType.par h456 (RankedType.par h45 (thread_ranked 4) (thread_ranked 5))
    (thread_ranked 6)
  exact (RankedType.cong_iff (Cong.par_assoc (thread 4) (thread 5) (thread 6))).mp ht

/-- Generic ranked Cong folding cannot create a typed replication body. -/
theorem unfolded_replication_ranked_rejected {n : Nat} {Δ : Context} :
    ¬ RankedType n Δ (.par (.nu boundBody) (.repl (.nu boundBody))) := by
  intro h
  have hr := (RankedType.cong_iff (Cong.repl_unfold (.nu boundBody))).mpr h
  exact hr.hasType.finiteLinear

/-- Generic ranked Cong transport also rules out any term congruent to this sum. -/
theorem congruent_sum_ranked_rejected {n : Nat} {Δ : Context} {q : Proc}
    (hc : Cong (.sum (.nu boundBody) .nil) q) : ¬ RankedType n Δ q := by
  intro h
  exact ((RankedType.cong_iff hc).mpr h).hasType.finiteLinear

end Cslib.SessionTypes.Endpoint.CongTypingTests
