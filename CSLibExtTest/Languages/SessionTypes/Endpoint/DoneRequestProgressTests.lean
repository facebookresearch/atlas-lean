/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress

/-! # A real DONE-payload request fires with ZERO active owned capabilities -/

namespace Cslib.SessionTypes.Endpoint.DoneRequestProgressTests

open PiCalculus Endpoint.Runtime

private def doneCap : Capability := ⟨7, .done⟩
private def sig : ServiceSignature := ⟨999, .positive, doneCap⟩
private def env : ServiceEnv := Finmap.singleton 710 sig
private def worker : Proc := .repl (.inp (.const 710) .nil)
private def network : Proc := .par (.out (.const 710) (.var 0) .nil) (.par worker .nil)
private def ownership : Context := Context.bind doneCap ∅

private theorem nil_done (e : Key) (he : e.name.ClosedAt 1)
    (hn : ∀ s v, env.lookup s = some v → e.name ≠ .const s) :
    Runtime.HasType 1 env (Finmap.singleton e doneCap) .nil := by
  apply Runtime.HasType.nil (Context.completed_empty.insert (by rfl))
  · intro x hx
    have hxe := (Finmap.mem_singleton _ _ _).mp hx
    subst x
    exact he
  · exact separated_singleton hn

private theorem worker_typed : Runtime.HasType 1 env ∅ worker := by
  apply Runtime.HasType.serve_input Finmap.lookup_singleton_eq
  · apply Runtime.HasType.nil (Context.completed_empty.insert (by rfl))
    · intro e he
      have heq := (Finmap.mem_singleton _ _ _).mp he
      subst e
      exact Nat.zero_lt_succ 1
    · exact separated_singleton (by intro s v hs hn; cases hn)
  · exact Context.completed_empty
  · intro e he
    exact False.elim (Finmap.notMem_empty he)
  · exact separated_empty env

private theorem request_typed : Runtime.HasType 1 env
    (Finmap.singleton ⟨.var 0, .positive⟩ doneCap) (.out (.const 710) (.var 0) .nil) := by
  apply Runtime.HasType.invoke (sig := sig) (e := ⟨.var 0, .positive⟩)
    (v := doneCap) Finmap.lookup_singleton_eq
  · exact separated_singleton (by intro s v hs hn; cases hn)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Capability.Equivalent.refl _
  · intro e c hc ha
    have heq := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst e
    rw [Finmap.lookup_singleton_eq] at hc
    cases hc
    exact False.elim (ha rfl)
  · exact Nat.zero_lt_succ 0
  · rw [erase_singleton]
    exact nil_typed 1 env

private theorem network_typed : Runtime.HasType 1 env ownership network := by
  have hpeer := nil_done ⟨.var 0, .negative⟩ (Nat.zero_lt_succ 0)
    (by intro s v hs hn; cases hn)
  have hr := Runtime.HasType.par (fun _ he _ => Finmap.notMem_empty he) worker_typed hpeer
  simp only [Finmap.empty_union] at hr
  have hp := Runtime.HasType.par (by simp [Finmap.Disjoint, Finmap.mem_singleton]) request_typed hr
  rw [ownership, Context.bind_empty]
  exact hp

private theorem network_available : Available env network := by
  intro s v hs
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hs)
  subst s
  exact Or.inr (Or.inl rfl)

private theorem ownership_done : ownership.Completed := by
  rw [ownership, Context.bind, Context.lift_empty]
  exact (Context.completed_empty.insert (by rfl)).insert (by rfl)

/-- GENERAL progress fires this request despite ZERO active owned keys and a
service priority999 exceeding payload rank7. InvocationPriority is vacuous ONLY
because actual unfolding is done, never by exempting the same payload key. -/
theorem done_payload_general_step :
    Runtime.HasType 1 env ownership network ∧ Conversion.Balanced ownership ∧
    Available env network ∧ ownership.Completed ∧ (sig.priority > doneCap.rank) ∧
    ∃ q, PiCalculus.Step network q := by
  have hb : Conversion.Balanced ownership := Conversion.balanced_empty.bind doneCap
  have hs : ∃ q, PiCalculus.Step network q := by
    rcases network_typed.progress_balanced hb network_available with hi | hs
    · exact False.elim
        (hi.no_unguarded_output (show HasUnguardedOutput network from Or.inl trivial))
    · exact hs
  exact ⟨network_typed, hb, network_available, ownership_done, by decide, hs⟩

end Cslib.SessionTypes.Endpoint.DoneRequestProgressTests
