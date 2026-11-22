/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress
import CSLibExt.Languages.PiCalculus.Behavioural

/-!
# Direct runtime deadlock rejection

The literal terms are the public CyclicTests/SelfWaitTests source fixtures.
Their module-private constants are not imported, copied into a new foundation,
or used to infer runtime impossibility from finite impossibility.
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeDeadlockTests

open PiCalculus Endpoint.Runtime

/-- The canonical cyclic wait is rejected by actual Runtime typing in EVERY
semantically balanced ownership interface, at every ambient depth/rank assignment. -/
theorem cyclic_runtime_rejected {n : Nat} {Δ : Context} (hb : Conversion.Balanced Δ) :
    ¬ Runtime.HasType n ∅ Δ
      (.par (.inp (.const 0) (.out (.const 1) (.const 7) .nil))
        (.inp (.const 1) (.out (.const 0) (.const 7) .nil))) := by
  intro ht
  rcases ht.progress_balanced hb (by intro s sig hs; simp at hs) with hi | ⟨q, hs⟩
  · obtain ⟨s, hn, hm⟩ := hi.1
    exact Finmap.notMem_empty hm
  · exact not_step_of_no_output (by simp [PiCalculus.HasUnguardedOutput]) q hs

/-- Actual literal private-pair ownership rejects the same-physical opposite-role
self-wait for ANY capability/rank, including c and c.dual (both orientations). -/
theorem private_self_wait_runtime_rejected (n : Nat) (c : Capability) :
    ¬ Runtime.HasType (n + 1) ∅ (Context.bind c ∅)
      (.inp (.var 0) (.out (.var 1) (.const 7) .nil)) := by
  intro ht
  rcases ht.progress_balanced (Conversion.balanced_empty.bind c)
    (by intro s sig hs; simp at hs) with hi | ⟨q, hs⟩
  · obtain ⟨s, hn, hm⟩ := hi
    cases hn
  · exact not_step_of_no_output (by simp [PiCalculus.HasUnguardedOutput]) q hs

/-- The real closed two-channel cyclic wait has no runtime derivation, not just
no finite-ranked derivation. Input binders shift the later subjects canonically. -/
theorem closed_cycle_runtime_rejected (n : Nat) : ¬ Runtime.HasType n ∅ ∅
    (.nu (.nu (.par (.inp (.var 0) (.out (.var 2) (.const 7) .nil))
      (.inp (.var 1) (.out (.var 1) (.const 7) .nil))))) := by
  intro ht
  rcases ht.progress_empty (by intro s sig hs; simp at hs) with hi | ⟨q, hs⟩
  · obtain ⟨s, hn, hm⟩ := hi.1
    cases hn
  · exact not_step_of_no_output (by simp [PiCalculus.HasUnguardedOutput]) q hs

/-- Inert !nil and !(νnil) are actual typed Idle states, have no canonical Step,
and are NOT Cong nil. GENERAL progress selects Idle, not linear completion alone. -/
theorem inert_replicas_runtime_idle (n : Nat) :
    ∀ p ∈ ([Proc.repl .nil, Proc.repl (.nu .nil)] : List Proc),
      Runtime.HasType n ∅ ∅ p ∧ Idle ∅ p ∧ (∀ q, ¬ PiCalculus.Step p q) ∧ ¬ Cong p .nil := by
  have hn := nil_typed n (∅ : ServiceEnv)
  have hs : ∀ e ∈ (∅ : Context), e.name.ClosedAt n :=
    fun _ he => False.elim (Finmap.notMem_empty he)
  have h0 := Runtime.HasType.serve (show ServiceTemplate ∅ Proc.nil from trivial)
    hn Context.completed_empty hs (separated_empty _)
  have h1 := Runtime.HasType.serve (show ServiceTemplate ∅ (Proc.nu .nil) from trivial)
    hn.nu_nil_intro Context.completed_empty hs (separated_empty _)
  intro p hp
  have ht : Runtime.HasType n ∅ ∅ p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h0
    · exact h1
  have hi : Idle ∅ p := by
    rcases ht.progress_empty (by intro s sig hs; simp at hs) with hi | ⟨q, hq⟩
    · exact hi
    · have hid : Idle ∅ p := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> trivial
      exact False.elim (hid.no_step q hq)
  refine ⟨ht, hi, hi.no_step, ?_⟩
  intro hc
  have hf := (finiteLinear_cong hc).mpr (show FiniteLinear Proc.nil from trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact hf

end Cslib.SessionTypes.Endpoint.RuntimeDeadlockTests
