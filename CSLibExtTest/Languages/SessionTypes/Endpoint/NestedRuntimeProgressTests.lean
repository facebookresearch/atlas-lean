/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress

/-! # GENERAL progress with multiple, wrapped and nested persistent templates -/

namespace Cslib.SessionTypes.Endpoint.NestedRuntimeProgressTests

open PiCalculus Endpoint.Runtime

private def wrapped : Proc := .repl (.par (.inp (.const 710) (senderWorker (.var 0))) .nil)
private def nested : Proc := .repl (.par senderDaemon receiverDaemon)
private def extra : Proc := .par wrapped (.par nested (.nu (.nu .nil)))
private def network (i : Nat) : Proc := .par (phase (.var 0) i) extra

private theorem extra_typed (r : Role) : Runtime.HasType 1 (services r) ∅ extra := by
  have hw : Runtime.HasType 1 (services r) ∅ wrapped :=
    (Runtime.HasType.cong_iff (.repl_cong (Cong.par_nil _).symm)).mp (sender_daemon_typed 1 r)
  have hb := Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context))
    (sender_daemon_typed 1 r) (receiver_daemon_typed 1 r)
  simp only [Finmap.union_empty] at hb
  have hn : Runtime.HasType 1 (services r) ∅ nested := Runtime.HasType.serve
    ⟨⟨710, rfl, Finmap.mem_of_lookup_eq_some (sender_declared r)⟩,
      ⟨711, rfl, Finmap.mem_of_lookup_eq_some (receiver_declared r)⟩⟩
    hb Context.completed_empty (fun _ he => False.elim (Finmap.notMem_empty he))
    (separated_empty _)
  have hp := (Runtime.HasType.cong_iff
    (.trans Cong.nu_nil.symm (.nu_cong Cong.nu_nil.symm))).mp (nil_typed 1 (services r))
  have ht := Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context)) hn hp
  simp only [Finmap.union_empty] at ht
  simpa only [extra, Finmap.union_empty] using
    Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context)) hw ht

private theorem network_typed (r : Role) (i : Nat) :
    Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) (network i) := by
  simpa only [network, Finmap.union_empty] using Runtime.HasType.par
    (fun _ _ he => Finmap.notMem_empty he)
    (phase_typed_by_preservation r (.var 0) (Nat.zero_lt_succ 0)
      (by constructor <;> intro h <;> cases h) i) (extra_typed r)

private theorem network_available (r : Role) (i : Nat) : Available (services r) (network i) := by
  intro s sig hs
  exact Or.inl (phase_available_by_reduction (.var 0) r i s sig hs)

private theorem phase_output (i : Nat) : PiCalculus.HasUnguardedOutput (network i) := by
  have hm : i % 3 < 3 := Nat.mod_lt i (by decide)
  have hh : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hh with h | h | h <;>
    simp [network, phase, h, PiCalculus.HasUnguardedOutput, pending, sentInvoked, bothInvoked,
      senderRequest, receiverRequest, senderWorker, receiverWorker]

/-- BOTH actual service invocations occur with these additional wrapped/nested
persistent templates and literal completed private pairs. GENERAL progress yields
Step at EVERY phase; actual chosen two calls independently exercise persistence. -/
theorem nested_two_calls_general_progress (r : Role) :
    PiCalculus.Step (network 0) (network 1) ∧ PiCalculus.Step (network 1) (network 2) ∧
    ∀ i, Runtime.HasType 1 (services r) (recurringInterface (.var 0) r) (network i) ∧
      Available (services r) (network i) ∧ ∃ q, PiCalculus.Step (network i) q := by
  refine ⟨.parL (phase_step (.var 0) 0), .parL (phase_step (.var 0) 1), ?_⟩
  intro i
  refine ⟨network_typed r i, network_available r i, ?_⟩
  rcases (network_typed r i).progress_balanced (recurring_balanced (.var 0) r)
    (network_available r i) with hi | hs
  · exact False.elim (hi.no_unguarded_output (phase_output i))
  · exact hs

private def privatePairs (i : Nat) : Proc :=
  .nu (.nu (.par .nil (liftProc 0 (liftProc 0 (network i)))))

private theorem scope_cong (i : Nat) : Cong (privatePairs i) (.par (network i) (.nu (.nu .nil))) :=
  .trans (.nu_cong (Cong.scope .nil (liftProc 0 (network i))).symm)
    (.trans (Cong.scope (.nu .nil) (network i)).symm (.par_comm _ _))

/-- GENERAL progress survives actual double completed-pair scope extrusion,
without supplying a normalized frontier or an execution witness. -/
theorem scoped_general_step (r : Role) (i : Nat) : ∃ q, PiCalculus.Step (privatePairs i) q := by
  have hp := (Runtime.HasType.cong_iff
    (.trans Cong.nu_nil.symm (.nu_cong Cong.nu_nil.symm))).mp (nil_typed 1 (services r))
  have ht := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he) (network_typed r i) hp
  simp only [Finmap.union_empty] at ht
  have ha : Available (services r) (.par (network i) (.nu (.nu .nil))) := by
    intro s sig hs
    exact Or.inl (network_available r i s sig hs)
  rcases ((Runtime.HasType.cong_iff (scope_cong i)).mpr ht).progress_balanced
    (recurring_balanced (.var 0) r) ((Available.cong_iff (scope_cong i)).mpr ha) with hi | hs
  · have hid : Idle (services r) (.par (network i) (.nu (.nu .nil))) :=
      (ServiceTemplate.cong_iff (scope_cong i)).mp hi
    exact False.elim (hid.no_unguarded_output (Or.inl (phase_output i)))
  · exact hs

/-- Canonical swap of the two real private binders retains the Step supplied by
GENERAL runtime progress, through the actual canonical Cong Step rule. -/
theorem swapped_private_pairs_general_step (r : Role) (i : Nat) :
    ∃ q, PiCalculus.Step
      (.nu (.nu (swapProc 0 (.par .nil (liftProc 0 (liftProc 0 (network i))))))) q := by
  obtain ⟨q, hs⟩ := scoped_general_step r i
  exact ⟨q, .cong (Cong.nu_swap _).symm hs (.refl q)⟩

end Cslib.SessionTypes.Endpoint.NestedRuntimeProgressTests
