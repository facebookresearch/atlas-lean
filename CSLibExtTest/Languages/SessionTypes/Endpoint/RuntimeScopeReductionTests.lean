/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveReduction

/-!
# General runtime preservation behind private scope and completed frames
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeScopeReductionTests

open PiCalculus Endpoint.Runtime

private theorem closed_phase (r : Role) (i : Nat) :
    Runtime.HasType 0 (services r) ∅ (.nu (phase (.var 0) i)) := by
  have hp := phase_typed_by_preservation r (.var 0) (Nat.zero_lt_succ 0)
    (by constructor <;> intro h <;> cases h) i
  cases r with
  | positive =>
    apply Runtime.HasType.nu (c := recurringCap) (separated_empty _)
    rw [Context.bind_empty]
    exact hp
  | negative =>
    apply Runtime.HasType.nu (c := recurringCap.dual) (separated_empty _)
    rw [Context.bind_empty, Capability.dual_dual]
    rw [Finmap.union_comm_of_disjoint (by
      simp [Finmap.Disjoint, Finmap.mem_singleton])]
    exact hp

/-- GENERAL runtime preservation covers all THREE private recursive phase kinds
in BOTH orientations and retains the EXACT empty external interface. -/
theorem private_phase_step (r : Role) (i : Nat) :
    Runtime.HasType 0 (services r) ∅ (.nu (phase (.var 0) (i + 1))) :=
  (closed_phase r i).subject_reduction_empty (PiCalculus.Step.nu (phase_step (.var 0) i))

private def frame : Context := Finmap.singleton ⟨.const 900, .positive⟩ ⟨3, .done⟩

private theorem frame_typed (r : Role) : Runtime.HasType 0 (services r) frame .nil := by
  apply Runtime.HasType.nil (Context.completed_empty.insert (by rfl))
  · intro e he
    have heq := (Finmap.mem_singleton _ _ _).mp he
    subst e
    trivial
  · apply separated_singleton
    intro s sig hs hn
    have he := Name.const.inj hn
    subst s
    have hm := Finmap.mem_of_lookup_eq_some hs
    simp [services, Finmap.mem_insert, Finmap.mem_singleton] at hm

private theorem frame_compatible : Conversion.Compatible frame := by
  intro e c d hc hd
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
  have hp := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hd)
  exact False.elim (Key.opposite_ne e (hp.trans he.symm))

private theorem frame_no_advance (Ξ : Context) : ¬ Conversion.SemanticAdvance frame Ξ := by
  intro h
  cases h with
  | @matched e c d s u hc hd he hh ht =>
    have hdone := (frame_typed .positive).nil_inv.1 e c hc
    cases hh with
    | passive hs hu => rw [hdone] at hs; cases hs
    | endpoint hs hu heq => rw [hdone] at hs; cases hs

/-- A real private Step framed by a recorded completed role retains that EXACT
role/rank/code through GENERAL preservation; it is not silently erased with nil. -/
theorem completed_frame_step (r : Role) (i : Nat) : Runtime.HasType 0 (services r) frame
    (.par (.nu (phase (.var 0) (i + 1))) .nil) := by
  have hsource := Runtime.HasType.par (fun _ he _ => Finmap.notMem_empty he)
    (closed_phase r i) (frame_typed r)
  simp only [Finmap.empty_union] at hsource
  obtain ⟨Ξ, ht, hc, he⟩ := hsource.subject_reduction frame_compatible
    (PiCalculus.Step.parL (PiCalculus.Step.nu (phase_step (.var 0) i)))
  rcases he with hid | ha
  · exact hid ▸ ht
  · exact False.elim (frame_no_advance Ξ ha)

/-- Actual pre/post scope extrusion transports a private recursive Step through
canonical Cong, then GENERAL runtime preservation retains exact empty ownership. -/
theorem extruded_private_step (r : Role) (i : Nat) : Runtime.HasType 0 (services r) ∅
    (.nu (.par (phase (.var 0) (i + 1)) (liftProc 0 senderDaemon))) := by
  have hsource := Runtime.HasType.par (Finmap.disjoint_empty (∅ : Context))
    (closed_phase r i) (sender_daemon_typed 0 r)
  simp only [Finmap.union_empty] at hsource
  have hscoped := (Runtime.HasType.cong_iff (Cong.scope (phase (.var 0) i) senderDaemon)).mp hsource
  have hs := PiCalculus.Step.cong (Cong.scope (phase (.var 0) i) senderDaemon).symm
    (PiCalculus.Step.parL (PiCalculus.Step.nu (phase_step (.var 0) i)))
    (Cong.scope (phase (.var 0) (i + 1)) senderDaemon)
  exact hscoped.subject_reduction_empty hs

private theorem phase_lift_one (i : Nat) : liftProc 1 (phase (.var 0) i) = phase (.var 0) i := by
  unfold phase
  split <;> rfl

private theorem nested_private_source (r : Role) (i : Nat) :
    Runtime.HasType 0 (services r) ∅ (.nu (.nu (phase (.var 0) i))) := by
  have hl := (closed_phase r i).lift 0
  simp only [Context.lift_empty] at hl
  have hp := hl.weaken_completed (z := ⟨.var 0, .positive⟩) (u := ⟨3, .done⟩)
    Finmap.notMem_empty rfl (Nat.zero_lt_succ 0) (by intro s sig hs hn; cases hn)
  have hpn := hp.weaken_completed (z := ⟨.var 0, .negative⟩) (u := ⟨3, .done⟩)
    (by simp [Finmap.mem_insert, Finmap.notMem_empty]) rfl (Nat.zero_lt_succ 0)
    (by intro s sig hs hn; cases hn)
  apply Runtime.HasType.nu (c := ⟨3, .done⟩) (separated_empty _)
  rw [Context.bind, Context.lift_empty]
  change Runtime.HasType 1 (services r)
    (((∅ : Context).insert ⟨.var 0, .positive⟩ ⟨3, .done⟩).insert ⟨.var 0, .negative⟩ ⟨3, .done⟩)
    (.nu (phase (.var 0) i))
  change Runtime.HasType 1 (services r) _ (.nu (liftProc 1 (phase (.var 0) i))) at hpn
  rw [phase_lift_one] at hpn
  exact hpn

/-- TWO private binders (one actual completed pair) swap pre/post a real Step.
GENERAL runtime preservation uses canonical capture-safe swap and literal private
projection, not the finite fragment's reduction theorem. -/
theorem swapped_private_step (r : Role) (i : Nat) : Runtime.HasType 0 (services r) ∅
    (.nu (.nu (swapProc 0 (phase (.var 0) (i + 1))))) := by
  have hsource := (Runtime.HasType.cong_iff (Cong.nu_swap (phase (.var 0) i))).mp
    (nested_private_source r i)
  have hs := PiCalculus.Step.cong (Cong.nu_swap (phase (.var 0) i)).symm
    (PiCalculus.Step.nu (PiCalculus.Step.nu (phase_step (.var 0) i)))
    (Cong.nu_swap (phase (.var 0) (i + 1)))
  exact hsource.subject_reduction_empty hs

end Cslib.SessionTypes.Endpoint.RuntimeScopeReductionTests
