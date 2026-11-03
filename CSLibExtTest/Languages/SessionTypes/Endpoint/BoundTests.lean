/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing
import CSLibExt.Languages.SessionTypes.Endpoint.ScopeTransport
import CSLibExt.Languages.SessionTypes.Endpoint.SubjectReduction
import CSLibExt.Languages.SessionTypes.Endpoint.RankedReduction
import CSLibExt.Languages.SessionTypes.Endpoint.FrontierNormalization
import CSLibExt.Languages.SessionTypes.Endpoint.GlobalProgress
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Actual restriction-bound endpoint communication

The guards use var 0, the physical name introduced by ν, not free constants.
-/

namespace Cslib.SessionTypes.Endpoint.BoundTests

open PiCalculus

private def positive : Key := ⟨.var 0, .positive⟩
private def negative : Key := ⟨.var 0, .negative⟩
private def sending : Capability := ⟨0, .sendName .done⟩
private def receiving : Capability := ⟨0, .recvName .done⟩

/-- Output on the actual surrounding restriction's name. -/
def sender : Proc := .out (.var 0) (.const 7) .nil

/-- Input on the peer role of that same restriction. -/
def receiver : Proc := .inp (.var 0) .nil

/-- The sending thread owns one linear role. -/
theorem sender_typed : HasType 1 (Finmap.singleton positive sending) sender := by
  apply HasType.outName (e := positive) (c := sending) (s := .done)
  · simp
  · rfl
  · change 0 < 1
    decide
  · trivial
  · rw [Finmap.insert_singleton_eq]
    exact HasType.nil_singleton (by change 0 < 1; decide)

/-- The receiving thread owns the opposite role on that same name. -/
theorem receiver_typed : HasType 1 (Finmap.singleton negative receiving) receiver := by
  apply HasType.inpName (e := negative) (c := receiving) (s := .done)
  · simp
  · rfl
  · change 0 < 1
    decide
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact HasType.nil_singleton (by change 1 < 2; decide)

/-- One physical restriction connects both live guards. -/
def network : Proc := .nu (.par sender receiver)

/-- The closed network owns no free endpoint; its two roles are ν-bound. -/
theorem network_typed : HasType 0 ∅ network := by
  apply HasType.nu (c := sending)
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact sender_typed
  · exact receiver_typed

/-- The live bound roles synchronize using the unchanged π step. -/
theorem network_step : PiCalculus.Step network (.nu (.par .nil .nil)) := by
  exact PiCalculus.Step.nu (PiCalculus.Step.commSelect (.refl _) (.refl _))

/-- The concrete communication's residual is typed with completed bound roles. -/
theorem residual_typed : HasType 0 ∅ (.nu (.par .nil .nil)) := by
  apply HasType.nu (c := ⟨0, .done⟩)
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact HasType.nil_singleton (by change 0 < 1; decide)
  · exact HasType.nil_singleton (by change 0 < 1; decide)

/-- General all-Step preservation, rather than a manually retyped residual,
retains the empty interface after the actual ν-bound synchronization. -/
theorem general_step_residual : HasType 0 ∅ (.nu (.par .nil .nil)) :=
  network_typed.subject_reduction_empty network_step

/-- Reverse output orientation is reached by canonical pre-congruence. -/
theorem reversed_network_typed : HasType 0 ∅ (.nu (.par receiver sender)) :=
  (HasType.cong_iff (Cong.nu_cong (Cong.par_comm sender receiver))).mp network_typed

/-- The receiver-first network reduces via congruence and the general theorem. -/
theorem reversed_general_step_residual : HasType 0 ∅ (.nu (.par .nil .nil)) := by
  have hs : PiCalculus.Step (.nu (.par receiver sender)) (.nu (.par .nil .nil)) :=
    PiCalculus.Step.cong (Cong.nu_cong (Cong.par_comm receiver sender)) network_step
      (Cong.refl _)
  exact reversed_network_typed.subject_reduction_empty hs

/-- Scope extrusion used as pre/post-congruence around the actual private
step preserves the original empty external interface by the general theorem. -/
theorem scoped_general_step_residual :
    HasType 0 ∅ (.par (.nu (.par .nil .nil)) .nil) := by
  have ht := network_typed.par_nil_intro
  have hs : PiCalculus.Step (.par network .nil) (.par (.nu (.par .nil .nil)) .nil) :=
    PiCalculus.Step.cong (Cong.scope (.par sender receiver) .nil)
      (PiCalculus.Step.nu (PiCalculus.Step.parL
        (PiCalculus.Step.commSelect (.refl _) (.refl _))))
      (Cong.symm (Cong.scope (.par .nil .nil) .nil))
  exact ht.subject_reduction_empty hs

/-- The negative role can be the actual sender; its original positive
capability is the receive head, rather than silently assuming positive output. -/
theorem negative_sender_network_typed : HasType 0 ∅ network := by
  apply HasType.nu (c := receiving)
  rw [Context.bind_empty]
  have hneg : HasType 1 (Finmap.singleton negative receiving.dual) sender := by
    apply HasType.outName (e := negative) (c := receiving.dual) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact HasType.nil_singleton (Nat.zero_lt_succ 0)
  have hpos : HasType 1 (Finmap.singleton positive receiving) receiver := by
    apply HasType.inpName (e := positive) (c := receiving) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact HasType.nil_singleton (by change 1 < 2; decide)
  have hd : Finmap.Disjoint (Finmap.singleton positive receiving : Context)
      (Finmap.singleton negative receiving.dual : Context) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, positive, negative]
  exact (HasType.par hd hpos hneg).par_comm

/-- The GENERAL theorem preserves the actual negative-sender derivation. -/
theorem negative_sender_general_residual : HasType 0 ∅ (.nu (.par .nil .nil)) :=
  negative_sender_network_typed.subject_reduction_empty network_step

/-- The refined closed network splits its opposite roles across threads,
so each live guard checks precisely its own singleton ownership. -/
theorem network_ranked : RankedType 0 ∅ network := by
  apply RankedType.nu (c := sending)
  rw [Context.bind_empty]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply RankedType.outName (e := positive) (c := sending) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [positive, Finmap.insert_singleton_eq]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  · apply RankedType.inpName (e := negative) (c := receiving) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [negative, Finmap.insert_singleton_eq, Context.lift_singleton]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 2; decide))

/-- GENERAL refinement projection and binder transport preserve this network. -/
theorem network_ranked_lift :
    RankedType 1 (Context.lift 0 ∅) (liftProc 0 network) := network_ranked.lift 0

/-- GENERAL ranked Cong transport commutes the actual restricted live guards. -/
theorem network_ranked_commuted : RankedType 0 ∅ (.nu (.par receiver sender)) :=
  (RankedType.cong_iff (Cong.nu_cong (Cong.par_comm sender receiver))).mp network_ranked

/-- GENERAL ranked congruence reverses extrusion on the same live network. -/
theorem network_ranked_reverse_scope : RankedType 0 ∅ (.par (.nu (.par sender receiver)) .nil) := by
  have ht := network_ranked.par_nil_intro
  have he := (RankedType.cong_iff (Cong.scope (.par sender receiver) .nil)).mp ht
  exact (RankedType.cong_iff (Cong.symm (Cong.scope (.par sender receiver) .nil))).mp he

/-- GENERAL ranked Step preservation on the actual private live channel. -/
theorem network_ranked_step_residual : RankedType 0 ∅ (.nu (.par .nil .nil)) :=
  network_ranked.subject_reduction_empty network_step

/-- GENERAL ranked preservation handles a receiver-first congruent source. -/
theorem receiver_first_ranked_step_residual : RankedType 0 ∅ (.nu (.par .nil .nil)) := by
  have hs : PiCalculus.Step (.nu (.par receiver sender)) (.nu (.par .nil .nil)) :=
    PiCalculus.Step.cong (Cong.nu_cong (Cong.par_comm receiver sender)) network_step (Cong.refl _)
  exact network_ranked_commuted.subject_reduction_empty hs

/-- Actual scope extrusion at both ends of the Step keeps every ranked guard. -/
theorem scoped_ranked_step_residual : RankedType 0 ∅ (.par (.nu (.par .nil .nil)) .nil) := by
  have hs : PiCalculus.Step (.par network .nil) (.par (.nu (.par .nil .nil)) .nil) :=
    PiCalculus.Step.cong (Cong.scope (.par sender receiver) .nil)
      (PiCalculus.Step.nu (PiCalculus.Step.parL
        (PiCalculus.Step.commSelect (.refl _) (.refl _))))
      (Cong.symm (Cong.scope (.par .nil .nil) .nil))
  exact network_ranked.par_nil_intro.subject_reduction_empty hs

/-- The negative subject role is a ranked sender in its own singleton owner. -/
theorem negative_sender_network_ranked : RankedType 0 ∅ network := by
  apply RankedType.nu (c := receiving)
  rw [Context.bind_empty]
  have hneg : RankedType 1 (Finmap.singleton negative receiving.dual) sender := by
    apply RankedType.outName (e := negative) (c := receiving.dual) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  have hpos : RankedType 1 (Finmap.singleton positive receiving) receiver := by
    apply RankedType.inpName (e := positive) (c := receiving) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 2; decide))
  have hd : Finmap.Disjoint (Finmap.singleton positive receiving : Context)
      (Finmap.singleton negative receiving.dual : Context) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, positive, negative]
  exact (RankedType.par hd hpos hneg).par_comm

/-- GENERAL ranked Step preservation uses the real negative-sender derivation. -/
theorem negative_sender_ranked_step_residual : RankedType 0 ∅ (.nu (.par .nil .nil)) :=
  negative_sender_network_ranked.subject_reduction_empty network_step

/-- GENERAL normalization retains ranked typing and exposes the actual
private live channel; it does not declare an empty interface completed. -/
theorem network_ranked_frontier : ∃ q,
    Cong network q ∧ RankedType 0 ∅ q ∧ FrontierNormal q := network_ranked.frontier_normal

/-- Process completion is NOT completion of the empty external context:
the actual live private channel cannot be congruent to nil. -/
theorem live_network_not_completed : ¬ Cong network .nil := by
  intro hc
  have hin : HasUnguardedInput network := by
    exact Or.inr trivial
  exact (input_cong hc).mp hin

/-- GENERAL normalization of a live ranked network cannot return nil. -/
theorem live_ranked_frontier_nonempty : ∃ q,
    Cong network q ∧ RankedType 0 ∅ q ∧ FrontierNormal q ∧ q ≠ .nil := by
  obtain ⟨q, hc, ht, hn⟩ := network_ranked.frontier_normal
  exact ⟨q, hc, ht, hn, fun he => live_network_not_completed (he ▸ hc)⟩

/-- GENERAL frontier progress on the actual balanced private channel body. -/
theorem balanced_live_frontier_progress :
    Cong (.par sender receiver) .nil ∨ ∃ q, PiCalculus.Step (.par sender receiver) q := by
  obtain ⟨c, ht⟩ := network_ranked.nu_inv
  exact (GuardFrontier.par (GuardFrontier.out _ _ _) (GuardFrontier.inp _ _)).progress
    ht (balanced_bind_empty c)

/-- GENERAL frontier progress also handles the genuine negative-role sender. -/
theorem balanced_negative_sender_frontier_progress :
    Cong (.par sender receiver) .nil ∨ ∃ q, PiCalculus.Step (.par sender receiver) q := by
  obtain ⟨c, ht⟩ := negative_sender_network_ranked.nu_inv
  exact (GuardFrontier.par (GuardFrontier.out _ _ _) (GuardFrontier.inp _ _)).progress
    ht (balanced_bind_empty c)

/-- Completed nil frontiers invoke the SAME general theorem, not empty
external-context completion of a live process. -/
theorem completed_frontier_progress :
    Cong (.par .nil .nil) .nil ∨ ∃ q, PiCalculus.Step (.par .nil .nil) q := by
  obtain ⟨c, ht⟩ := network_ranked_step_residual.nu_inv
  exact (GuardFrontier.par GuardFrontier.nil GuardFrontier.nil).progress ht (balanced_bind_empty c)

/-- A live frontier cannot take the completion branch; the Step witness is
obtained from GENERAL progress rather than supplying a prechosen head pair. -/
theorem balanced_live_frontier_actual_step : ∃ q, PiCalculus.Step (.par sender receiver) q := by
  rcases balanced_live_frontier_progress with hc | hs
  · have hin : HasUnguardedInput (.par sender receiver) := Or.inr trivial
    exact False.elim ((input_cong hc).mp hin)
  · exact hs

/-- GENERAL global progress inspects the actual hidden private live pair. -/
theorem closed_network_global_progress : Cong network .nil ∨ ∃ q, PiCalculus.Step network q :=
  network_ranked.progress_empty

/-- The live private network gets an actual Step from GENERAL global progress,
not from a caller-chosen communication pair or interface-completion shortcut. -/
theorem closed_network_global_actual_step : ∃ q, PiCalculus.Step network q := by
  rcases closed_network_global_progress with hc | hs
  · exact False.elim (live_network_not_completed hc)
  · exact hs

/-- The general global theorem covers the negative-role sender derivation too. -/
theorem negative_sender_global_progress : Cong network .nil ∨ ∃ q, PiCalculus.Step network q :=
  negative_sender_network_ranked.progress_empty

/-- The receiver-first congruent network uses the same global theorem. -/
theorem receiver_first_global_progress :
    Cong (.nu (.par receiver sender)) .nil ∨ ∃ q, PiCalculus.Step (.nu (.par receiver sender)) q :=
  network_ranked_commuted.progress_empty

/-- A scope-extruded variant is admitted without a caller normal-form witness. -/
theorem scoped_network_global_progress :
    Cong (.nu (.par (.par sender receiver) (liftProc 0 .nil))) .nil ∨
      ∃ q, PiCalculus.Step (.nu (.par (.par sender receiver) (liftProc 0 .nil))) q := by
  have ht := (RankedType.cong_iff (Cong.scope (.par sender receiver) .nil)).mp
    network_ranked.par_nil_intro
  exact ht.progress_empty

/-- Completed private restrictions invoke the SAME global completed-or-Step theorem. -/
theorem completed_network_global_progress :
    Cong (.nu (.par .nil .nil)) .nil ∨ ∃ q, PiCalculus.Step (.nu (.par .nil .nil)) q :=
  network_ranked_step_residual.progress_empty

/-- Every finite reachable residual has global progress, without a termination claim. -/
theorem actual_reachable_network_progress :
    Cong (.nu (.par .nil .nil)) .nil ∨ ∃ q, PiCalculus.Step (.nu (.par .nil .nil)) q :=
  network_ranked.reachable_progress (Relation.ReflTransGen.single network_step)

end Cslib.SessionTypes.Endpoint.BoundTests
