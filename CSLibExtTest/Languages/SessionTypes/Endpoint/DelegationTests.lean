/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing
import CSLibExt.Languages.SessionTypes.Endpoint.Priority
import CSLibExt.Languages.SessionTypes.Endpoint.SubjectReduction
import CSLibExt.Languages.SessionTypes.Endpoint.RankedReduction
import CSLibExt.Languages.SessionTypes.Endpoint.FrontierNormalization
import CSLibExt.Languages.SessionTypes.Endpoint.GlobalProgress
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Three-thread linear endpoint delegation with actual bound channel subjects

Under νa.νb the sender transfers b's positive role over a. The receiver then
uses the received name as a subject against b's negative-role owner.
-/

namespace Cslib.SessionTypes.Endpoint.DelegationTests

open PiCalculus

private def aPos : Key := ⟨.var 1, .positive⟩
private def aNeg : Key := ⟨.var 1, .negative⟩
private def bPos : Key := ⟨.var 0, .positive⟩
private def bNeg : Key := ⟨.var 0, .negative⟩
private def payload : Protocol := .sendName .done
private def bCap : Capability := ⟨1, payload⟩
private def aCap : Capability := ⟨0, .sendEndpoint .positive 1 payload .done⟩

/-- The sender initially owns a's send role and the transferable b role. -/
def senderContext : Context := ((∅ : Context).insert aPos aCap).insert bPos bCap

/-- Transfer the endpoint capability, leaving no b capability in the sender. -/
def sender : Proc := .out (.var 1) (.var 0) .nil

/-- The transfer is typed as an endpoint payload, not as passive name data. -/
theorem sender_typed : HasType 2 senderContext sender := by
  apply HasType.outEndpoint (e := aPos) (d := bPos) (c := aCap)
    (k := 1) (t := payload) (s := .done)
  · simp [senderContext, aPos, bPos]
  · rfl
  · simp [senderContext, bCap]
  · decide
  · change 1 < 2
    decide
  · change 0 < 2
    decide
  · change HasType 2 (Finmap.singleton aPos ⟨0, .done⟩) .nil
    exact HasType.nil_singleton (by change 1 < 2; decide)

/-- The receiver initially has only a's peer role, not b's capability. -/
def receiverContext : Context := Finmap.singleton aNeg aCap.dual

/-- The receive-bound name is subsequently used as a session subject. -/
def receiver : Proc := .inp (.var 1) (.out (.var 0) (.const 7) .nil)

/-- Linear reception, unlike passive reception, licenses the bound subject. -/
theorem receiver_typed : HasType 2 receiverContext receiver := by
  apply HasType.inpEndpoint (e := aNeg) (c := aCap.dual) (r := .positive)
    (k := 1) (t := payload) (s := .done)
  · simp [receiverContext]
  · rfl
  · change 1 < 2
    decide
  · rw [receiverContext, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply HasType.outName (e := ⟨.var 0, .positive⟩) (c := bCap) (s := .done)
    · simp [bCap]
    · rfl
    · change 0 < 3
      decide
    · trivial
    · rw [Finmap.insert_insert]
      apply HasType.nil_insert (HasType.nil_singleton ?_) rfl
      · change 0 < 3
        decide
      · change 2 < 3
        decide

/-- The third thread owns b's peer, not a duplicated sent role. -/
def peer : Proc := .inp (.var 0) .nil

/-- The peer has the dual payload protocol on the same physical b name. -/
theorem peer_typed : HasType 2 (Finmap.singleton bNeg bCap.dual) peer := by
  apply HasType.inpName (e := bNeg) (c := bCap.dual) (s := .done)
  · simp
  · rfl
  · change 0 < 2
    decide
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact HasType.nil_singleton (by change 1 < 3; decide)

/-- The complete restriction context splits into the three real thread owners. -/
theorem network_context :
    Context.bind bCap (Context.bind aCap ∅) =
      senderContext ∪ (receiverContext ∪ Finmap.singleton bNeg bCap.dual) := by
  apply Finmap.ext
  change
    ({⟨bNeg, bCap.dual⟩} + {⟨bPos, bCap⟩} +
      {⟨aNeg, aCap.dual⟩} + {⟨aPos, aCap⟩} : Multiset (Sigma (fun _ : Key => Capability))) =
    ({⟨bPos, bCap⟩} + {⟨aPos, aCap⟩} +
      ({⟨aNeg, aCap.dual⟩} + {⟨bNeg, bCap.dual⟩}))
  ac_rfl

/-- The a transfer and b use form a connected, genuinely ν-closed network. -/
def network : Proc := .nu (.nu (.par sender (.par receiver peer)))

/-- The three-thread delegation network has no free linear endpoint interface. -/
theorem network_typed : HasType 0 ∅ network := by
  apply HasType.nu (c := aCap)
  apply HasType.nu (c := bCap)
  rw [network_context]
  apply HasType.par
  · simp [Finmap.Disjoint, senderContext, receiverContext, Finmap.mem_insert,
      Finmap.mem_union, Finmap.mem_singleton, aPos, aNeg, bPos, bNeg]
    intro e he
    exact False.elim (Finmap.notMem_empty he)
  · exact sender_typed
  · apply HasType.par
    · simp [Finmap.Disjoint, receiverContext, Finmap.mem_singleton, aNeg, bNeg]
    · exact receiver_typed
    · exact peer_typed

/-- The first actual π communication transfers b to the receiver. -/
theorem network_transfer : PiCalculus.Step network
    (.nu (.nu (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer))) := by
  apply PiCalculus.Step.nu
  apply PiCalculus.Step.nu
  exact PiCalculus.Step.cong (Cong.symm (Cong.par_assoc sender receiver peer))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (.refl _) (.refl _)))
    (Cong.refl _)

/-- The receiver communicates on b with the third thread after transfer,
using exactly the substituted subject in the existing π semantics. -/
theorem network_use : PiCalculus.Step
    (.nu (.nu (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer)))
    (.nu (.nu (.par .nil (.par .nil .nil)))) := by
  apply PiCalculus.Step.nu
  apply PiCalculus.Step.nu
  exact PiCalculus.Step.cong (Cong.par_assoc .nil (.out (.var 0) (.const 7) .nil) peer)
    (PiCalculus.Step.parR (PiCalculus.Step.commSelect (.refl _) (.refl _)))
    (Cong.refl _)

/-- The second communication reaches a quiescent finite network in the
existing π congruence, with no fairness or recursive termination claim. -/
theorem network_completed :
    Cong (.nu (.nu (.par .nil (.par .nil .nil)))) .nil := by
  exact Cong.trans (Cong.nu_cong (Cong.nu_cong
    (Cong.trans (Cong.par_cong (Cong.refl _) (Cong.par_nil _)) (Cong.par_nil _))))
    (Cong.trans (Cong.nu_cong Cong.nu_nil) Cong.nu_nil)

/-- The sender's guard precedes the transferred active endpoint, so the
connected a-to-b dependency is strictly ranked rather than assumed enabled. -/
theorem sender_guard_ranked : GuardMin senderContext aPos 0 := by
  intro e c hc ha hne
  have hm := Finmap.mem_of_lookup_eq_some hc
  rcases Finmap.mem_insert.mp hm with hm | hm
  · subst e
    simp only [senderContext, Finmap.lookup_insert, Option.some.injEq] at hc
    subst c
    exact Nat.zero_lt_one
  · rcases Finmap.mem_insert.mp hm with hm | hm
    · exact False.elim (hne hm)
    · exact False.elim (Finmap.notMem_empty hm)

/-- The GENERAL theorem handles the real ν-bound delegation, pre-congruence
reassociation and parallel frame, retaining its empty external interface. -/
theorem general_transfer_preserved : HasType 0 ∅
    (.nu (.nu (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer))) :=
  network_typed.subject_reduction_empty network_transfer

/-- The received endpoint is used as an actual subject on the next Step;
the same general theorem supplies the completed network's typing. -/
theorem general_received_subject_use_preserved :
    HasType 0 ∅ (.nu (.nu (.par .nil (.par .nil .nil)))) :=
  general_transfer_preserved.subject_reduction_empty network_use

/-- Swapping both surrounding restrictions before and after the real step
is handled by generic pre/post-congruence transport, not a special step rule. -/
theorem general_swapped_transfer_preserved : HasType 0 ∅
    (.nu (.nu (swapProc 0 (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer)))) := by
  have ht := (HasType.cong_iff (Cong.nu_swap (.par sender (.par receiver peer)))).mp
    network_typed
  have hs : PiCalculus.Step
      (.nu (.nu (swapProc 0 (.par sender (.par receiver peer)))))
      (.nu (.nu (swapProc 0 (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer)))) :=
    PiCalculus.Step.cong (Cong.symm (Cong.nu_swap _)) network_transfer (Cong.nu_swap _)
  exact ht.subject_reduction_empty hs

/-- An open interface for the actual endpoint transfer preserves the exact
combined key domain, including the transferred active subject capability. -/
theorem general_open_transfer_preserved : ∃ Ξ,
    HasType 2 Ξ (.par .nil (.out (.var 0) (.const 7) .nil)) ∧ Compatible Ξ ∧
      (Ξ = senderContext ∪ receiverContext ∨ DualAdvance (senderContext ∪ receiverContext) Ξ) := by
  have hwhole : Compatible (Context.bind bCap (Context.bind aCap ∅)) :=
    (balanced_empty.compatible.bind aCap).bind bCap
  rw [network_context, ← Finmap.union_assoc] at hwhole
  have hd : Finmap.Disjoint senderContext receiverContext := by
    simp [Finmap.Disjoint, senderContext, receiverContext, Finmap.mem_insert,
      Finmap.mem_singleton, aPos, aNeg, bPos]
    intro e he
    exact False.elim (Finmap.notMem_empty he)
  have ht := HasType.par hd sender_typed receiver_typed
  have hs : PiCalculus.Step (.par sender receiver)
      (.par .nil (.out (.var 0) (.const 7) .nil)) :=
    PiCalculus.Step.commSelect (.refl _) (.refl _)
  exact ht.subject_reduction hwhole.union_left hs

/-- The actual transferred active endpoint keeps its exact combined rank1
send protocol in the context returned by GENERAL Step preservation. -/
theorem general_open_payload_value_exact : ∃ Ξ,
    HasType 2 Ξ (.par .nil (.out (.var 0) (.const 7) .nil)) ∧
      Ξ.lookup bPos = some bCap := by
  obtain ⟨Ξ, ht, hc, he⟩ := general_open_transfer_preserved
  have old : (senderContext ∪ receiverContext).lookup bPos = some bCap := by
    rw [Finmap.lookup_union_left (by simp [senderContext])]
    exact Finmap.lookup_insert _
  have hno : bPos.opposite ∉ senderContext ∪ receiverContext := by
    simp [senderContext, receiverContext, Finmap.mem_union, Finmap.mem_insert,
      Finmap.mem_singleton, bPos, aPos, aNeg, Key.opposite, Role.opposite]
    exact Finmap.notMem_empty
  refine ⟨Ξ, ht, ?_⟩
  rcases he with rfl | ha
  · exact old
  · cases ha with
    | @matched e c s hu hp hs =>
      have hne : bPos ≠ e := by
        intro hh
        subst e
        exact hno (Finmap.mem_of_lookup_eq_some hp)
      have hnp : bPos ≠ e.opposite := by
        intro hh
        have hh' : bPos.opposite = e := by
          have hf := congrArg Key.opposite hh
          simpa only [Key.opposite_opposite] using hf
        exact hno (hh'.symm ▸ Finmap.mem_of_lookup_eq_some hu)
      rw [dual_update_lookup_other _ e bPos c s hne hnp]
      exact old

/-- Sender priority includes the active delegated b role at strict rank0<1. -/
theorem sender_ranked : RankedType 2 senderContext sender := by
  apply RankedType.outEndpoint (e := aPos) (d := bPos) (c := aCap)
    (k := 1) (t := payload) (s := .done)
  · exact sender_guard_ranked
  · simp [senderContext, aPos, bPos]
  · rfl
  · simp [senderContext, bCap]
  · decide
  · change 1 < 2
    decide
  · exact Nat.zero_lt_succ 1
  · change RankedType 2 (Finmap.singleton aPos ⟨0, .done⟩) .nil
    exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 2; decide))

/-- Reception adds usable subject ownership at rank1; the carrier's completed
rank0 role is ignored only because its protocol actually unfolds to done. -/
theorem receiver_ranked : RankedType 2 receiverContext receiver := by
  apply RankedType.inpEndpoint (e := aNeg) (c := aCap.dual) (r := .positive)
    (k := 1) (t := payload) (s := .done)
  · exact guardMin_singleton _ _
  · simp [receiverContext]
  · rfl
  · change 1 < 2
    decide
  · rw [receiverContext, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply RankedType.outName (e := ⟨.var 0, .positive⟩) (c := bCap) (s := .done)
    · intro e c hc ha hne
      by_cases he : e = (⟨.var 0, .positive⟩ : Key)
      · exact False.elim (hne he)
      · rw [Finmap.lookup_insert_of_ne _ he] at hc
        have hem := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
        subst e
        rw [Finmap.lookup_singleton_eq] at hc
        cases hc
        exact False.elim (ha rfl)
    · simp [bCap]
    · rfl
    · exact Nat.zero_lt_succ 2
    · trivial
    · rw [Finmap.insert_insert]
      apply RankedType.nil_of_hasType
      apply HasType.nil_insert (HasType.nil_singleton ?_) rfl
      · exact Nat.zero_lt_succ 2
      · change 2 < 3
        decide

/-- The third owner waits on b's peer at rank1, with no duplicate key. -/
theorem peer_ranked : RankedType 2 (Finmap.singleton bNeg bCap.dual) peer := by
  apply RankedType.inpName (e := bNeg) (c := bCap.dual) (s := .done)
  · exact guardMin_singleton _ _
  · simp
  · rfl
  · exact Nat.zero_lt_succ 1
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 3; decide))

/-- All guards of the actual connected three-thread/two-ν delegation fixture
satisfy the refinement, including the received-name subject guard. -/
theorem network_ranked : RankedType 0 ∅ network := by
  apply RankedType.nu (c := aCap)
  apply RankedType.nu (c := bCap)
  rw [network_context]
  apply RankedType.par
  · simp [Finmap.Disjoint, senderContext, receiverContext, Finmap.mem_insert,
      Finmap.mem_union, Finmap.mem_singleton, aPos, aNeg, bPos, bNeg]
    intro e he
    exact False.elim (Finmap.notMem_empty he)
  · exact sender_ranked
  · apply RankedType.par
    · simp [Finmap.Disjoint, receiverContext, Finmap.mem_singleton, aNeg, bNeg]
    · exact receiver_ranked
    · exact peer_ranked

/-- General capture-safe rekey/binder transport is exercised on delegation. -/
theorem network_ranked_lift : RankedType 1 (Context.lift 0 ∅) (liftProc 0 network) :=
  network_ranked.lift 0

/-- GENERAL ranked output congruence preserves the active delegation payload
constraint while changing only its completed continuation syntax. -/
theorem sender_ranked_congruent_body : RankedType 2 senderContext
    (.out (.var 1) (.var 0) (.par .nil .nil)) :=
  (RankedType.cong_iff (Cong.out_cong _ _ (Cong.symm (Cong.par_nil .nil)))).mp sender_ranked

/-- GENERAL ranked input congruence preserves the received role and all
inner subject guard inequalities through an input-binder context. -/
theorem receiver_ranked_congruent_body : RankedType 2 receiverContext
    (.inp (.var 1) (.par (.out (.var 0) (.const 7) .nil) .nil)) :=
  (RankedType.cong_iff (Cong.inp_cong _ (Cong.symm (Cong.par_nil _)))).mp receiver_ranked

/-- GENERAL ranked Step preservation on actual three-thread delegation. -/
theorem network_ranked_transfer : RankedType 0 ∅
    (.nu (.nu (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer))) :=
  network_ranked.subject_reduction_empty network_transfer

/-- The received endpoint remains usable as a SUBJECT in the next ranked Step. -/
theorem network_ranked_received_subject_use :
    RankedType 0 ∅ (.nu (.nu (.par .nil (.par .nil .nil)))) :=
  network_ranked_transfer.subject_reduction_empty network_use

/-- Generic ranked preservation covers swapped pre/post-congruence on the
same private endpoint transfer, without changing its empty external context. -/
theorem network_ranked_swapped_transfer : RankedType 0 ∅
    (.nu (.nu (swapProc 0 (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer)))) := by
  have ht := (RankedType.cong_iff (Cong.nu_swap (.par sender (.par receiver peer)))).mp
    network_ranked
  have hs : PiCalculus.Step
      (.nu (.nu (swapProc 0 (.par sender (.par receiver peer)))))
      (.nu (.nu (swapProc 0 (.par (.par .nil (.out (.var 0) (.const 7) .nil)) peer)))) :=
    PiCalculus.Step.cong (Cong.symm (Cong.nu_swap _)) network_transfer (Cong.nu_swap _)
  exact ht.subject_reduction_empty hs

/-- The open ranked transfer returns zero-or-one actual carrier advancement. -/
theorem ranked_open_transfer : ∃ Ξ,
    RankedType 2 Ξ (.par .nil (.out (.var 0) (.const 7) .nil)) ∧ Compatible Ξ ∧
      (Ξ = senderContext ∪ receiverContext ∨ DualAdvance (senderContext ∪ receiverContext) Ξ) := by
  have hwhole : Compatible (Context.bind bCap (Context.bind aCap ∅)) :=
    (balanced_empty.compatible.bind aCap).bind bCap
  rw [network_context, ← Finmap.union_assoc] at hwhole
  have hd : Finmap.Disjoint senderContext receiverContext := by
    simp [Finmap.Disjoint, senderContext, receiverContext, Finmap.mem_insert,
      Finmap.mem_singleton, aPos, aNeg, bPos]
    intro e he
    exact False.elim (Finmap.notMem_empty he)
  have ht := RankedType.par hd sender_ranked receiver_ranked
  have hs : PiCalculus.Step (.par sender receiver)
      (.par .nil (.out (.var 0) (.const 7) .nil)) :=
    PiCalculus.Step.commSelect (.refl _) (.refl _)
  exact ht.subject_reduction hwhole.union_left hs

/-- GENERAL ranked returned-map evidence retains the transferred active
rank1 sendName protocol, rather than an arbitrarily retyped payload. -/
theorem ranked_open_payload_value_exact : ∃ Ξ,
    RankedType 2 Ξ (.par .nil (.out (.var 0) (.const 7) .nil)) ∧
      Ξ.lookup bPos = some bCap := by
  obtain ⟨Ξ, ht, hc, he⟩ := ranked_open_transfer
  have old : (senderContext ∪ receiverContext).lookup bPos = some bCap := by
    rw [Finmap.lookup_union_left (by simp [senderContext])]
    exact Finmap.lookup_insert _
  have hno : bPos.opposite ∉ senderContext ∪ receiverContext := by
    simp [senderContext, receiverContext, Finmap.mem_union, Finmap.mem_insert,
      Finmap.mem_singleton, bPos, aPos, aNeg, Key.opposite, Role.opposite]
    exact Finmap.notMem_empty
  refine ⟨Ξ, ht, ?_⟩
  rcases he with rfl | ha
  · exact old
  · cases ha with
    | @matched e c s hu hp hs =>
      have hne : bPos ≠ e := by
        intro hh
        subst e
        exact hno (Finmap.mem_of_lookup_eq_some hp)
      have hnp : bPos ≠ e.opposite := by
        intro hh
        have hh' : bPos.opposite = e := by
          have hf := congrArg Key.opposite hh
          simpa only [Key.opposite_opposite] using hf
        exact hno (hh'.symm ▸ Finmap.mem_of_lookup_eq_some hu)
      rw [dual_update_lookup_other _ e bPos c s hne hnp]
      exact old

/-- GENERAL normalization retains the original connected three-thread
ranked delegation network and all its private ownership, not only chosen heads. -/
theorem connected_delegation_ranked_frontier : ∃ q,
    Cong network q ∧ RankedType 0 ∅ q ∧ FrontierNormal q := network_ranked.frontier_normal

/-- GENERAL balanced-frontier progress covers the whole original connected
three-thread delegation body, not just its preselected sender/receiver pair. -/
theorem connected_delegation_frontier_progress :
    Cong (.par sender (.par receiver peer)) .nil ∨
      ∃ q, PiCalculus.Step (.par sender (.par receiver peer)) q := by
  obtain ⟨c, hc⟩ := network_ranked.nu_inv
  obtain ⟨d, hd⟩ := hc.nu_inv
  exact (GuardFrontier.par (GuardFrontier.out _ _ _)
    (GuardFrontier.par (GuardFrontier.inp _ _) (GuardFrontier.inp _ _))).progress
      hd ((balanced_empty.bind c).bind d)

/-- The ACTUAL Step is derived from the general frontier theorem; no
complementary head pair is passed as an admission premise. -/
theorem connected_delegation_frontier_actual_step :
    ∃ q, PiCalculus.Step (.par sender (.par receiver peer)) q := by
  rcases connected_delegation_frontier_progress with hc | hs
  · have hin : HasUnguardedInput (.par sender (.par receiver peer)) := Or.inr (Or.inl trivial)
    exact False.elim ((input_cong hc).mp hin)
  · exact hs

/-- GENERAL GLOBAL progress on the original connected three-thread ν network. -/
theorem connected_delegation_global_progress :
    Cong network .nil ∨ ∃ q, PiCalculus.Step network q := network_ranked.progress_empty

/-- A live private delegated channel cannot be completed just because its
external ownership map is empty. The actual Step comes from GLOBAL progress. -/
theorem connected_delegation_global_actual_step : ∃ q, PiCalculus.Step network q := by
  rcases connected_delegation_global_progress with hc | hs
  · have hin : HasUnguardedInput network := Or.inr (Or.inl trivial)
    exact False.elim ((input_cong hc).mp hin)
  · exact hs

/-- Both swapped private binders are tracked by the GENERAL global theorem. -/
theorem swapped_delegation_global_progress :
    Cong (.nu (.nu (swapProc 0 (.par sender (.par receiver peer))))) .nil ∨
    ∃ q, PiCalculus.Step (.nu (.nu (swapProc 0 (.par sender (.par receiver peer))))) q := by
  have ht := (RankedType.cong_iff (Cong.nu_swap (.par sender (.par receiver peer)))).mp network_ranked
  exact ht.progress_empty

/-- Progress at the actual two-step reachable residual is preservation plus
GLOBAL progress, not a theorem that ranks or every execution terminate. -/
theorem reachable_delegation_global_progress :
    Cong (.nu (.nu (.par .nil (.par .nil .nil)))) .nil ∨
      ∃ q, PiCalculus.Step (.nu (.nu (.par .nil (.par .nil .nil)))) q :=
  network_ranked.reachable_progress
    ((Relation.ReflTransGen.single network_transfer).tail network_use)

end Cslib.SessionTypes.Endpoint.DelegationTests
