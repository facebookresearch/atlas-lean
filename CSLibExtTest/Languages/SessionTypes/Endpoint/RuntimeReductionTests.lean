/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveReduction

/-!
# General runtime preservation with unequal advertised/actual endpoint codes
-/

namespace Cslib.SessionTypes.Endpoint.RuntimeReductionTests

open PiCalculus Endpoint.Runtime

private def actualB : Capability := ⟨7, recurringProtocol.unfold⟩
private def sendA (r : Role) : Capability := ⟨1, .sendEndpoint r 7 recurringProtocol .done⟩
private def recvB (r : Role) : Capability := ⟨1, .recvEndpoint r 7 recurringProtocol.unfold .done⟩
private def sendKey : Key := ⟨.var 0, .positive⟩
private def recvKey : Key := ⟨.var 0, .negative⟩
private def valueKey (r : Role) : Key := ⟨.var 1, r⟩
private def outContext (r : Role) : Context :=
  (Finmap.singleton (valueKey r) actualB).insert sendKey (sendA r)
private def inContext (r : Role) : Context := Finmap.singleton recvKey (recvB r)
private def sourceContext (r : Role) : Context := outContext r ∪ inContext r
private def residualContext (r : Role) : Context :=
  ((sourceContext r).insert sendKey ⟨1, .done⟩).insert recvKey ⟨1, .done⟩

private theorem advertised_peer_equivalent (r : Role) : (recvB r).Equivalent (sendA r).dual :=
  ⟨rfl, (Protocol.treeEquiv_unfold recurringProtocol).symm.recvEndpoint
    (Protocol.TreeEquiv.refl .done) r 7⟩

private theorem output_source (r : Role) : Runtime.HasType 2 (services r) (outContext r)
    (.out (.var 0) (.var 1) .nil) := by
  have hne : sendKey ≠ valueKey r := by intro h; cases h
  have hnil : Runtime.HasType 2 (services r)
      ((Finmap.singleton (valueKey r) actualB).erase (valueKey r)) .nil := by
    rw [erase_singleton]
    exact nil_typed 2 _
  have hbody := hnil.weaken_completed (z := sendKey) (u := ⟨1, .done⟩)
    (by rw [erase_singleton]; exact Finmap.notMem_empty) rfl (Nat.zero_lt_succ 1)
    (by intro s sig hs hn; cases hn)
  apply Runtime.HasType.outEndpoint (e := sendKey) (d := valueKey r) (c := sendA r)
    (v := actualB) (k := 7) (t := recurringProtocol) (s := .done)
  · intro d c hd ha hds
    rw [outContext, Finmap.lookup_insert_of_ne _ hds] at hd
    have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hd)
    subst d
    rw [Finmap.lookup_singleton_eq] at hd
    cases hd
    exact (by decide : 1 < 7)
  · exact (separated_singleton (by intro s sig hs hn; cases hn)).insert sendKey (sendA r)
      (by intro s sig hs hn; cases hn)
  · exact Finmap.lookup_insert _
  · rfl
  · rw [outContext, Finmap.lookup_insert_of_ne _ hne.symm]
    exact Finmap.lookup_singleton_eq
  · exact ⟨rfl, (Protocol.treeEquiv_unfold recurringProtocol).symm⟩
  · exact hne
  · exact Nat.zero_lt_succ 1
  · exact (by decide : 1 < 2)
  · rw [outContext, Context.erase_insert_ne hne, Finmap.insert_insert]
    exact hbody

private theorem input_source (r : Role) : Runtime.HasType 2 (services r) (inContext r)
    (.inp (.var 0) (senderRequest (.var 0))) := by
  have hp := (sender_request_typed r (.var 0) (Nat.zero_lt_succ 2)
    (by constructor <;> intro h <;> cases h)).retype
      (ContextEquivalent.singleton (⟨.var 0, r⟩ : Key) (c := recurringCap) (d := actualB)
        ⟨rfl, Protocol.treeEquiv_unfold recurringProtocol⟩)
  have hbody := hp.weaken_completed (z := ⟨.var 1, .negative⟩) (u := ⟨1, .done⟩)
    (by simp [Finmap.mem_singleton]) rfl (by decide : 1 < 3)
    (by intro s sig hs hn; cases hn)
  apply Runtime.HasType.inpEndpoint (e := recvKey) (c := recvB r)
    (r := r) (k := 7) (t := recurringProtocol.unfold) (s := .done)
    (guardMin_singleton _ _) (separated_singleton (by intro s sig hs hn; cases hn))
    Finmap.lookup_singleton_eq rfl (Nat.zero_lt_succ 1)
  rw [Finmap.insert_singleton_eq, Context.lift_singleton]
  change Runtime.HasType 3 (services r)
    (((∅ : Context).insert ⟨.var 1, .negative⟩ ⟨1, .done⟩).insert ⟨.var 0, r⟩ actualB) _
  rw [Finmap.insert_insert_of_ne (s := (∅ : Context)) (by intro h; cases h)]
  exact hbody

private theorem out_lookup (r : Role) : (sourceContext r).lookup sendKey = some (sendA r) := by
  rw [sourceContext, Finmap.lookup_union_left (by simp [outContext, Finmap.mem_insert]),
    outContext, Finmap.lookup_insert]

private theorem in_lookup (r : Role) : (sourceContext r).lookup recvKey = some (recvB r) := by
  rw [sourceContext, Finmap.lookup_union_right (by
    simp [outContext, sendKey, recvKey, valueKey, Finmap.mem_insert, Finmap.mem_singleton]),
    inContext, Finmap.lookup_singleton_eq]

private theorem value_lookup (r : Role) : (sourceContext r).lookup (valueKey r) = some actualB := by
  rw [sourceContext, Finmap.lookup_union_left (by simp [outContext, Finmap.mem_insert]),
    outContext, Finmap.lookup_insert_of_ne _ (by intro h; cases h), Finmap.lookup_singleton_eq]

private theorem source_lookup_cases {r : Role} {e : Key} {c : Capability}
    (hc : (sourceContext r).lookup e = some c) :
    (e = sendKey ∧ c = sendA r) ∨ (e = recvKey ∧ c = recvB r) ∨
      (e = valueKey r ∧ c = actualB) := by
  have hm := Finmap.mem_of_lookup_eq_some hc
  rcases Finmap.mem_union.mp hm with hm | hm
  · rcases Finmap.mem_insert.mp hm with he | he
    · subst e
      exact Or.inl ⟨rfl, Context.unique hc (out_lookup r)⟩
    · have heq := (Finmap.mem_singleton _ _ _).mp he
      subst e
      exact Or.inr (Or.inr ⟨rfl, Context.unique hc (value_lookup r)⟩)
  · have heq := (Finmap.mem_singleton _ _ _).mp hm
    subst e
    exact Or.inr (Or.inl ⟨rfl, Context.unique hc (in_lookup r)⟩)

private theorem value_peer_absent (r : Role) :
    (sourceContext r).lookup (valueKey r).opposite = none := by
  apply Finmap.lookup_eq_none.mpr
  cases r <;> simp [sourceContext, outContext, inContext, valueKey, sendKey, recvKey,
    Key.opposite, Role.opposite, Finmap.mem_union, Finmap.mem_insert, Finmap.mem_singleton]

private theorem source_compatible (r : Role) : Conversion.Compatible (sourceContext r) := by
  intro e c d hc hd
  rcases source_lookup_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have he := Context.unique hd (in_lookup r)
    subst d
    exact advertised_peer_equivalent r
  · have he := Context.unique hd (out_lookup r)
    subst d
    simpa only [Capability.dual_dual] using (advertised_peer_equivalent r).dual.symm
  · rw [value_peer_absent r] at hd
    cases hd

private theorem real_split (r : Role) : Finmap.Disjoint (outContext r) (inContext r) := by
  intro e he ht
  have heq := (Finmap.mem_singleton _ _ _).mp ht
  subst e
  simp [outContext, sendKey, recvKey, valueKey, Finmap.mem_insert, Finmap.mem_singleton] at he

private theorem linear_advance_target {r : Role} {Ξ : Context}
    (h : Conversion.SemanticAdvance (sourceContext r) Ξ) : Ξ = residualContext r := by
  cases h with
  | @matched e c d s u hc hd he hh ht =>
    rcases source_lookup_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hdc := Context.unique hd (in_lookup r)
      subst d
      cases hh with
      | passive hs hu => cases hs
      | endpoint hs hu heq =>
        change Protocol.sendEndpoint r 7 recurringProtocol .done = .sendEndpoint _ _ _ s at hs
        have hs' := (Protocol.sendEndpoint.inj hs).2.2.2
        subst s
        change Protocol.recvEndpoint r 7 recurringProtocol.unfold .done =
          .recvEndpoint _ _ _ u at hu
        have hu' := (Protocol.recvEndpoint.inj hu).2.2.2
        subst u
        rfl
    · cases hh with
      | passive hs hu => cases hs
      | endpoint hs hu heq => cases hs
    · rw [value_peer_absent r] at hd
      cases hd

/-- GENERAL runtime subject reduction forces a faithful LINEAR carrier advance
for this actual transfer with distinct advertised A/B codes. An identity residual
would still own an active carrier whose name is absent from the actual target. -/
theorem linear_step_exact (r : Role) :
    Runtime.HasType 2 (services r) (residualContext r)
      (.par .nil (senderRequest (.var 1))) ∧
      Conversion.SemanticAdvance (sourceContext r) (residualContext r) := by
  have hsource := Runtime.HasType.par (real_split r) (output_source r) (input_source r)
  have hs : PiCalculus.Step (.par (.out (.var 0) (.var 1) .nil)
      (.inp (.var 0) (senderRequest (.var 0)))) (.par .nil (senderRequest (.var 1))) :=
    PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)
  obtain ⟨Ξ, ht, hc, he⟩ := hsource.subject_reduction (source_compatible r) hs
  rcases he with hid | ha
  · subst Ξ
    have hdone := ht.absent_lookup_completed (out_lookup r)
      (by simp [NameAbsent, senderRequest, sendKey])
    cases hdone
  · have htarget := linear_advance_target ha
    exact ⟨htarget ▸ ht, htarget ▸ ha⟩

private theorem residual_send (r : Role) :
    (residualContext r).lookup sendKey = some (⟨1, .done⟩ : Capability) := by
  rw [residualContext, Finmap.lookup_insert_of_ne _ (by decide : sendKey ≠ recvKey),
    Finmap.lookup_insert]

private theorem residual_recv (r : Role) :
    (residualContext r).lookup recvKey = some (⟨1, .done⟩ : Capability) := Finmap.lookup_insert _

private theorem residual_value (r : Role) :
    (residualContext r).lookup (valueKey r) = some actualB := by
  rw [residualContext, Finmap.lookup_insert_of_ne _ (by intro h; cases h),
    Finmap.lookup_insert_of_ne _ (by intro h; cases h)]
  exact value_lookup r

private theorem residual_peer_absent (r : Role) :
    (residualContext r).lookup (valueKey r).opposite = none := by
  rw [residualContext, Finmap.lookup_insert_of_ne _ (by
    simp [valueKey, recvKey, Key.opposite]), Finmap.lookup_insert_of_ne _ (by
    simp [valueKey, sendKey, Key.opposite])]
  exact value_peer_absent r

private theorem residual_no_advance (r : Role) (Ξ : Context) :
    ¬ Conversion.SemanticAdvance (residualContext r) Ξ := by
  intro ha
  cases ha with
  | @matched e c d s u hc hd he hh ht =>
    have hm := ((linear_step_exact r).2.mem_iff e).mp (Finmap.mem_of_lookup_eq_some hc)
    obtain ⟨old, ho⟩ := Finmap.mem_iff.mp hm
    rcases source_lookup_cases ho with ⟨rfl, hcap⟩ | ⟨rfl, hcap⟩ | ⟨rfl, hcap⟩
    · have he := Context.unique hc (residual_send r)
      subst c
      cases hh with
      | passive hs hu => cases hs
      | endpoint hs hu heq => cases hs
    · have he := Context.unique hc (residual_recv r)
      subst c
      cases hh with
      | passive hs hu => cases hs
      | endpoint hs hu heq => cases hs
    · rw [residual_peer_absent r] at hd
      cases hd

/-- GENERAL runtime subject reduction forces exact identity at the subsequent
SHARED invocation: completed carrier slots cannot advance, and actual B has no
owned opposite peer. The transferred actual B/rank7 and both done slots remain. -/
theorem shared_step_identity (r : Role) : Runtime.HasType 2 (services r) (residualContext r)
    (.par (senderWorker (.var 1)) senderDaemon) := by
  have hrequest := (Runtime.HasType.cong_iff
    (Cong.trans (Cong.par_comm .nil _) (Cong.par_nil _))).mp (linear_step_exact r).1
  have hsource := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he)
    hrequest (sender_daemon_typed 2 r)
  simp only [Finmap.union_empty] at hsource
  have hco := (linear_step_exact r).2.compatible (source_compatible r)
  obtain ⟨Ξ, ht, hc, he⟩ := hsource.subject_reduction hco
    (service_invocation_step 710 (.var 1) (senderWorker (.var 0)))
  rcases he with hid | ha
  · exact hid ▸ ht
  · exact False.elim (residual_no_advance r Ξ ha)

/-- Exact observable interface metadata after BOTH actual reductions. -/
theorem residual_metadata_exact (r : Role) :
    (residualContext r).lookup ⟨.var 0, .positive⟩ = some (⟨1, .done⟩ : Capability) ∧
    (residualContext r).lookup ⟨.var 0, .negative⟩ = some (⟨1, .done⟩ : Capability) ∧
    (residualContext r).lookup ⟨.var 1, r⟩ = some (⟨7, recurringProtocol.unfold⟩ : Capability) :=
  ⟨residual_send r, residual_recv r, residual_value r⟩

/-- One ACTUAL two-Step network delegates then invokes the persistent recursive
service. GENERAL runtime preservation types every state; source carrier A and
receiver/actual B are unequal raw codes, and shared invocation is exact identity. -/
theorem general_delegate_invoke_trace (r : Role) :
    Runtime.HasType 2 (services r) (sourceContext r)
      (.par (.par (.out (.var 0) (.var 1) .nil)
        (.inp (.var 0) (senderRequest (.var 0)))) senderDaemon) ∧
    Runtime.HasType 2 (services r) (residualContext r)
      (.par (senderRequest (.var 1)) senderDaemon) ∧
    Runtime.HasType 2 (services r) (residualContext r)
      (.par (senderWorker (.var 1)) senderDaemon) ∧
    PiCalculus.Step
      (.par (.par (.out (.var 0) (.var 1) .nil)
        (.inp (.var 0) (senderRequest (.var 0)))) senderDaemon)
      (.par (senderRequest (.var 1)) senderDaemon) ∧
    PiCalculus.Step (.par (senderRequest (.var 1)) senderDaemon)
      (.par (senderWorker (.var 1)) senderDaemon) ∧
    recurringProtocol ≠ recurringProtocol.unfold := by
  have hactors := Runtime.HasType.par (real_split r) (output_source r) (input_source r)
  have hsource := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he) hactors
    (sender_daemon_typed 2 r)
  simp only [Finmap.union_empty] at hsource
  have hs : PiCalculus.Step
      (.par (.par (.out (.var 0) (.var 1) .nil)
        (.inp (.var 0) (senderRequest (.var 0)))) senderDaemon)
      (.par (senderRequest (.var 1)) senderDaemon) :=
    PiCalculus.Step.cong (Cong.refl _)
      (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
      (Cong.par_cong (Cong.trans (Cong.par_comm .nil _) (Cong.par_nil _)) (Cong.refl _))
  have hfirst : Runtime.HasType 2 (services r) (residualContext r)
      (.par (senderRequest (.var 1)) senderDaemon) := by
    obtain ⟨Ξ, ht, hc, he⟩ := hsource.subject_reduction (source_compatible r) hs
    rcases he with hid | ha
    · subst Ξ
      have hdone := ht.absent_lookup_completed (out_lookup r)
        (by simp [NameAbsent, senderRequest, senderDaemon, senderWorker, sendKey, liftName])
      cases hdone
    · exact linear_advance_target ha ▸ ht
  refine ⟨hsource, hfirst, shared_step_identity r, hs,
    service_invocation_step 710 (.var 1) (senderWorker (.var 0)), ?_⟩
  rw [recurring_unfold]
  intro h
  cases h

end Cslib.SessionTypes.Endpoint.RuntimeReductionTests
