/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.ConversionRetyping
import CSLibExt.Languages.SessionTypes.Endpoint.CongTyping
import CSLibExt.Languages.SessionTypes.Endpoint.ContextAdvance

/-!
# Advertised finite code versus owned graph code in actual delegation

The receiver uses the received name as a subject; a third thread supplies
its opposite role for a second canonical communication. Both payload roles
are exercised. No general semantic preservation or progress is asserted
in this file.
-/

namespace Cslib.SessionTypes.Endpoint.ConversionTests

open PiCalculus

/-- A distinct three-state graph: its root sends then ends; the unused middle
state is a guarded receive cycle, so no code equality is assumed. -/
def payloadGraph : Graph := ⟨3, fun i => if i.val = 0 then .sendName ⟨2, by decide⟩
  else if i.val = 1 then .recvName ⟨1, by decide⟩ else .done⟩
def payloadCode : Protocol := .regular payloadGraph ⟨0, by decide⟩ false
def payloadEnd : Protocol := .regular payloadGraph ⟨2, by decide⟩ false

theorem payload_tree_equal : payloadCode.TreeEquiv (.sendName .done) :=
  Protocol.treeEquiv_iff_head.mpr
    (HeadMatch.sendName (Protocol.treeEquiv_iff_head.mpr HeadMatch.done))

theorem payload_codes_unequal : payloadCode ≠ .sendName .done := by
  intro h
  cases h

def carrier : Key := ⟨.const 0, .positive⟩
def receivedCarrier : Key := carrier.opposite
def payload (r : Role) : Key := ⟨.const 1, r⟩
def offer (r : Role) : Capability := ⟨0, .sendEndpoint r 7 (.sendName .done) .done⟩
def owned : Capability := ⟨7, payloadCode⟩
def finished : Capability := ⟨0, .done⟩
def left (r : Role) : Context := (Finmap.singleton carrier (offer r)).insert (payload r) owned
def right (r : Role) : Context := Finmap.singleton receivedCarrier (offer r).dual
def third (r : Role) : Context := Finmap.singleton (payload r).opposite owned.dual
def leftDone : Context := Finmap.singleton carrier finished
def rightDone : Context := Finmap.singleton receivedCarrier finished
def rightMoved (r : Role) : Context := rightDone.insert (payload r) owned
def whole (r : Role) : Context := left r ∪ (right r ∪ third r)

def sender : Proc := .out (.const 0) (.const 1) .nil
def receiver : Proc := .inp (.const 0) (.out (.var 0) (.const 7) .nil)
def peer : Proc := .inp (.const 1) .nil
def network : Proc := .par sender (.par receiver peer)
def afterTransfer : Proc := .par .nil (.par (.out (.const 1) (.const 7) .nil) peer)
def afterUse : Proc := .par .nil (.par .nil .nil)

theorem first_split (r : Role) : Finmap.Disjoint (left r) (right r ∪ third r) := by
  cases r <;> simp [left, right, third, carrier, receivedCarrier, payload,
    Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton, Key.opposite, Role.opposite]

theorem second_split (r : Role) : Finmap.Disjoint (right r) (third r) := by
  simp [right, third, carrier, receivedCarrier, payload, Finmap.Disjoint,
    Finmap.mem_singleton, Key.opposite, Role.opposite]

theorem sender_converted (r : Role) : Conversion.HasType 0 (left r) sender := by
  apply Conversion.HasType.outEndpoint (e := carrier) (d := payload r)
    (c := offer r) (v := owned) (k := 7) (t := .sendName .done) (s := .done)
  · simp [left, carrier, payload]
  · rfl
  · exact Finmap.lookup_insert _
  · exact ⟨rfl, payload_tree_equal⟩
  · simp [carrier, payload]
  · trivial
  · trivial
  · rw [left, Context.erase_insert_same, Context.erase_of_notMem (by simp [carrier, payload]),
      Finmap.insert_singleton_eq]
    exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton trivial)

theorem receiver_converted (r : Role) : Conversion.HasType 0 (right r) receiver := by
  apply Conversion.HasType.inpEndpoint (e := receivedCarrier) (c := (offer r).dual)
    (r := r) (k := 7) (t := .sendName .done) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · rw [right, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Conversion.one_action_tail
    · exact (Endpoint.HasType.nil_singleton (n := 1) (e := Key.mapName (liftName 0) receivedCarrier)
        (k := 0) trivial).nil_inv.1
    · intro e he
      have heq := (Finmap.mem_singleton _ _ _).mp he
      subst e
      trivial
    · exact Nat.zero_lt_succ 0
    · trivial
    · exact Protocol.TreeEquiv.refl _

theorem peer_converted (r : Role) : Conversion.HasType 0 (third r) peer := by
  apply Conversion.HasType.inpName (e := (payload r).opposite) (c := owned.dual)
    (s := payloadEnd.dual)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · rw [third, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Conversion.HasType.nil
    · intro e c he
      have heq := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some he)
      subst e
      simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at he
      subst c
      rfl
    · intro e he
      have heq := (Finmap.mem_singleton _ _ _).mp he
      subst e
      trivial

theorem source_converted (r : Role) : Conversion.HasType 0 (whole r) network :=
  Conversion.HasType.par (first_split r) (sender_converted r)
    (Conversion.HasType.par (second_split r) (receiver_converted r) (peer_converted r))

/-- The actual owned graph code, NOT the advertised constructor, supports the
received subject by the proved local one-action-tail conversion. -/
theorem moved_receiver_converted (r : Role) :
    Conversion.HasType 0 (rightMoved r) (.out (.const 1) (.const 7) .nil) := by
  apply Conversion.one_action_tail
  · exact (Endpoint.HasType.nil_singleton (n := 0) (e := receivedCarrier) (k := 0) trivial).nil_inv.1
  · intro e he
    have heq := (Finmap.mem_singleton _ _ _).mp he
    subst e
    trivial
  · trivial
  · trivial
  · exact payload_tree_equal.symm

/-- Actual canonical transfer, not a second execution relation. -/
theorem transfer_step : PiCalculus.Step network afterTransfer :=
  PiCalculus.Step.cong (Cong.symm (Cong.par_assoc _ _ _))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
    (Cong.par_assoc _ _ _)

/-- Actual second communication uses the received name as the subject. -/
theorem received_subject_step : PiCalculus.Step afterTransfer afterUse :=
  PiCalculus.Step.parR (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _))

def afterTransferContext (r : Role) : Context := leftDone ∪ (rightMoved r ∪ third r)
def rightUsed (r : Role) : Context := rightDone.insert (payload r) ⟨7, payloadEnd⟩
def peerUsed (r : Role) : Context := Finmap.singleton (payload r).opposite ⟨7, payloadEnd.dual⟩
def afterUseContext (r : Role) : Context := leftDone ∪ (rightUsed r ∪ peerUsed r)

private theorem singleton_lookup (x y : Key) (c : Capability) :
    (Finmap.singleton y c : Context).lookup x = if x = y then some c else none := by
  by_cases h : x = y
  · subst x
    simp
  · rw [ite_eq_right h]
    exact Finmap.lookup_eq_none.mpr (by simpa only [Finmap.mem_singleton] using h)

/-- Source peer compatibility is explicit. It does not imply raw payload
checking succeeds: the carrier advertises A but the actual slot owns B. -/
theorem source_compatible (r : Role) : Conversion.Compatible (whole r) := by
  apply Conversion.compatible_of_raw
  intro e c d hc hd
  cases r <;> cases e with
  | mk a role =>
    cases role <;> by_cases h0 : a = .const 0 <;> by_cases h1 : a = .const 1
    all_goals simp_all [whole, left, right, third, carrier, receivedCarrier, payload,
      Finmap.lookup_union_right, Finmap.mem_insert, Finmap.mem_singleton,
      Key.opposite, Role.opposite, singleton_lookup]
    all_goals subst a
    all_goals try simp_all [Finmap.lookup_insert]
    all_goals subst c
    all_goals exact (Capability.dual_dual d).symm

/-- The actual transfer residual retains the sender's raw B/rank7 slot. -/
theorem transfer_residual_converted (r : Role) :
    Conversion.HasType 0 (afterTransferContext r) afterTransfer := by
  apply Conversion.HasType.par
  · cases r <;> simp [leftDone, rightMoved, rightDone, third, carrier, receivedCarrier,
      payload, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
      Key.opposite, Role.opposite]
  · exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton trivial)
  · apply Conversion.HasType.par
    · cases r <;> simp [rightMoved, rightDone, third, carrier, receivedCarrier,
        payload, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
        Key.opposite, Role.opposite]
    · exact moved_receiver_converted r
    · exact peer_converted r

/-- After the second Step, all actual remaining graph cursors unfold to done. -/
theorem use_residual_converted (r : Role) :
    Conversion.HasType 0 (afterUseContext r) afterUse := by
  apply Conversion.HasType.par
  · cases r <;> simp [leftDone, rightUsed, rightDone, peerUsed, carrier, receivedCarrier,
      payload, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
      Key.opposite, Role.opposite]
  · exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton trivial)
  · apply Conversion.HasType.par
    · cases r <;> simp [rightUsed, rightDone, peerUsed, carrier, receivedCarrier,
        payload, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
        Key.opposite, Role.opposite]
    · apply Conversion.HasType.nil
      · exact (Endpoint.HasType.nil_singleton (n := 0) (e := receivedCarrier)
          (k := 0) trivial).nil_inv.1.insert rfl
      · intro e he
        rcases Finmap.mem_insert.mp he with rfl | he
        · trivial
        · have heq := (Finmap.mem_singleton _ _ _).mp he
          subst e
          trivial
    · apply Conversion.HasType.nil
      · intro e c he
        change (Finmap.singleton (payload r).opposite ⟨7, payloadEnd.dual⟩ : Context).lookup e = some c at he
        have heq := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some he)
        subst e
        simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at he
        subst c
        rfl
      · intro e he
        have heq := (Finmap.mem_singleton _ _ _).mp he
        subst e
        trivial

theorem whole_carrier (r : Role) : (whole r).lookup carrier = some (offer r) := by
  cases r <;> simp [whole, left, right, third, carrier, receivedCarrier, payload,
    Finmap.mem_insert, Finmap.mem_singleton, Key.opposite, Role.opposite]

theorem whole_receiver (r : Role) : (whole r).lookup receivedCarrier = some (offer r).dual := by
  cases r <;> simp [whole, left, right, third, carrier, receivedCarrier, payload,
    Finmap.lookup_union_right, Finmap.mem_insert, Finmap.mem_singleton,
    Key.opposite, Role.opposite]

theorem whole_payload (r : Role) : (whole r).lookup (payload r) = some owned := by
  exact (Finmap.lookup_union_left (by simp [left])).trans (Finmap.lookup_insert _)

/-- Raw typing fails at the SAME fixed advertised-A/owned-B interface,
regardless of the parallel ownership split chosen by a purported derivation. -/
theorem raw_same_interface_rejected (r : Role) : ¬ Endpoint.HasType 0 (whole r) network := by
  intro h
  obtain ⟨Γ, Θ, heq, hd, ho, hi⟩ := h.par_inv
  obtain ⟨e, c, hn, hc, hcase⟩ := ho.out_inv
  have hw : (whole r).lookup e = some c := by
    rw [heq]
    exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
  cases e with
  | mk a role =>
    change a = .const 0 at hn
    subst a
    cases role with
    | positive =>
      have hcc : c = offer r := Context.unique hw (whole_carrier r)
      subst c
      rcases hcase with ⟨s, hs, hp⟩ | ⟨d, k, t, s, hbn, hs, hv, hne, hp⟩
      · cases hs
      · obtain ⟨hr, hk, ht, hnext⟩ := Protocol.sendEndpoint.inj hs
        subst k
        subst t
        have hdkey : d = payload r := by
          cases d with
          | mk b role =>
            change b = .const 1 at hbn
            subst b
            change r = role at hr
            subst role
            rfl
        subst d
        have hvw : (whole r).lookup (payload r) = some ⟨7, .sendName .done⟩ := by
          rw [heq]
          exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
        have hprotocol := congrArg Capability.protocol (Context.unique hvw (whole_payload r))
        exact payload_codes_unequal hprotocol.symm
    | negative =>
      have hcc : c = (offer r).dual := Context.unique hw (whole_receiver r)
      subst c
      rcases hcase with ⟨s, hs, hp⟩ | ⟨d, k, t, s, hbn, hs, hv, hne, hp⟩ <;> cases hs

/-- Literal post-transfer lookup keeps raw B and rank7, not the advertised A. -/
theorem moved_payload_lookup (r : Role) :
    (rightMoved r).lookup (payload r) = some owned := Finmap.lookup_insert _

def advertisedContext (ownedRole advertisedRole : Role) (k : Nat) (t : Protocol) : Context :=
  (Finmap.singleton carrier (⟨0, .sendEndpoint advertisedRole k t .done⟩ : Capability)).insert
    (payload ownedRole) owned

/-- The ACTUAL conversion output rule requires independent literal metadata;
equivalent protocol fields alone never repair a wrong role or capability rank. -/
theorem advertised_metadata_necessary {r a : Role} {k : Nat} {t : Protocol}
    (h : Conversion.HasType 0 (advertisedContext r a k t) sender) :
    a = r ∧ k = 7 ∧ payloadCode.TreeEquiv t := by
  obtain ⟨e, c, hn, hc, hs⟩ := h.out_inv
  have hem := Finmap.mem_of_lookup_eq_some hc
  rcases Finmap.mem_insert.mp hem with he | he
  · subst e
    cases hn
  · have he := (Finmap.mem_singleton _ _ _).mp he
    subst e
    have hcc : c = ⟨0, .sendEndpoint a k t .done⟩ := by
      apply Option.some.inj
      have hc' := hc
      change ((Finmap.singleton carrier (⟨0, .sendEndpoint a k t .done⟩ : Capability) : Context).insert
        (payload r) owned).lookup carrier = some c at hc'
      rw [Finmap.lookup_insert_of_ne _ (show carrier ≠ payload r by simp [carrier, payload]),
        Finmap.lookup_singleton_eq] at hc'
      exact hc'.symm
    subst c
    rcases hs with ⟨s, hh⟩ | ⟨d, v, l, u, s, hdn, hd, hh, heq⟩
    · cases hh
    · have hdm := Finmap.mem_of_lookup_eq_some hd
      rcases Finmap.mem_insert.mp hdm with hkey | hkey
      · subst d
        have hv : v = owned := (Option.some.inj ((Finmap.lookup_insert _).symm.trans hd)).symm
        subst v
        obtain ⟨hr, hk, ht, hnext⟩ := Protocol.sendEndpoint.inj hh
        subst l
        subst u
        exact ⟨hr, heq.1.symm, heq.2⟩
      · have hkey := (Finmap.mem_singleton _ _ _).mp hkey
        subst d
        cases hdn

/-- Wrong payload rank is rejected by the actual seven-rule judgement. -/
theorem wrong_payload_rank_rejected (r : Role) :
    ¬ Conversion.HasType 0 (advertisedContext r r 8 (.sendName .done)) sender := by
  intro h
  have hk := (advertised_metadata_necessary h).2.1
  cases hk

/-- Wrong payload role is rejected even though both trees are equivalent. -/
theorem wrong_payload_role_rejected (r : Role) :
    ¬ Conversion.HasType 0 (advertisedContext r r.opposite 7 (.sendName .done)) sender := by
  intro h
  have hr := (advertised_metadata_necessary h).1
  cases r <;> cases hr

/-- Matching role/rank cannot hide a genuinely different payload tree. -/
theorem wrong_payload_tree_rejected (r : Role) :
    ¬ Conversion.HasType 0 (advertisedContext r r 7 (.recvName .done)) sender := by
  intro h
  have hh := (advertised_metadata_necessary h).2.2.head
  cases hh

/-- Wrong peer direction is rejected by semantic peer compatibility. -/
theorem wrong_peer_direction_rejected :
    ¬ (⟨0, .sendName .done⟩ : Capability).Equivalent (⟨0, .sendName .done⟩ : Capability).dual := by
  intro h
  have hh := h.2.head
  cases hh

/-- TreeEquiv does NOT justify changing an unrelated subject capability rank. -/
theorem unrelated_capability_rank_rejected :
    ¬ (⟨0, .done⟩ : Capability).Equivalent ⟨1, .done⟩ := by
  intro h
  cases h.1

/-- Both payload role orientations satisfy this concrete two-Step delegation
fixture, with typed source/residuals, compatibility and raw-typing rejection. -/
theorem both_roles_gate (r : Role) :
    Conversion.HasType 0 (whole r) network ∧ Conversion.Compatible (whole r) ∧
    PiCalculus.Step network afterTransfer ∧ PiCalculus.Step afterTransfer afterUse ∧
    Conversion.HasType 0 (afterTransferContext r) afterTransfer ∧
    Conversion.HasType 0 (afterUseContext r) afterUse ∧
    ¬ Endpoint.HasType 0 (whole r) network :=
  ⟨source_converted r, source_compatible r, transfer_step, received_subject_step,
    transfer_residual_converted r, use_residual_converted r, raw_same_interface_rejected r⟩

/-- Total post-transfer lookups preserve B/rank7, both carrier ranks0 and
the untouched third thread's exact peer capability value. -/
theorem transfer_metadata_exact (r : Role) :
    (afterTransferContext r).lookup (payload r) = some owned ∧
    (afterTransferContext r).lookup carrier = some finished ∧
    (afterTransferContext r).lookup receivedCarrier = some finished ∧
    (afterTransferContext r).lookup (payload r).opposite = some owned.dual := by
  cases r <;> simp [afterTransferContext, leftDone, rightMoved, rightDone, third,
    carrier, receivedCarrier, payload, Finmap.lookup_union_right,
    Finmap.mem_insert, Finmap.mem_singleton, Key.opposite, Role.opposite]

/-- A concrete wrong-direction peer interface fails semantic compatibility. -/
theorem wrong_peer_interface_rejected : ¬ Conversion.Compatible
    ((Finmap.singleton carrier (⟨0, .sendName .done⟩ : Capability) : Context).insert
      receivedCarrier ⟨0, .sendName .done⟩) := by
  intro h
  apply wrong_peer_direction_rejected
  apply h carrier ⟨0, .sendName .done⟩ ⟨0, .sendName .done⟩
  · simp [carrier, receivedCarrier, Key.opposite, Role.opposite]
  · exact Finmap.lookup_insert _

/-- Separate explicit consumers instantiate both quantified payload roles. -/
theorem positive_role_source : Conversion.HasType 0 (whole .positive) network :=
  (both_roles_gate .positive).1

theorem negative_role_source : Conversion.HasType 0 (whole .negative) network :=
  (both_roles_gate .negative).1

def recodedOffer (r : Role) : Capability := ⟨0, .sendEndpoint r 7 payloadCode .done⟩
def recodedOwned : Capability := ⟨7, .sendName .done⟩
def recodedLeft (r : Role) : Context :=
  (Finmap.singleton carrier (recodedOffer r)).insert (payload r) recodedOwned
def recodedRight (r : Role) : Context := Finmap.singleton receivedCarrier (recodedOffer r).dual
def recodedThird (r : Role) : Context := Finmap.singleton (payload r).opposite recodedOwned.dual
def recodedWhole (r : Role) : Context := recodedLeft r ∪ (recodedRight r ∪ recodedThird r)

theorem offer_equivalent (r : Role) : (offer r).Equivalent (recodedOffer r) :=
  ⟨rfl, payload_tree_equal.symm.sendEndpoint (Protocol.TreeEquiv.refl .done) r 7⟩

theorem owned_equivalent : owned.Equivalent recodedOwned := ⟨rfl, payload_tree_equal⟩

/-- Multiple keys change actual raw code, including opposite roles of one
physical name. The target parallel split is not a retyping hypothesis. -/
theorem recoded_whole_equivalent (r : Role) : ContextEquivalent (whole r) (recodedWhole r) :=
  ((ContextEquivalent.singleton carrier (offer_equivalent r)).insert (payload r) owned_equivalent).union
    ((ContextEquivalent.singleton receivedCarrier (offer_equivalent r).dual).union
      (ContextEquivalent.singleton (payload r).opposite owned_equivalent.dual))

theorem parallel_general_retyping (r : Role) :
    Conversion.HasType 0 (recodedWhole r) network :=
  (source_converted r).retype (recoded_whole_equivalent r)

theorem parallel_semantic_compatibility (r : Role) : Conversion.Compatible (recodedWhole r) :=
  (recoded_whole_equivalent r).compatible (source_compatible r)

/-- General retyping changes the endpoint input's advertised capability code,
while its arbitrary continuation still uses the received subject at rank7. -/
theorem endpoint_input_general_retyping (r : Role) :
    Conversion.HasType 0 (recodedRight r) receiver :=
  (receiver_converted r).retype (ContextEquivalent.singleton receivedCarrier (offer_equivalent r).dual)

/-- The original concrete delegation residual is a consumer of GENERAL
context retyping, not just the earlier one_action_tail helper. -/
theorem original_residual_general_retyping (r : Role) : Conversion.HasType 0
    (leftDone ∪ ((rightDone.insert (payload r) recodedOwned) ∪ third r)) afterTransfer :=
  (transfer_residual_converted r).retype
    ((ContextEquivalent.refl leftDone).union
      (((ContextEquivalent.refl rightDone).insert (payload r) owned_equivalent).union
        (ContextEquivalent.refl (third r))))

/-- Domain changes are rejected even for completed, equivalent protocols. -/
theorem domain_change_rejected : ¬ ContextEquivalent (∅ : Context)
    (Finmap.singleton carrier finished) := by
  intro h
  have hm := (h.mem_iff carrier).mpr (by simp)
  exact Finmap.notMem_empty hm

/-- Protocol equivalence alone cannot allow an enclosing capability rank change. -/
theorem context_rank_change_rejected : ¬ ContextEquivalent
    (Finmap.singleton carrier (⟨0, .done⟩ : Capability))
    (Finmap.singleton carrier (⟨1, .done⟩ : Capability)) := by
  intro h
  obtain ⟨d, hd, hr⟩ := h.lookup Finmap.lookup_singleton_eq
  simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hd
  subst d
  cases hr.1

/-- Completed graph cursors remain actually completed under GENERAL retyping. -/
theorem completed_graph_retyping : Conversion.HasType 0
    (Finmap.singleton carrier (⟨0, payloadEnd⟩ : Capability)) .nil := by
  have ht := Conversion.HasType.of_raw
    (Endpoint.HasType.nil_singleton (n := 0) (e := carrier) (k := 0) trivial)
  exact ht.retype (ContextEquivalent.singleton carrier
    ⟨rfl, Protocol.treeEquiv_iff_head.mpr HeadMatch.done⟩)

def twoActionReceiver : Proc :=
  .inp (.const 0) (.out (.var 0) (.const 7) (.out (.var 0) (.const 8) .nil))
def twoActionInput (r : Role) : Capability :=
  ⟨0, .recvEndpoint r 7 (.sendName (.sendName .done)) .done⟩
def twoActionInputRecoded (r : Role) : Capability :=
  ⟨0, .recvEndpoint r 7 (.sendName payloadCode) .done⟩

/-- A genuine endpoint input continuation consumes its received subject
TWICE, rather than testing only the one_action_tail fragment. -/
theorem two_action_raw_source (r : Role) : Endpoint.HasType 0
    (Finmap.singleton receivedCarrier (twoActionInput r)) twoActionReceiver := by
  apply Endpoint.HasType.inpEndpoint (e := receivedCarrier) (c := twoActionInput r)
    (r := r) (k := 7) (t := .sendName (.sendName .done)) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Endpoint.HasType.outName (e := ⟨.var 0, r⟩)
      (c := ⟨7, .sendName (.sendName .done)⟩) (s := .sendName .done)
    · exact Finmap.lookup_insert _
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [Finmap.insert_insert]
      apply Endpoint.HasType.outName (e := ⟨.var 0, r⟩) (c := ⟨7, .sendName .done⟩) (s := .done)
      · exact Finmap.lookup_insert _
      · rfl
      · exact Nat.zero_lt_succ 0
      · trivial
      · rw [Finmap.insert_insert]
        exact (Endpoint.HasType.nil_singleton (n := 1)
          (e := Key.mapName (liftName 0) receivedCarrier) (k := 0) trivial).nil_insert
          (c := ⟨7, .done⟩) rfl (Nat.zero_lt_succ 0)

private def idleWrap (p : Proc) : Proc := .nu (.par .nil (liftProc 0 p))

private theorem idleWrap_cong (p : Proc) : Cong p (idleWrap p) :=
  Cong.trans (Cong.symm (Cong.par_nil p))
    (Cong.trans (Cong.par_comm p .nil)
      (Cong.trans (Cong.par_cong (Cong.symm Cong.nu_nil) (Cong.refl p)) (Cong.scope .nil p)))

/-- GENERAL retyping enters two actual private ν binders and an input binder,
with an active received payload at rank7 and two sequential subject actions. -/
theorem nested_input_general_retyping (r : Role) : Conversion.HasType 0
    (Finmap.singleton receivedCarrier (twoActionInputRecoded r))
    (idleWrap (idleWrap twoActionReceiver)) := by
  have hraw := (Endpoint.HasType.cong_iff
    (Cong.trans (idleWrap_cong twoActionReceiver) (idleWrap_cong (idleWrap twoActionReceiver)))).mp
    (two_action_raw_source r)
  have heq : (twoActionInput r).Equivalent (twoActionInputRecoded r) :=
    ⟨rfl, payload_tree_equal.symm.sendName.recvEndpoint (Protocol.TreeEquiv.refl .done) r 7⟩
  exact (Conversion.HasType.of_raw hraw).retype (ContextEquivalent.singleton receivedCarrier heq)

/-- Machine-checked link from the concrete transfer residual to the literal
two carrier insertions. The raw relation applies to this exact-dual fixture,
not to arbitrary semantic-compatible conversion typing. -/
theorem transfer_context_literal_update (r : Role) :
    afterTransferContext r = ((whole r).insert carrier finished).insert receivedCarrier finished := by
  have hl : ((left r).erase (payload r)).insert carrier finished = leftDone := by
    rw [left, Context.erase_insert_same, Context.erase_of_notMem (by simp [carrier, payload]),
      Finmap.insert_singleton_eq]
    rfl
  have hr : ((right r ∪ third r).insert receivedCarrier finished).insert (payload r) owned =
      rightMoved r ∪ third r := by
    rw [Finmap.insert_union, Finmap.insert_union]
    simp only [right, Finmap.insert_singleton_eq]
    rfl
  have hu := Context.transfer_union_insert_owned (Δ := left r) (Θ := right r ∪ third r)
    (e := carrier) (f := receivedCarrier) (d := payload r) (c := finished) (t := finished)
    (first_split r) (by simp [left, carrier, payload])
    (by simp [right]) (Finmap.lookup_insert _) (by simp [carrier, payload])
  simpa only [hl, hr, afterTransferContext, whole] using hu

theorem transfer_actual_raw_advance (r : Role) : DualAdvance (whole r) (afterTransferContext r) := by
  rw [transfer_context_literal_update]
  exact DualAdvance.matched (whole_carrier r) (whole_receiver r) (Or.inr ⟨r, 7, .sendName .done, rfl⟩)

/-- The second concrete residual is exactly the two payload-subject advances,
with carrier frame values unchanged and actual graph tails retained. -/
theorem use_context_literal_update (r : Role) : afterUseContext r =
    ((afterTransferContext r).insert (payload r) ⟨7, payloadEnd⟩).insert
      (payload r).opposite ⟨7, payloadEnd.dual⟩ := by
  have hf : payload r ∉ leftDone := by simp [leftDone, carrier, payload]
  have hg : (payload r).opposite ∉ leftDone := by simp [leftDone, carrier, payload, Key.opposite]
  have hs : (payload r).opposite ∉ rightMoved r := by
    cases r <;> simp [rightMoved, rightDone, carrier, receivedCarrier, payload, Key.opposite, Role.opposite]
  rw [afterTransferContext, Context.insert_union_right_of_fresh hf,
    Context.insert_union_right_of_fresh hg]
  rw [Finmap.insert_union, Context.insert_union_right_of_fresh]
  · simp only [rightMoved, Finmap.insert_insert, third, Finmap.insert_singleton_eq]
    rfl
  · simpa only [Finmap.mem_insert, not_or] using
      (show (payload r).opposite ≠ payload r ∧ (payload r).opposite ∉ rightMoved r from
        ⟨by cases r <;> simp [payload, Key.opposite, Role.opposite], hs⟩)

theorem use_actual_raw_advance (r : Role) : DualAdvance (afterTransferContext r) (afterUseContext r) := by
  rw [use_context_literal_update]
  exact DualAdvance.matched (transfer_metadata_exact r).1
    (transfer_metadata_exact r).2.2.2 (Or.inl rfl)

/-- The target split is derived from the equivalent whole map, with each
child retaining exactly its original key domain. -/
theorem parallel_split_domains (r : Role) :
    ∃ Γ Θ, recodedWhole r = Γ ∪ Θ ∧ Finmap.Disjoint Γ Θ ∧
      (∀ e, e ∈ left r ↔ e ∈ Γ) ∧ (∀ e, e ∈ right r ∪ third r ↔ e ∈ Θ) := by
  obtain ⟨Γ, Θ, hu, hd, hΓ, hΘ⟩ := (recoded_whole_equivalent r).split (first_split r)
  exact ⟨Γ, Θ, hu, hd, hΓ.mem_iff, hΘ.mem_iff⟩

/-- Changing the moved payload's representation leaves the total peer-frame
lookup literally unchanged, not merely equivalent. -/
theorem retyped_residual_frame_exact (r : Role) :
    (leftDone ∪ ((rightDone.insert (payload r) recodedOwned) ∪ third r)).lookup
      (payload r).opposite = some owned.dual := by
  cases r <;> simp [leftDone, rightDone, third, carrier, receivedCarrier, payload,
    Finmap.lookup_union_right, Finmap.mem_insert, Finmap.mem_singleton,
    Key.opposite, Role.opposite]

end Cslib.SessionTypes.Endpoint.ConversionTests
