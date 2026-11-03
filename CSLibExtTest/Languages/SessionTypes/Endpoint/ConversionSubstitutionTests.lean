/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.ConversionCommunication
import CSLibExt.Languages.SessionTypes.Endpoint.CongTyping

/-!
# Actual capability substitution with distinct semantic peer head codes

These tests invoke the GENERAL new theorems. The receiver advertises a
payload and continuation code different from the sender's, at equal ranks.
-/

namespace Cslib.SessionTypes.Endpoint.ConversionSubstitutionTests

open PiCalculus

def terminalGraph : Graph := ⟨1, fun _ => .done⟩
def terminalCode : Protocol := .regular terminalGraph ⟨0, by decide⟩ false
def advertised : Protocol := .sendName (.sendName .done)
def actualPayload : Protocol := .sendName (.sendName terminalCode)
def value : Capability := ⟨7, actualPayload⟩
def inputValue : Capability := ⟨7, advertised⟩
def e : Key := ⟨.var 0, .positive⟩
def f (r : Role) : Key := ⟨.var 1, r⟩
def sending (r : Role) : Capability := ⟨3, .sendEndpoint r 7 advertised .done⟩
def receiving (r : Role) : Capability := ⟨3, .recvEndpoint r 7 actualPayload terminalCode⟩
def Γ (r : Role) : Context := (Finmap.singleton e (sending r)).insert (f r) value
def Θ (r : Role) : Context := Finmap.singleton e.opposite (receiving r)
def q : Proc := .out (.var 0) (.const 11) (.out (.var 0) (.const 12) .nil)

theorem terminal_equivalent : terminalCode.TreeEquiv .done :=
  Protocol.treeEquiv_iff_head.mpr HeadMatch.done

theorem actual_equivalent : actualPayload.TreeEquiv advertised :=
  terminal_equivalent.sendName.sendName

theorem peer_equivalent (r : Role) : (receiving r).Equivalent (sending r).dual :=
  ⟨rfl, actual_equivalent.recvEndpoint terminal_equivalent r 7⟩

private theorem two_sends {n : Nat} {Δ : Context} {d : Key}
    (hc : Δ.Completed) (hs : ∀ e ∈ Δ, e.name.ClosedAt n) (hd : d.name.ClosedAt n) :
    Conversion.HasType n (Δ.insert d value)
      (.out d.name (.const 11) (.out d.name (.const 12) .nil)) := by
  apply Conversion.HasType.outName (e := d) (c := value) (s := .sendName terminalCode)
  · exact Finmap.lookup_insert _
  · rfl
  · exact hd
  · trivial
  · rw [Finmap.insert_insert]
    apply Conversion.HasType.outName (e := d) (c := ⟨7, .sendName terminalCode⟩) (s := terminalCode)
    · exact Finmap.lookup_insert _
    · rfl
    · exact hd
    · trivial
    · rw [Finmap.insert_insert]
      apply Conversion.HasType.nil (hc.insert rfl)
      intro x hx
      rcases Finmap.mem_insert.mp hx with rfl | hx
      · exact hd
      · exact hs x hx

theorem split (r : Role) : Finmap.Disjoint (Γ r) (Θ r) := by
  simp [Γ, Θ, e, f, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
    Key.opposite, Role.opposite]

theorem subject_lookup (r : Role) : (Γ r).lookup e = some (sending r) := by simp [Γ, e, f]
theorem payload_lookup (r : Role) : (Γ r).lookup (f r) = some value := Finmap.lookup_insert _

theorem sender_body (r : Role) : Conversion.HasType 2
    (((Γ r).erase (f r)).insert e ⟨3, .done⟩) .nil := by
  rw [Γ, Context.erase_insert_same, Context.erase_of_notMem (by simp [e, f]),
    Finmap.insert_singleton_eq]
  exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton (by change 0 < 2; decide))

theorem receiver_typed (r : Role) : Conversion.HasType 2 (Θ r) (.inp e.name q) := by
  apply Conversion.HasType.inpEndpoint (e := e.opposite) (c := receiving r) (r := r)
    (k := 7) (t := actualPayload) (s := terminalCode)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 1
  · rw [Θ, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply two_sends
    · exact (Endpoint.HasType.nil_singleton_completed (n := 3)
        (e := Key.mapName (liftName 0) e.opposite) (c := ⟨3, terminalCode⟩)
        (by change 1 < 3; decide) rfl).nil_inv.1
    · intro x hx
      have he := (Finmap.mem_singleton _ _ _).mp hx
      subst x
      change 1 < 3
      decide
    · exact Nat.zero_lt_succ 2

private theorem sender_lookup_total (r : Role) :
    (Γ r ∪ Θ r).lookup e = some (sending r) :=
  (Finmap.lookup_union_left (by simp [Γ])).trans (subject_lookup r)

private theorem receiver_lookup_total (r : Role) :
    (Γ r ∪ Θ r).lookup e.opposite = some (receiving r) := by
  rw [Finmap.lookup_union_right (by simp [Γ, e, f, Key.opposite, Role.opposite])]
  exact Finmap.lookup_singleton_eq

/-- The actual source is semantically compatible even though its two
carrier protocols are NOT literal syntactic duals. -/
theorem source_compatible (r : Role) : Conversion.Compatible (Γ r ∪ Θ r) := by
  intro x c d hc hd
  have hx := Finmap.mem_of_lookup_eq_some hc
  rcases Finmap.mem_union.mp hx with hx | hx
  · rcases Finmap.mem_insert.mp hx with hx | hx
    · subst x
      have ha : (f r).opposite ∉ Γ r ∪ Θ r := by
        cases r <;> simp [Γ, Θ, e, f, Key.opposite, Role.opposite]
      rw [Finmap.lookup_eq_none.mpr ha] at hd
      cases hd
    · have hx := (Finmap.mem_singleton _ _ _).mp hx
      subst x
      have hec := Context.unique hc (sender_lookup_total r)
      have hed := Context.unique hd (receiver_lookup_total r)
      subst c
      subst d
      exact peer_equivalent r
  · have hx := (Finmap.mem_singleton _ _ _).mp hx
    subst x
    have hec := Context.unique hc (receiver_lookup_total r)
    have hed : d = sending r := by
      simpa only [Key.opposite_opposite] using Context.unique hd (sender_lookup_total r)
    subst c
    subst d
    simpa only [Capability.dual_dual] using (peer_equivalent r).dual.symm

/-- GENERAL semantic endpoint-head preservation, with an arbitrary two-action
receiver and genuinely different advertised payload and continuation codes. -/
theorem semantic_head_preservation (r : Role) :
    ∃ d t u, (Θ r).lookup e.opposite = some d ∧ d.rank = 3 ∧
      d.protocol.unfold = .recvEndpoint r 7 t u ∧ t.TreeEquiv advertised ∧ u.TreeEquiv .done ∧
      Conversion.HasType 2 (((Γ r ∪ Θ r).insert e ⟨3, .done⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par .nil (PiCalculus.subst q (f r).name)) :=
  Conversion.endpoint_head_preservation (e := e) (f := f r) (c := sending r) (v := value)
    (t := advertised) (s := .done) (split r) (subject_lookup r) rfl (payload_lookup r)
    ⟨rfl, actual_equivalent⟩ (by simp [e, f]) (sender_body r) (receiver_typed r)
    (by change 1 < 2; decide) (source_compatible r)

/-- The payload's actual raw code/rank7 survives the literal two carrier updates. -/
theorem moved_payload_exact (r : Role) :
    (((Γ r ∪ Θ r).insert e ⟨3, .done⟩).insert e.opposite ⟨3, terminalCode⟩).lookup (f r) =
      some value :=
  Conversion.endpoint_payload_after (split r) (payload_lookup r) Finmap.lookup_singleton_eq
    (by simp [e, f]) _ _

/-- This semantic fixture cannot be described by old literal peer-code equality. -/
theorem peer_codes_not_equal (r : Role) : receiving r ≠ (sending r).dual := by
  intro h
  have ht := congrArg Capability.protocol h
  have he := (Protocol.recvEndpoint.inj ht).2.2.2
  cases he

theorem payload_codes_unequal : actualPayload ≠ advertised := by
  intro h
  have h1 := Protocol.sendName.inj h
  have h2 := Protocol.sendName.inj h1
  cases h2

private theorem advertised_body (r : Role) : Conversion.HasType 3
    ((Context.lift 0 (∅ : Context)).insert ⟨.var 0, r⟩ inputValue) q := by
  have ht := two_sends (n := 3) (Δ := ∅) (d := ⟨.var 0, r⟩)
    Context.completed_empty (by intro e he; exact False.elim (Finmap.notMem_empty he))
    (Nat.zero_lt_succ 2)
  have he : value.Equivalent inputValue := ⟨rfl, actual_equivalent⟩
  simpa only [Context.lift_empty, q] using ht.retype
    ((ContextEquivalent.refl (∅ : Context)).insert ⟨.var 0, r⟩ he)

/-- GENERAL advertised-A versus actual-B substitution supports all subject
positions of a two-action receiver, at the exact sent-key/code/rank7. -/
theorem actual_substitution (r : Role) : Conversion.HasType 2
    ((∅ : Context).insert (f r) value) (PiCalculus.subst q (.var 1)) :=
  (advertised_body r).subst_endpoint (Δ := ∅) (v := value) ⟨rfl, actual_equivalent⟩
    (by change 1 < 2; decide) Finmap.notMem_empty

/-- GENERAL lift and swap move actual owned subject keys through canonical
cutoffs while preserving the actual capability value. -/
theorem lift_swap_transport (r : Role) : Conversion.HasType 3
    (Context.swap 1 (Context.lift 0 ((∅ : Context).insert (f r) value)))
    (swapProc 1 (liftProc 0 (PiCalculus.subst q (.var 1)))) :=
  ((actual_substitution r).lift 0).swap (by decide : 1 + 1 < 3)

def aliasContext (r : Role) : Context := Finmap.singleton (f r).opposite value.dual
def aliasProc : Proc := .inp (.var 1) (.inp (.var 2) .nil)

private theorem alias_typed (r : Role) : Conversion.HasType 2 (aliasContext r) aliasProc := by
  apply Conversion.HasType.inpName (e := (f r).opposite) (c := value.dual)
    (s := .recvName terminalCode.dual)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 1 < 2
    decide
  · rw [aliasContext, Finmap.insert_singleton_eq, Context.lift_singleton]
    apply Conversion.HasType.inpName (e := Key.mapName (liftName 0) (f r).opposite)
      (c := ⟨7, .recvName terminalCode.dual⟩) (s := terminalCode.dual)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · change 2 < 3
      decide
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      apply Conversion.HasType.nil
      · intro x c hx
        have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hx)
        subst x
        simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hx
        subst c
        rfl
      · intro x hx
        have he := (Finmap.mem_singleton _ _ _).mp hx
        subst x
        change 3 < 4
        decide

/-- A same-physical-name OPPOSITE role remains owned during endpoint
substitution. Freshness excludes only the transmitted exact key, not its peer. -/
theorem legal_opposite_alias_substitution (r : Role) : Conversion.HasType 2
    ((aliasContext r).insert (f r) value)
    (.par (PiCalculus.subst q (.var 1)) aliasProc) := by
  have ht : Conversion.HasType 3
      ((Context.lift 0 (aliasContext r)).insert ⟨.var 0, r⟩ inputValue)
      (.par q (liftProc 0 aliasProc)) := by
    rw [← Finmap.empty_union (s₁ := Context.lift 0 (aliasContext r)), Finmap.insert_union]
    apply Conversion.HasType.par
    · simp [aliasContext, Context.lift_singleton, f, Key.opposite, Role.opposite,
        Key.mapName, liftName, Finmap.Disjoint, Finmap.mem_insert, Finmap.mem_singleton,
        Finmap.notMem_empty]
    · simpa only [Context.lift_empty] using advertised_body r
    · exact (alias_typed r).lift 0
  have he : value.Equivalent inputValue := ⟨rfl, actual_equivalent⟩
  have hf : f r ∉ aliasContext r := by
    cases r <;> simp [aliasContext, f, Key.opposite, Role.opposite]
  have hout := ht.subst_endpoint he (by change 1 < 2; decide) hf
  exact hout

/-- The general semantic head result has this exact literal receiver update,
not a normalized sender-dual continuation code. -/
theorem actual_receiver_tail_preserved (r : Role) : Conversion.HasType 2
    (((Γ r ∪ Θ r).insert e ⟨3, .done⟩).insert e.opposite ⟨3, terminalCode⟩)
    (.par .nil (PiCalculus.subst q (f r).name)) := by
  obtain ⟨d, t, u, hd, hr, hh, htp, hus, hout⟩ := semantic_head_preservation r
  have he : d = receiving r := Context.unique hd Finmap.lookup_singleton_eq
  subst d
  have hu := (Protocol.recvEndpoint.inj hh).2.2.2
  change terminalCode = u at hu
  subst u
  exact hout

/-- Actual canonical communication, separate from the proved typed residual. -/
theorem actual_communication_step (r : Role) : PiCalculus.Step
    (.par (.out e.name (f r).name .nil) (.inp e.name q))
    (.par .nil (PiCalculus.subst q (f r).name)) :=
  PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)

private theorem advertised_receiver_body (r : Role) : Conversion.HasType 3
    ((Context.lift 0 ((Θ r).insert e.opposite ⟨3, terminalCode⟩)).insert
      ⟨.var 0, r⟩ inputValue) q := by
  rw [Θ, Finmap.insert_singleton_eq, Context.lift_singleton]
  let Δ : Context := Finmap.singleton (Key.mapName (liftName 0) e.opposite) ⟨3, terminalCode⟩
  have ht := two_sends (n := 3) (Δ := Δ) (d := ⟨.var 0, r⟩)
    (Endpoint.HasType.nil_singleton_completed (n := 3)
      (e := Key.mapName (liftName 0) e.opposite) (c := ⟨3, terminalCode⟩)
      (by change 1 < 3; decide) rfl).nil_inv.1
    (by intro x hx; have he := (Finmap.mem_singleton _ _ _).mp hx; subst x; change 1 < 3; decide)
    (Nat.zero_lt_succ 2)
  simpa only [q] using ht.retype ((ContextEquivalent.refl Δ).insert ⟨.var 0, r⟩
    (show value.Equivalent inputValue from ⟨rfl, actual_equivalent⟩))

/-- GENERAL split-derived substitution uses actual payload ownership and old
receiver carrier lookup to derive fresh received-key transport. -/
theorem split_derived_substitution (r : Role) : Conversion.HasType 2
    (((Θ r).insert e.opposite ⟨3, terminalCode⟩).insert (f r) value)
    (PiCalculus.subst q (.var 1)) :=
  (advertised_receiver_body r).subst_endpoint_from_split (split r) (payload_lookup r)
    Finmap.lookup_singleton_eq ⟨rfl, actual_equivalent⟩ (by change 1 < 2; decide)

/-- Passive substitution crosses both input binders of a real typed peer
without creating ANY endpoint capability or changing the owned raw value. -/
theorem passive_substitution_no_capability (r : Role) :
    Conversion.HasType 2 (aliasContext r) aliasProc := by
  have ht := ((alias_typed r).lift 0).subst_passive (b := .const 99) trivial
  exact ht

private theorem raw_bound_body (r : Role) : Endpoint.HasType 3
    (Finmap.singleton (⟨.var 0, r⟩ : Key) inputValue) q := by
  apply Endpoint.HasType.outName (e := ⟨.var 0, r⟩) (c := inputValue) (s := .sendName .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 2
  · trivial
  · rw [Finmap.insert_singleton_eq]
    apply Endpoint.HasType.outName (e := ⟨.var 0, r⟩) (c := ⟨7, .sendName .done⟩) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 2
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact Endpoint.HasType.nil_singleton (Nat.zero_lt_succ 2)

/-- GENERAL substitution transports the received subject through an actual
nu scope, keeping the sent name lifted inside rather than capturing var0. -/
theorem nested_nu_substitution (r : Role) : Conversion.HasType 2
    ((∅ : Context).insert (f r) value)
    (.nu (.par .nil (liftProc 0 (PiCalculus.subst q (.var 1))))) := by
  have hn := (Endpoint.HasType.nil (n := 3) Context.completed_empty
    (by intro x hx; exact False.elim (Finmap.notMem_empty hx))).nu_nil_intro
  have hp := Endpoint.HasType.par (Finmap.disjoint_empty _) hn (raw_bound_body r)
  rw [Finmap.empty_union] at hp
  have hscope := hp.scope_forward
  have ht : Conversion.HasType 3
      ((Context.lift 0 (∅ : Context)).insert ⟨.var 0, r⟩ inputValue)
      (.nu (.par .nil (liftProc 0 q))) := by
    have he : (∅ : Context).insert ⟨.var 0, r⟩ inputValue =
        Finmap.singleton ⟨.var 0, r⟩ inputValue := by
      apply Finmap.ext
      rw [Finmap.entries_insert_of_notMem Finmap.notMem_empty]
      rfl
    rw [Context.lift_empty, he]
    exact Conversion.HasType.of_raw hscope
  have hout := ht.subst_endpoint (Δ := ∅) (v := value) (b := .var 1) ⟨rfl, actual_equivalent⟩
    (by change 1 < 2; decide) Finmap.notMem_empty
  exact hout

/-- Literal enclosing-rank mismatch fails independently of protocol equivalence. -/
theorem peer_rank_mismatch_rejected (r : Role) :
    ¬ (⟨4, (receiving r).protocol⟩ : Capability).Equivalent (sending r).dual := by
  intro h
  have hr := h.1
  change 4 = 3 at hr
  cases hr

/-- Wrong advertised role cannot be repaired by otherwise equivalent payloads. -/
theorem peer_role_mismatch_rejected (r : Role) :
    ¬ (receiving r.opposite).Equivalent (sending r).dual := by
  intro h
  have hh := h.2.head
  cases r <;> cases hh

/-- Matching advertised metadata cannot hide the wrong payload-tree direction. -/
theorem peer_tree_mismatch_rejected (r : Role) :
    ¬ (⟨3, .recvEndpoint r 7 (.recvName .done) terminalCode⟩ : Capability).Equivalent
      (sending r).dual := by
  intro h
  have hh := h.2.head
  cases hh with
  | recvEndpoint hp hs =>
    have hh' := hp.head
    cases hh'

def passiveSend : Capability := ⟨3, .sendName .done⟩
def passiveReceive : Capability := ⟨3, .recvName terminalCode⟩

/-- GENERAL passive head preservation also retains a receiver tail code
that is only semantically equal to the sender's dual tail. -/
theorem passive_head_consumer : Conversion.HasType 1
    (((Finmap.singleton e passiveSend ∪ Finmap.singleton e.opposite passiveReceive : Context).insert
      e ⟨3, .done⟩).insert e.opposite ⟨3, terminalCode⟩) (.par .nil .nil) := by
  have hd : Finmap.Disjoint (Finmap.singleton e passiveSend : Context)
      (Finmap.singleton e.opposite passiveReceive) := by
    simp [Finmap.Disjoint, Finmap.mem_singleton, e, Key.opposite, Role.opposite]
  have hp : Conversion.HasType 1
      ((Finmap.singleton e passiveSend : Context).insert e ⟨3, .done⟩) .nil := by
    rw [Finmap.insert_singleton_eq]
    exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton (Nat.zero_lt_succ 0))
  have hq : Conversion.HasType 1 (Finmap.singleton e.opposite passiveReceive)
      (.inp e.name .nil) := by
    apply Conversion.HasType.inpName (e := e.opposite) (c := passiveReceive) (s := terminalCode)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact Conversion.HasType.of_raw (Endpoint.HasType.nil_singleton_completed
        (by change 1 < 2; decide) rfl)
  have hc : Conversion.Compatible (Finmap.singleton e passiveSend ∪
      Finmap.singleton e.opposite passiveReceive : Context) := by
    have hr := (ContextEquivalent.refl (Finmap.singleton e passiveSend : Context)).union
      (ContextEquivalent.singleton e.opposite
        (show passiveSend.dual.Equivalent passiveReceive from
          ⟨rfl, terminal_equivalent.symm.recvName⟩))
    have hb : Conversion.Compatible (Finmap.singleton e passiveSend ∪
        Finmap.singleton e.opposite passiveSend.dual : Context) := by
      change Conversion.Compatible
        (Finmap.singleton ⟨.var 0, .positive⟩ passiveSend ∪
          Finmap.singleton ⟨.var 0, .negative⟩ passiveSend.dual)
      rw [← Context.bind_empty]
      exact Conversion.compatible_of_raw (balanced_bind_empty passiveSend).compatible
    exact hr.compatible hb
  obtain ⟨d, u, he, hr, hu, hs, hout⟩ := Conversion.passive_head_preservation
    (c := passiveSend) (s := .done) (b := .const 11) hd Finmap.lookup_singleton_eq
      rfl hp hq trivial hc
  have heq : d = passiveReceive := Context.unique he Finmap.lookup_singleton_eq
  subst d
  have hut := Protocol.recvName.inj hu
  change terminalCode = u at hut
  subst u
  exact hout

theorem source_pair_typed (r : Role) : Conversion.HasType 2 (Γ r ∪ Θ r)
    (.par (.out e.name (f r).name .nil) (.inp e.name q)) := by
  apply Conversion.HasType.par (split r)
  · exact Conversion.HasType.outEndpoint (subject_lookup r) rfl (payload_lookup r)
      (show value.Equivalent (⟨7, advertised⟩ : Capability) from ⟨rfl, actual_equivalent⟩)
      (by simp [e, f]) (by change 0 < 2; decide) (by change 1 < 2; decide) (sender_body r)
  · exact receiver_typed r

/-- The full source-typing wrapper is exercised, retaining source lookups,
rank/tail evidence and the exact two subject insertions in its conclusion. -/
theorem packed_head_consumer (r : Role) :
    ∃ a c d s u, a.name = e.name ∧ (Γ r ∪ Θ r).lookup a = some c ∧
      (Γ r ∪ Θ r).lookup a.opposite = some d ∧ d.rank = c.rank ∧ u.TreeEquiv s.dual ∧
      Conversion.HasType 2 (((Γ r ∪ Θ r).insert a ⟨c.rank, s⟩).insert a.opposite ⟨d.rank, u⟩)
        (.par .nil (PiCalculus.subst q (f r).name)) := by
  obtain ⟨a, c, d, s, u, hn, hc, hd, hr, ht, hh, hout⟩ :=
    (source_pair_typed r).head_preservation (source_compatible r)
  exact ⟨a, c, d, s, u, hn, hc, hd, hr, ht, hout⟩

/-- Actual source lookup refutes the old raw matched-pair premise at this
carrier; retyping a residual cannot create equality in the old source. -/
theorem raw_peer_premise_rejected (r : Role) :
    (Γ r ∪ Θ r).lookup e.opposite ≠ some (sending r).dual := by
  intro h
  exact peer_codes_not_equal r (Context.unique (receiver_lookup_total r) h)

/-- The general endpoint substitution inserts the ACTUAL raw code and rank,
not a recoded advertised value. -/
theorem substituted_value_lookup (r : Role) :
    ((∅ : Context).insert (f r) value).lookup (f r) = some value := Finmap.lookup_insert _

/-- Both payload role instances use the same generic substitution proof. -/
theorem positive_substitution : Conversion.HasType 2
    ((∅ : Context).insert (f .positive) value) (PiCalculus.subst q (.var 1)) :=
  actual_substitution .positive

theorem negative_substitution : Conversion.HasType 2
    ((∅ : Context).insert (f .negative) value) (PiCalculus.subst q (.var 1)) :=
  actual_substitution .negative

end Cslib.SessionTypes.Endpoint.ConversionSubstitutionTests
