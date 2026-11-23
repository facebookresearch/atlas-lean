/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RankedReduction

/-!
# Faithful head advancement, balance and disjoint partial-interface frames
-/

namespace Cslib.SessionTypes.Endpoint.ContextAdvanceTests

open PiCalculus

def sendCap : Capability := ⟨3, .sendName .done⟩
def sendKey : Key := ⟨.var 0, .positive⟩
def pairContext : Context := Context.bind sendCap ∅

/-- Actual head typing on a balanced, physically restriction-bound channel. -/
theorem heads_typed :
    HasType 1 pairContext (.par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)) := by
  rw [pairContext, Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply HasType.outName (e := sendKey) (c := sendCap) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [sendKey, Finmap.insert_singleton_eq]
      exact HasType.nil_singleton (Nat.zero_lt_succ 0)
  · apply HasType.inpName (e := ⟨.var 0, .negative⟩) (c := sendCap.dual) (s := .done)
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact HasType.nil_singleton (by change 1 < 2; decide)

/-- The faithful result gives a real typed residual and a matched update,
not an arbitrary existential context that forgets subject heads. -/
theorem actual_passive_advance :
    ∃ Ξ, DualAdvance pairContext Ξ ∧ HasType 1 Ξ (.par .nil .nil) ∧ Balanced Ξ := by
  obtain ⟨e, c, s, hn, hc, hp, hm, ht⟩ := heads_typed.head_comm_faithful
    (balanced_bind_empty sendCap).compatible
  have ha := DualAdvance.matched hc hp hm.sendsTo
  exact ⟨_, ha, ht, ha.balanced (balanced_bind_empty sendCap)⟩

def advanced : Context :=
  (pairContext.insert sendKey ⟨sendCap.rank, .done⟩).insert sendKey.opposite
    ⟨sendCap.rank, .done⟩

/-- The actual send head advances to done with the identical subject rank. -/
theorem explicit_passive_advance : DualAdvance pairContext advanced := by
  apply DualAdvance.matched
  · exact Context.lookup_bind_positive sendCap ∅
  · exact Context.lookup_bind_negative sendCap ∅
  · exact Or.inl rfl

/-- The positive role is still owned at rank three, at the actual done continuation. -/
theorem advanced_subject_exact : advanced.lookup sendKey = some ⟨3, .done⟩ :=
  dual_update_lookup_subject pairContext sendKey sendCap .done

def frameKey : Key := ⟨.const 10, .negative⟩
def frameCap : Capability := ⟨17, .recvName .done⟩
def frame : Context := Finmap.singleton frameKey frameCap

private theorem frame_disjoint : Finmap.Disjoint pairContext frame := by
  rw [pairContext, Context.bind_empty]
  simp [Finmap.Disjoint, Finmap.mem_union, Finmap.mem_singleton, frame, frameKey]

/-- Both frame orientations keep the actual matched update correspondence. -/
theorem framed_advance_both : DualAdvance (pairContext ∪ frame) (advanced ∪ frame) ∧
    DualAdvance (frame ∪ pairContext) (frame ∪ advanced) :=
  ⟨explicit_passive_advance.frame_left,
    explicit_passive_advance.frame_right (frame_disjoint.symm _ _)⟩

/-- The unrelated active partial-interface role keeps its entire old value. -/
theorem framed_role_unchanged : (advanced ∪ frame).lookup frameKey = some frameCap := by
  rw [Finmap.lookup_union_right]
  · exact Finmap.lookup_singleton_eq
  · intro he
    have he' := (explicit_passive_advance.mem_iff frameKey).mp he
    exact frame_disjoint frameKey he' (by simp [frame])

def endpointCap : Capability := ⟨3, .sendEndpoint .positive 5 .done .done⟩
def payloadKey : Key := ⟨.const 2, .positive⟩
def endpointContext : Context := (Context.bind endpointCap ∅).insert payloadKey ⟨5, .done⟩

/-- Endpoint payload evidence records its actual role, rank, protocol and
non-aliasing with BOTH subject roles, not just a send-shaped protocol. -/
theorem exact_endpoint_payload_head :
    MatchedOutput endpointContext sendKey endpointCap .done (.const 2) := by
  apply MatchedOutput.endpoint (d := payloadKey) (k := 5) (v := .done)
  · rfl
  · rfl
  · exact Finmap.lookup_insert _
  · decide
  · decide

/-- The endpoint case advances only the carrier pair at its literal head. -/
theorem explicit_endpoint_advance : DualAdvance endpointContext
    ((endpointContext.insert sendKey ⟨3, .done⟩).insert sendKey.opposite ⟨3, .done⟩) := by
  apply DualAdvance.matched (c := endpointCap)
  · rw [endpointContext, Finmap.lookup_insert_of_ne _ (by decide : sendKey ≠ payloadKey)]
    exact Context.lookup_bind_positive endpointCap ∅
  · rw [endpointContext, Finmap.lookup_insert_of_ne _
      (by decide : sendKey.opposite ≠ payloadKey)]
    exact Context.lookup_bind_negative endpointCap ∅
  · exact exact_endpoint_payload_head.sendsTo

/-- Transfer changes the owner, not the combined endpoint capability value. -/
theorem endpoint_payload_combined_value_unchanged :
    ((endpointContext.insert sendKey ⟨3, .done⟩).insert sendKey.opposite ⟨3, .done⟩).lookup
      payloadKey = some ⟨5, .done⟩ := by
  have ht := dual_update_lookup_other endpointContext sendKey payloadKey endpointCap .done
    (by decide) (by decide)
  change ((endpointContext.insert sendKey ⟨3, .done⟩).insert sendKey.opposite
    ⟨3, .done⟩).lookup payloadKey = endpointContext.lookup payloadKey at ht
  rw [ht]
  exact Finmap.lookup_insert _

def frameProcess : Proc := .inp frameKey.name .nil

private theorem frame_typed : HasType 1 frame frameProcess := by
  apply HasType.inpName (e := frameKey) (c := frameCap) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · rw [frame, Finmap.insert_singleton_eq, Context.lift_singleton]
    exact HasType.nil_singleton trivial

private theorem partial_compatible : Compatible (pairContext ∪ frame) := by
  intro e c d hc hd
  by_cases he : e = frameKey
  · subst e
    have hn : (pairContext ∪ frame).lookup frameKey.opposite = none := by
      rw [Finmap.lookup_union_right]
      · exact Finmap.lookup_eq_none.mpr (by simp [frame, frameKey, Key.opposite,
          Role.opposite, Finmap.mem_singleton])
      · rw [pairContext, Context.bind_empty]
        simp [Finmap.mem_union, Finmap.mem_singleton, frameKey, Key.opposite, Role.opposite]
    rw [hn] at hd
    cases hd
  · have hp : e.opposite ≠ frameKey := by
      intro hx
      have hn : (pairContext ∪ frame).lookup frameKey.opposite = none := by
        rw [Finmap.lookup_union_right]
        · exact Finmap.lookup_eq_none.mpr (by simp [frame, frameKey, Key.opposite,
          Role.opposite, Finmap.mem_singleton])
        · rw [pairContext, Context.bind_empty]
          simp [Finmap.mem_union, Finmap.mem_singleton, frameKey, Key.opposite, Role.opposite]
      have hx' : e = frameKey.opposite := by
        have hh := congrArg Key.opposite hx
        simpa only [Key.opposite_opposite] using hh
      rw [hx', hn] at hc
      cases hc
    have hce : pairContext.lookup e = some c := by
      rw [Finmap.lookup_union_left_of_not_in (by simpa [frame, Finmap.mem_singleton] using he)] at hc
      exact hc
    have hde : pairContext.lookup e.opposite = some d := by
      rw [Finmap.lookup_union_left_of_not_in (by simpa [frame, Finmap.mem_singleton] using hp)] at hd
      exact hd
    exact (balanced_bind_empty sendCap).compatible e c d hce hde

/-- General Step preservation handles a real active partial-interface frame
and returns exact zero-or-one external advancement, not an arbitrary map. -/
theorem general_framed_step : ∃ Ξ,
    HasType 1 Ξ (.par (.par .nil .nil) frameProcess) ∧ Compatible Ξ ∧
      (Ξ = pairContext ∪ frame ∨ DualAdvance (pairContext ∪ frame) Ξ) := by
  have ht := HasType.par frame_disjoint heads_typed frame_typed
  have hs : PiCalculus.Step
      (.par (.par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)) frameProcess)
      (.par (.par .nil .nil) frameProcess) :=
    PiCalculus.Step.parL (PiCalculus.Step.commSelect (.refl _) (.refl _))
  exact ht.subject_reduction partial_compatible hs

/-- The returned general-Step evidence forces the unrelated active frame
capability to remain exactly rank17/recvName done in this real reduction. -/
theorem general_framed_step_value_exact : ∃ Ξ,
    HasType 1 Ξ (.par (.par .nil .nil) frameProcess) ∧
      Ξ.lookup frameKey = some frameCap := by
  obtain ⟨Ξ, ht, hc, he⟩ := general_framed_step
  refine ⟨Ξ, ht, ?_⟩
  rcases he with rfl | ha
  · rw [Finmap.lookup_union_right (by
      rw [pairContext, Context.bind_empty]
      simp [Finmap.mem_union, Finmap.mem_singleton, frameKey])]
    exact Finmap.lookup_singleton_eq
  · cases ha with
    | @matched e c s hu hp hs =>
      have oldFrame : (pairContext ∪ frame).lookup frameKey = some frameCap := by
        rw [Finmap.lookup_union_right (by
          rw [pairContext, Context.bind_empty]
          simp [Finmap.mem_union, Finmap.mem_singleton, frameKey])]
        exact Finmap.lookup_singleton_eq
      have hne : frameKey ≠ e := by
        intro hh
        subst e
        have hv := Context.unique hu oldFrame
        subst c
        rcases hs with hs | ⟨r, k, v, hs⟩ <;> cases hs
      have hnp : frameKey ≠ e.opposite := by
        intro hh
        have hno : frameKey.opposite ∉ pairContext ∪ frame := by
          rw [pairContext, Context.bind_empty]
          simp [Finmap.mem_union, Finmap.mem_singleton, frame, frameKey,
            Key.opposite, Role.opposite]
        have hh' : frameKey.opposite = e := by
          have hh' := congrArg Key.opposite hh
          simpa only [Key.opposite_opposite] using hh'
        exact hno (hh'.symm ▸ Finmap.mem_of_lookup_eq_some hu)
      rw [dual_update_lookup_other _ e frameKey c s hne hnp]
      exact oldFrame

/-- Balanced open interfaces use the GENERAL all-Step balanced theorem. -/
theorem general_balanced_head_step : ∃ Ξ,
    HasType 1 Ξ (.par .nil .nil) ∧ Balanced Ξ ∧
      (Ξ = pairContext ∨ DualAdvance pairContext Ξ) :=
  heads_typed.subject_reduction_balanced (balanced_bind_empty sendCap)
    (PiCalculus.Step.commSelect (.refl _) (.refl _))

/-- The opposite parallel-frame orientation uses parR in the same generic
proof and preserves ordinary compatibility of the partial external interface. -/
theorem general_right_framed_step : ∃ Ξ,
    HasType 1 Ξ (.par frameProcess (.par .nil .nil)) ∧ Compatible Ξ ∧
      (Ξ = frame ∪ pairContext ∨ DualAdvance (frame ∪ pairContext) Ξ) := by
  have ht := HasType.par (frame_disjoint.symm _ _) frame_typed heads_typed
  have hc : Compatible (frame ∪ pairContext) := by
    rw [Finmap.union_comm_of_disjoint (frame_disjoint.symm _ _)]
    exact partial_compatible
  exact ht.subject_reduction hc
    (PiCalculus.Step.parR (PiCalculus.Step.commSelect (.refl _) (.refl _)))

private theorem heads_ranked :
    RankedType 1 pairContext (.par (.out (.var 0) (.const 7) .nil) (.inp (.var 0) .nil)) := by
  rw [pairContext, Context.bind_empty]
  apply RankedType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · apply RankedType.outName (e := sendKey) (c := sendCap) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · trivial
    · rw [sendKey, Finmap.insert_singleton_eq]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (Nat.zero_lt_succ 0))
  · apply RankedType.inpName (e := ⟨.var 0, .negative⟩) (c := sendCap.dual) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · exact Nat.zero_lt_succ 0
    · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
      exact RankedType.nil_of_hasType (HasType.nil_singleton (by change 1 < 2; decide))

private theorem frame_ranked : RankedType 1 frame frameProcess := by
  apply RankedType.inpName (e := frameKey) (c := frameCap) (s := .done)
  · exact guardMin_singleton _ _
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · rw [frame, Finmap.insert_singleton_eq, Context.lift_singleton]
    exact RankedType.nil_of_hasType (HasType.nil_singleton trivial)

/-- GENERAL ranked Step handles both actual parallel-frame constructors with
an active, unmatched external receive capability and exact update evidence. -/
theorem ranked_framed_step_both :
    (∃ Ξ, RankedType 1 Ξ (.par (.par .nil .nil) frameProcess) ∧ Compatible Ξ ∧
      (Ξ = pairContext ∪ frame ∨ DualAdvance (pairContext ∪ frame) Ξ)) ∧
    (∃ Ξ, RankedType 1 Ξ (.par frameProcess (.par .nil .nil)) ∧ Compatible Ξ ∧
      (Ξ = frame ∪ pairContext ∨ DualAdvance (frame ∪ pairContext) Ξ)) := by
  have hl := RankedType.par frame_disjoint heads_ranked frame_ranked
  have hr := RankedType.par (frame_disjoint.symm _ _) frame_ranked heads_ranked
  have hc : Compatible (frame ∪ pairContext) := by
    rw [Finmap.union_comm_of_disjoint (frame_disjoint.symm _ _)]
    exact partial_compatible
  exact ⟨hl.subject_reduction partial_compatible
      (PiCalculus.Step.parL (PiCalculus.Step.commSelect (.refl _) (.refl _))),
    hr.subject_reduction hc (PiCalculus.Step.parR (PiCalculus.Step.commSelect (.refl _) (.refl _)))⟩

/-- GENERAL ranked balanced-interface corollary on an actual open channel. -/
theorem ranked_balanced_head_step : ∃ Ξ, RankedType 1 Ξ (.par .nil .nil) ∧ Balanced Ξ ∧
    (Ξ = pairContext ∨ DualAdvance pairContext Ξ) :=
  heads_ranked.subject_reduction_balanced (balanced_bind_empty sendCap)
    (PiCalculus.Step.commSelect (.refl _) (.refl _))

/-- The actual map returned by GENERAL ranked preservation keeps the entire
unmatched active rank17 frame capability, not merely the frame's key. -/
theorem ranked_framed_value_exact : ∃ Ξ,
    RankedType 1 Ξ (.par (.par .nil .nil) frameProcess) ∧ Ξ.lookup frameKey = some frameCap := by
  obtain ⟨Ξ, ht, hc, he⟩ := ranked_framed_step_both.1
  have oldFrame : (pairContext ∪ frame).lookup frameKey = some frameCap := by
    rw [Finmap.lookup_union_right (by
      rw [pairContext, Context.bind_empty]
      simp [Finmap.mem_union, Finmap.mem_singleton, frameKey])]
    exact Finmap.lookup_singleton_eq
  refine ⟨Ξ, ht, ?_⟩
  rcases he with rfl | ha
  · exact oldFrame
  · cases ha with
    | @matched e c s hu hp hs =>
      have hne : frameKey ≠ e := by
        intro hh
        subst e
        have hv := Context.unique hu oldFrame
        subst c
        rcases hs with hs | ⟨r, k, v, hs⟩ <;> cases hs
      have hnp : frameKey ≠ e.opposite := by
        intro hh
        have hno : frameKey.opposite ∉ pairContext ∪ frame := by
          rw [pairContext, Context.bind_empty]
          simp [Finmap.mem_union, Finmap.mem_singleton, frame, frameKey,
            Key.opposite, Role.opposite]
        have hh' : frameKey.opposite = e := by
          have hh' := congrArg Key.opposite hh
          simpa only [Key.opposite_opposite] using hh'
        exact hno (hh'.symm ▸ Finmap.mem_of_lookup_eq_some hu)
      rw [dual_update_lookup_other _ e frameKey c s hne hnp]
      exact oldFrame

end Cslib.SessionTypes.Endpoint.ContextAdvanceTests
