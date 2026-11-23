/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.AdvanceProjection

/-!
# Internal and external restriction-update projection consumers
-/

namespace Cslib.SessionTypes.Endpoint.AdvanceProjectionTests

open PiCalculus

def frameKey : Key := ⟨.const 9, .negative⟩
def frameCap : Capability := ⟨19, .recvName (.sendName .done)⟩
def frame : Context := Finmap.singleton frameKey frameCap
def positiveCap : Capability := ⟨7, .sendName (.recvName .done)⟩
def positiveNext : Capability := ⟨7, .recvName .done⟩

/-- Positive internal sender: only the private pair advances. -/
theorem private_positive_advance :
    DualAdvance (Context.bind positiveCap frame) (Context.bind positiveNext frame) := by
  have ha : DualAdvance (Context.bind positiveCap frame)
      (((Context.bind positiveCap frame).insert (⟨.var 0, .positive⟩ : Key)
        ⟨positiveCap.rank, .recvName .done⟩).insert (⟨.var 0, .negative⟩ : Key)
          ⟨positiveCap.rank, (Protocol.recvName .done).dual⟩) :=
    DualAdvance.matched (Context.lookup_bind_positive positiveCap frame)
      (Context.lookup_bind_negative positiveCap frame) (Or.inl rfl)
  change DualAdvance (Context.bind positiveCap frame)
    (((Context.bind positiveCap frame).insert (⟨.var 0, .positive⟩ : Key)
      positiveNext).insert (⟨.var 0, .negative⟩ : Key) positiveNext.dual) at ha
  rw [Context.update_bound_positive] at ha
  exact ha

/-- The general projection theorem retains the exact external frame and rank. -/
theorem private_positive_projection :
    (∃ d, d.rank = positiveCap.rank ∧ Context.bind positiveNext frame = Context.bind d frame) ∨
      (∃ Δ', DualAdvance frame Δ' ∧ Context.bind positiveNext frame = Context.bind positiveCap Δ') :=
  private_positive_advance.project_bind

/-- The unrelated active frame keeps its complete protocol/rank/value. -/
theorem private_frame_exact :
    (Context.bind positiveNext frame).lookup frameKey = some frameCap := by
  exact Context.lookup_bind_outer.mpr (Finmap.lookup_singleton_eq)

def negativeCap : Capability := ⟨13, .recvName (.sendName .done)⟩
def negativeNext : Capability := ⟨13, .sendName .done⟩

/-- Negative internal sender: the new positive role is its dual continuation. -/
theorem private_negative_advance :
    DualAdvance (Context.bind negativeCap frame) (Context.bind negativeNext frame) := by
  have ha := DualAdvance.matched (Context.lookup_bind_negative negativeCap frame)
    (Context.lookup_bind_positive negativeCap frame) (Or.inl (show
      negativeCap.dual.protocol.unfold = .sendName (.recvName .done) from rfl))
  change DualAdvance (Context.bind negativeCap frame)
    (((Context.bind negativeCap frame).insert (⟨.var 0, .negative⟩ : Key)
      negativeNext.dual).insert (⟨.var 0, .positive⟩ : Key) negativeNext) at ha
  rw [Context.update_bound_negative] at ha
  exact ha

/-- The general projection also covers the negative orientation at rank13. -/
theorem private_negative_projection :
    (∃ d, d.rank = negativeCap.rank ∧ Context.bind negativeNext frame = Context.bind d frame) ∨
      (∃ Δ', DualAdvance frame Δ' ∧ Context.bind negativeNext frame = Context.bind negativeCap Δ') :=
  private_negative_advance.project_bind

/-- Both private residual interfaces are genuinely balanced pairs. -/
theorem private_pairs_balanced : Balanced (Context.bind positiveNext ∅) ∧
    Balanced (Context.bind negativeNext ∅) :=
  ⟨balanced_bind_empty _, balanced_bind_empty _⟩

def externalKey : Key := ⟨.const 4, .negative⟩
def externalCap : Capability := ⟨23, .sendEndpoint .positive 31 .done (.recvName .done)⟩
def external : Context :=
  ((Finmap.singleton externalKey externalCap).insert externalKey.opposite externalCap.dual).insert
    frameKey frameCap

def externalNext : Context :=
  (external.insert externalKey ⟨23, .recvName .done⟩).insert externalKey.opposite
    ⟨23, .sendName .done⟩

/-- External free carrier: its payload can be private, with no invented
external payload lookup; both actual subject lookups still determine the update. -/
theorem external_free_advance : DualAdvance external externalNext := by
  apply DualAdvance.matched (c := externalCap) (s := .recvName .done)
  · rw [external, Finmap.lookup_insert_of_ne _ (by decide : externalKey ≠ frameKey),
      Finmap.lookup_insert_of_ne _ (by decide : externalKey ≠ externalKey.opposite)]
    exact Finmap.lookup_singleton_eq
  · rw [external, Finmap.lookup_insert_of_ne _ (by decide : externalKey.opposite ≠ frameKey),
      Finmap.lookup_insert]
  · exact Or.inr ⟨.positive, 31, .done, rfl⟩

/-- An active private pair remains unchanged around the free matched carrier. -/
theorem free_under_private_advance :
    DualAdvance (Context.bind positiveCap external) (Context.bind positiveCap externalNext) :=
  external_free_advance.bind_outer positiveCap

/-- The projection theorem handles free external names without a closed-hole restriction. -/
theorem free_under_private_projection :
    (∃ d, d.rank = positiveCap.rank ∧
      Context.bind positiveCap externalNext = Context.bind d external) ∨
    (∃ Δ', DualAdvance external Δ' ∧
      Context.bind positiveCap externalNext = Context.bind positiveCap Δ') :=
  free_under_private_advance.project_bind

/-- The private pair's positive active capability is byte-for-byte unchanged. -/
theorem free_update_private_pair_exact :
    (Context.bind positiveCap externalNext).lookup (⟨.var 0, .positive⟩ : Key) =
      some positiveCap := Context.lookup_bind_positive _ _

/-- The unrelated external frame retains its rank19 and nonterminal protocol. -/
theorem free_update_frame_exact :
    (Context.bind positiveCap externalNext).lookup frameKey = some frameCap := by
  apply (Context.lookup_bind_outer (e := frameKey)).mpr
  rw [externalNext, Finmap.lookup_insert_of_ne _ (by decide : frameKey ≠ externalKey.opposite),
    Finmap.lookup_insert_of_ne _ (by decide : frameKey ≠ externalKey)]
  exact Finmap.lookup_insert _

def outerBound : Context := Context.bind positiveCap frame
def outerBoundNext : Context := Context.bind positiveNext frame

/-- An outer var0 pair advances before an additional restriction is entered. -/
theorem lifted_var_one_advance :
    DualAdvance (Context.bind negativeCap outerBound)
      (Context.bind negativeCap outerBoundNext) :=
  private_positive_advance.bind_outer negativeCap

/-- Under the added binder, the actual sender is var1, not the private var0. -/
theorem lifted_var_one_old_lookup :
    (Context.bind negativeCap outerBound).lookup (⟨.var 1, .positive⟩ : Key) =
      some positiveCap := by
  exact (Context.lookup_bind_outer (e := ⟨.var 0, .positive⟩)).mpr
    (Context.lookup_bind_positive positiveCap frame)

/-- General projection treats var1 as an outer pair and retains the new
private active rank13 pair without confusing the two binder indices. -/
theorem lifted_var_one_projection :
    (∃ d, d.rank = negativeCap.rank ∧
      Context.bind negativeCap outerBoundNext = Context.bind d outerBound) ∨
    (∃ Δ', DualAdvance outerBound Δ' ∧
      Context.bind negativeCap outerBoundNext = Context.bind negativeCap Δ') :=
  lifted_var_one_advance.project_bind

/-- The surviving private peer is still the exact rank13 dual capability. -/
theorem lifted_var_one_private_peer_exact :
    (Context.bind negativeCap outerBoundNext).lookup (⟨.var 0, .negative⟩ : Key) =
      some negativeCap.dual := Context.lookup_bind_negative _ _

/-- The actual outer carrier at var1 advances to rank7 recvName done. -/
theorem lifted_var_one_residual_exact :
    (Context.bind negativeCap outerBoundNext).lookup (⟨.var 1, .positive⟩ : Key) =
      some positiveNext := by
  exact (Context.lookup_bind_outer (e := ⟨.var 0, .positive⟩)).mpr
    (Context.lookup_bind_positive positiveNext frame)

/-- Both sender orientations advance an actually balanced private interface;
no typing, Step or caller-supplied result is assumed by projection. -/
theorem balanced_private_both_advances :
    (∃ Ξ, DualAdvance (Context.bind positiveCap ∅) Ξ ∧ Balanced Ξ) ∧
    (∃ Ξ, DualAdvance (Context.bind negativeCap ∅) Ξ ∧ Balanced Ξ) := by
  have hp := DualAdvance.matched (Context.lookup_bind_positive positiveCap ∅)
    (Context.lookup_bind_negative positiveCap ∅) (Or.inl (show
      positiveCap.protocol.unfold = .sendName (.recvName .done) from rfl))
  have hn := DualAdvance.matched (Context.lookup_bind_negative negativeCap ∅)
    (Context.lookup_bind_positive negativeCap ∅) (Or.inl (show
      negativeCap.dual.protocol.unfold = .sendName (.recvName .done) from rfl))
  exact ⟨⟨_, hp, hp.balanced (balanced_bind_empty _)⟩,
    ⟨_, hn, hn.balanced (balanced_bind_empty _)⟩⟩

/-- GENERAL faithful projection retains the actual private protocol transition,
not merely a residual capability with an equal rank. -/
theorem private_positive_faithful_projection :
    (∃ d, d.rank = positiveCap.rank ∧
      DualAdvance (Context.bind positiveCap ∅) (Context.bind d ∅) ∧
      Context.bind positiveNext frame = Context.bind d frame) ∨
    (∃ Δ', DualAdvance frame Δ' ∧ Context.bind positiveNext frame = Context.bind positiveCap Δ') :=
  private_positive_advance.project_bind_faithful

/-- The same faithful projection handles a negative private sender. -/
theorem private_negative_faithful_projection :
    (∃ d, d.rank = negativeCap.rank ∧
      DualAdvance (Context.bind negativeCap ∅) (Context.bind d ∅) ∧
      Context.bind negativeNext frame = Context.bind d frame) ∨
    (∃ Δ', DualAdvance frame Δ' ∧ Context.bind negativeNext frame = Context.bind negativeCap Δ') :=
  private_negative_advance.project_bind_faithful

end Cslib.SessionTypes.Endpoint.AdvanceProjectionTests
