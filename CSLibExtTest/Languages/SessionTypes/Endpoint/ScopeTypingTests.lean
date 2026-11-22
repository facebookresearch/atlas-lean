/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.ScopeTyping

/-!
# Scope extrusion with a genuinely restricted subject

The bound sender/receiver pattern follows the same-repository BoundTests
consumer, using the unchanged public typing constructors.
-/

namespace Cslib.SessionTypes.Endpoint.ScopeTypingTests

open PiCalculus

def positive : Key := ⟨.var 0, .positive⟩
def negative : Key := ⟨.var 0, .negative⟩
def sending : Capability := ⟨0, .sendName .done⟩
def sender : Proc := .out (.var 0) (.const 7) .nil
def receiver : Proc := .inp (.var 0) .nil
def body : Proc := .par sender receiver

/-- The sender uses the actual surrounding restriction's subject name. -/
theorem sender_typed : HasType 1 (Finmap.singleton positive sending) sender := by
  apply HasType.outName (e := positive) (c := sending) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 0 < 1
    decide
  · trivial
  · rw [Finmap.insert_singleton_eq]
    exact HasType.nil_singleton (by change 0 < 1; decide)

/-- The other live guard owns the negative role of that same bound name. -/
theorem receiver_typed :
    HasType 1 (Finmap.singleton negative sending.dual) receiver := by
  apply HasType.inpName (e := negative) (c := sending.dual) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 0 < 1
    decide
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact HasType.nil_singleton (by change 1 < 2; decide)

/-- Both live roles are allocated by one real restriction. -/
theorem restricted_typed : HasType 0 ∅ (.nu body) := by
  apply HasType.nu (c := sending)
  rw [Context.bind_empty]
  apply HasType.par
  · simp [Finmap.Disjoint, Finmap.mem_singleton]
  · exact sender_typed
  · exact receiver_typed

def outer : Key := ⟨.const 5, .positive⟩
def outerContext : Context := Finmap.singleton outer sending
def partner : Proc := .out outer.name (.const 6) .nil

/-- A nonempty unrelated outer partner remains outside the fresh binder. -/
theorem partner_typed : HasType 0 outerContext partner := by
  apply HasType.outName (e := outer) (c := sending) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [outerContext, Finmap.insert_singleton_eq]
    exact HasType.nil_singleton trivial

/-- The general forward rule transports a live restricted pair beside a
nonempty outer partner; no closed-hole restriction is added to the theorem. -/
theorem scope_forward_real_bound_subject :
    HasType 0 outerContext (.nu (.par body (liftProc 0 partner))) := by
  have hsource : HasType 0 outerContext (.par (.nu body) partner) := by
    have ht := HasType.par (Finmap.disjoint_empty outerContext)
      restricted_typed partner_typed
    simpa only [Finmap.empty_union] using ht
  exact hsource.scope_forward

/-- Canonical lifting is fresh even in nested subjects and payload positions. -/
theorem nested_partner_fresh : NameAbsent (.var 0)
    (liftProc 0 (.inp (.var 0) (.nu (.out (.var 1) (.var 0) .nil)))) :=
  nameAbsent_fresh_lift 0 _

/-- Reverse scope also handles the same actual live restricted subject. -/
theorem scope_reverse_real_bound_subject :
    HasType 0 outerContext (.par (.nu body) partner) :=
  scope_forward_real_bound_subject.scope_reverse

end Cslib.SessionTypes.Endpoint.ScopeTypingTests
