/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing

/-!
# Passive names do not acquire subject capabilities
-/

namespace Cslib.SessionTypes.Endpoint.RejectionTests

open PiCalculus

/-- No role of a passive receive-bound name is present in the lifted context. -/
theorem passive_subject_rejected (n : Nat) (Δ : Context) (b : Name) (p : Proc) :
    ¬ HasType (n + 1) (Context.lift 0 Δ) (.out (.var 0) b p) := by
  intro h
  obtain ⟨r, c, hc⟩ := h.out_owned
  have hm := Finmap.mem_of_lookup_eq_some hc
  exact Context.fresh_lift Δ r hm

/-- Folding or unfolding structural congruence cannot smuggle replication
into the finite typed fragment. -/
theorem replication_via_cong_rejected {n : Nat} {Δ : Context} {p q : Proc}
    (hp : HasType n Δ p) (hc : Cong p (.repl q)) : False := by
  exact (finiteLinear_cong hc).mp hp.finiteLinear

/-- Without any retained peer role, the sender cannot use the transferred
physical channel again. This is role ownership, not a blanket name ban. -/
theorem sender_reuse_rejected (b : Name) (p : Proc) :
    ¬ HasType 2 (Finmap.singleton (⟨.var 1, .positive⟩ : Key) ⟨0, .done⟩)
      (.out (.var 0) b p) := by
  intro h
  obtain ⟨r, c, hc⟩ := h.out_owned
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
  have hn := congrArg Key.name he
  cases hn

/-- An active protocol cannot be discarded at nil. -/
theorem active_capability_at_nil_rejected (n : Nat) (e : Key) :
    ¬ HasType n (Finmap.singleton e ⟨0, .sendName .done⟩) .nil := by
  intro h
  have he := h.nil_inv.1 e ⟨0, .sendName .done⟩ Finmap.lookup_singleton_eq
  cases he

/-- A receive guard cannot consume an endpoint declared for sending,
regardless of the passive ambient name scope. -/
theorem wrong_polarity_rejected (n : Nat) (e : Key) (p : Proc) :
    ¬ HasType n (Finmap.singleton e ⟨0, .sendName .done⟩) (.inp e.name p) := by
  intro h
  obtain ⟨d, c, _, hc, hcase⟩ := h.inp_inv
  have hd := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
  subst d
  have he : c = (⟨0, .sendName .done⟩ : Capability) :=
    Context.unique hc Finmap.lookup_singleton_eq
  subst c
  rcases hcase with ⟨s, hs, _⟩ | ⟨r, k, t, s, hs, _⟩
  · change Protocol.sendName .done = .recvName s at hs
    cases hs
  · change Protocol.sendName .done = .recvEndpoint r k t s at hs
    cases hs

end Cslib.SessionTypes.Endpoint.RejectionTests
