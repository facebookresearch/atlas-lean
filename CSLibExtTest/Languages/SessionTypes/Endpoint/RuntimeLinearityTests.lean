/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress

/-! # Direct runtime endpoint removal and duplicate-transfer rejection -/

namespace Cslib.SessionTypes.Endpoint.RuntimeLinearityTests

open PiCalculus Endpoint.Runtime

private theorem endpoint_continuation {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    {e : Key} {c : Capability} {r : Role} {k : Nat} {t s : Protocol} {b : Name} {p : Proc}
    (h : Runtime.HasType n Γ Δ (.out e.name b p)) (he : Δ.lookup e = some c)
    (hu : ∀ f w, Δ.lookup f = some w → f.name = e.name → f = e)
    (hh : c.protocol.unfold = .sendEndpoint r k t s) :
    ∃ d v, d.name = b ∧ Δ.lookup d = some v ∧ d ≠ e ∧
      Runtime.HasType n Γ ((Δ.erase d).insert e ⟨c.rank, s⟩) p := by
  generalize ha : e.name = a at h
  generalize hb : b = b' at h
  cases h with
  | @outName _ _ _ f w _ u _ hg hd hw hn hscope hdata hp =>
    have hf := hu f w hw ha.symm
    subst f
    have hc := Context.unique hw he
    subst w
    rw [hh] at hn
    cases hn
  | @outEndpoint _ _ _ f d w v k' t' u _ hg hd hw hn hv hm hne hscope hdata hp =>
    have hf := hu f w hw ha.symm
    subst f
    have hc := Context.unique hw he
    subst w
    rw [hh] at hn
    cases hn
    exact ⟨d, v, rfl, hv, hne.symm, hp⟩
  | invoke hs hd hv hr heq hg hscope hp =>
    exact False.elim (hd e c he _ _ hs ha)

private theorem no_var_subject {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    {i : Nat} {b : Name} {p : Proc}
    (hn : ∀ e w, Δ.lookup e = some w → e.name ≠ .var i) :
    ¬ Runtime.HasType n Γ Δ (.out (.var i) b p) := by
  intro ht
  rcases ht.output_subject with ⟨e,w,he,hw⟩ | ⟨s,sig,he,hs⟩
  · exact hn e w hw he
  · cases he

/-- The actual var1→var0 endpoint transfer removes the ONLY var0 role. Its
runtime continuation cannot reuse that physical subject, for BOTH payload roles
and arbitrary runtime continuation p (including replicas/services). -/
theorem sender_reuse_runtime_rejected (r : Role) (b : Name) (p : Proc) :
    ¬ Runtime.HasType 2 ∅
      ((Finmap.singleton (⟨.var 1, .positive⟩ : Key)
        (⟨0, .sendEndpoint r 1 (.sendName .done) .done⟩ : Capability)).insert
        ⟨.var 0, r⟩ ⟨1, .sendName .done⟩)
      (.out (.var 1) (.var 0) (.out (.var 0) b p)) := by
  intro ht
  obtain ⟨d,v,hd,hv,hde,hp⟩ := endpoint_continuation
    (e := ⟨.var 1, .positive⟩)
    (c := ⟨0, .sendEndpoint r 1 (.sendName .done) .done⟩) ht
    (by rw [Finmap.lookup_insert_of_ne _ (by intro h; cases h)];
        exact Finmap.lookup_singleton_eq)
    (by
      intro f w hw hn
      rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hw) with he | he
      · subst f
        cases hn
      · exact (Finmap.mem_singleton _ _ _).mp he) rfl
  have hdk : d = (⟨.var 0, r⟩ : Key) := by
    rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hv) with he | he
    · exact he
    · have heq := (Finmap.mem_singleton _ _ _).mp he
      subst d
      cases hd
  subst d
  apply no_var_subject ?_ hp
  intro e w hw hn
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hw) with he | he
  · subst e
    cases hn
  · obtain ⟨hne,hold⟩ := Finmap.mem_erase.mp he
    rcases Finmap.mem_insert.mp hold with heq | heq
    · exact hne heq
    · have hx := (Finmap.mem_singleton _ _ _).mp heq
      subst e
      cases hn

/-- The same endpoint cannot be transferred AGAIN on another live carrier.
The first carrier has rank0, the second rank1, and the sole payload rank2, so
rank ordering admits the intended two-carrier sequence. FIRST actual runtime
transfer erases the payload; this covers BOTH payload orientations. -/
theorem duplicate_transfer_runtime_rejected (r : Role) (p : Proc) :
    ¬ Runtime.HasType 3 ∅
      (((Finmap.singleton (⟨.var 1, .positive⟩ : Key)
        (⟨0, .sendEndpoint r 2 (.sendName .done) .done⟩ : Capability)).insert
        ⟨.var 2, .positive⟩ ⟨1, .sendEndpoint r 2 (.sendName .done) .done⟩).insert
        ⟨.var 0, r⟩ ⟨2, .sendName .done⟩)
      (.out (.var 1) (.var 0) (.out (.var 2) (.var 0) p)) := by
  intro ht
  obtain ⟨d,v,hd,hv,hde,hp⟩ := endpoint_continuation
    (e := ⟨.var 1, .positive⟩)
    (c := ⟨0, .sendEndpoint r 2 (.sendName .done) .done⟩) ht
    (by
      rw [Finmap.lookup_insert_of_ne _ (by intro h; cases h),
        Finmap.lookup_insert_of_ne _ (by intro h; cases h)]
      exact Finmap.lookup_singleton_eq)
    (by
      intro f w hw hn
      rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hw) with he | he
      · subst f
        cases hn
      · rcases Finmap.mem_insert.mp he with he | he
        · subst f
          cases hn
        · exact (Finmap.mem_singleton _ _ _).mp he) rfl
  have hdk : d = (⟨.var 0, r⟩ : Key) := by
    rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hv) with he | he
    · exact he
    · rcases Finmap.mem_insert.mp he with he | he
      · subst d
        cases hd
      · have heq := (Finmap.mem_singleton _ _ _).mp he
        subst d
        cases hd
  subst d
  obtain ⟨d',v',hd',hv',hne',hq⟩ := endpoint_continuation
    (e := ⟨.var 2, .positive⟩)
    (c := ⟨1, .sendEndpoint r 2 (.sendName .done) .done⟩) hp
    (by
      rw [Finmap.lookup_insert_of_ne _ (by intro h; cases h),
        Finmap.lookup_erase_ne (by intro h; cases h),
        Finmap.lookup_insert_of_ne _ (by intro h; cases h), Finmap.lookup_insert])
    (by
      intro f w hw hn
      rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hw) with he | he
      · subst f
        cases hn
      · obtain ⟨hne,hold⟩ := Finmap.mem_erase.mp he
        rcases Finmap.mem_insert.mp hold with he | he
        · exact False.elim (hne he)
        · rcases Finmap.mem_insert.mp he with he | he
          · exact he
          · have hf := (Finmap.mem_singleton _ _ _).mp he
            subst f
            cases hn) rfl
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hv') with he | he
  · subst d'
    cases hd'
  · obtain ⟨hne,hold⟩ := Finmap.mem_erase.mp he
    rcases Finmap.mem_insert.mp hold with he | he
    · exact hne he
    · rcases Finmap.mem_insert.mp he with he | he
      · subst d'
        cases hd'
      · have hf := (Finmap.mem_singleton _ _ _).mp he
        subst d'
        cases hd'

/-- The duplicate fixture's first guard passes the static order: its other
active carrier has rank1 and the payload rank2, so rejection is not an equal-rank
shortcut. The endpoint-removal proof above does not assume rank rejection. -/
theorem duplicate_first_guard_admitted (r : Role) : GuardMin
    (((Finmap.singleton (⟨.var 1, .positive⟩ : Key)
      (⟨0, .sendEndpoint r 2 (.sendName .done) .done⟩ : Capability)).insert
      ⟨.var 2, .positive⟩ ⟨1, .sendEndpoint r 2 (.sendName .done) .done⟩).insert
      ⟨.var 0, r⟩ ⟨2, .sendName .done⟩) ⟨.var 1, .positive⟩ 0 := by
  intro e w hw ha hne
  by_cases h0 : e = (⟨.var 0,r⟩ : Key)
  · subst e
    rw [Finmap.lookup_insert] at hw
    cases hw
    exact (by decide : 0 < 2)
  · rw [Finmap.lookup_insert_of_ne _ h0] at hw
    by_cases h2 : e = (⟨.var 2,.positive⟩ : Key)
    · subst e
      rw [Finmap.lookup_insert] at hw
      cases hw
      exact Nat.zero_lt_one
    · rw [Finmap.lookup_insert_of_ne _ h2] at hw
      exact False.elim (hne ((Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hw)))

end Cslib.SessionTypes.Endpoint.RuntimeLinearityTests
