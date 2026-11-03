/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveProgress

/-! # A genuinely sequential two-active-channel actor with service continuation -/

namespace Cslib.SessionTypes.Endpoint.CentralRuntimeProgressTests

open PiCalculus Endpoint.Runtime

private def capE : Capability := ⟨1, .sendName .done⟩
private def capD : Capability := ⟨3, .sendName .done⟩
private def endE : Capability := ⟨1, .done⟩
private def endD : Capability := ⟨3, .done⟩
private def keyE : Key := ⟨.var 0, .positive⟩
private def keyD : Key := ⟨.var 1, .positive⟩
private def own : Context := (Finmap.singleton keyE capE).insert keyD capD
private def env : ServiceEnv := Finmap.singleton 710 ⟨0, .positive, endD⟩
private def worker : Proc := .repl (.inp (.const 710) .nil)
private def actor : Proc := .out (.var 0) (.const 712)
  (.out (.var 1) (.const 712) (.out (.const 710) (.var 1) .nil))
private def network : Proc := .par actor
  (.par (.inp (.var 0) .nil) (.par (.inp (.var 1) .nil) worker))

private theorem end_nil (e : Key) (c : Capability) (hc : c.protocol.unfold = .done)
    (he : e.name.ClosedAt 2) (hn : ∀ s sig, env.lookup s = some sig → e.name ≠ .const s) :
    Runtime.HasType 2 env (Finmap.singleton e c) .nil := by
  apply Runtime.HasType.nil (Context.completed_empty.insert hc)
  · intro x hx
    have hxe := (Finmap.mem_singleton _ _ _).mp hx
    subst x
    exact he
  · exact separated_singleton hn

private theorem call_typed : Runtime.HasType 2 env (Finmap.singleton keyD endD)
    (.out (.const 710) (.var 1) .nil) := by
  apply Runtime.HasType.invoke (e := keyD) (v := endD) Finmap.lookup_singleton_eq
  · exact separated_singleton (by intro s sig hs hn; cases hn)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Capability.Equivalent.refl _
  · intro e c hc ha
    have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst e
    rw [Finmap.lookup_singleton_eq] at hc
    cases hc
    exact False.elim (ha rfl)
  · exact (by decide : 1 < 2)
  · rw [erase_singleton]
    exact nil_typed 2 env

private theorem actor_typed : Runtime.HasType 2 env own actor := by
  have hne : keyE ≠ keyD := by decide
  have hc := call_typed.weaken_completed (z := keyE) (u := endE)
    (by simp [Finmap.mem_singleton, hne]) rfl (Nat.zero_lt_succ 1)
    (by intro s sig hs hn; cases hn)
  have hd : Runtime.HasType 2 env ((Finmap.singleton keyD capD).insert keyE endE)
      (.out (.var 1) (.const 712) (.out (.const 710) (.var 1) .nil)) := by
    apply Runtime.HasType.outName (e := keyD) (c := capD) (s := .done)
      ((guardMin_singleton keyD capD).insert_completed (by rfl))
      ((separated_singleton (by intro s sig hs hn; cases hn)).insert keyE endE
        (by intro s sig hs hn; cases hn))
    · rw [Finmap.lookup_insert_of_ne _ hne.symm]
      exact Finmap.lookup_singleton_eq
    · rfl
    · exact (by decide : 1 < 2)
    · trivial
    · change Runtime.HasType 2 env
        (((Finmap.singleton keyD capD : Context).insert keyE endE).insert keyD endD) _
      rw [Finmap.insert_insert_of_ne (s := (Finmap.singleton keyD capD : Context))
          (a := keyE) (a' := keyD) hne, Finmap.insert_singleton_eq]
      exact hc
  apply Runtime.HasType.outName (e := keyE) (c := capE) (s := .done)
  · intro x c hx ha hxe
    by_cases hxd : x = keyD
    · subst x
      rw [own, Finmap.lookup_insert] at hx
      cases hx
      exact (by decide : 1 < 3)
    · rw [own, Finmap.lookup_insert_of_ne _ hxd] at hx
      have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hx)
      exact False.elim (hxe he)
  · exact (separated_singleton (by intro s sig hs hn; cases hn)).insert keyD capD
      (by intro s sig hs hn; cases hn)
  · rw [own, Finmap.lookup_insert_of_ne _ hne]
    exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 1
  · trivial
  · change Runtime.HasType 2 env
      (((Finmap.singleton keyE capE : Context).insert keyD capD).insert keyE endE) _
    rw [Finmap.insert_insert_of_ne (s := (Finmap.singleton keyE capE : Context))
        (a := keyD) (a' := keyE) hne.symm, Finmap.insert_singleton_eq]
    change Runtime.HasType 2 env (((∅ : Context).insert keyE endE).insert keyD capD) _
    rw [Finmap.insert_insert_of_ne (s := (∅ : Context)) hne]
    exact hd

private def peerE : Context := Finmap.singleton ⟨.var 0, .negative⟩ capE.dual
private def peerD : Context := Finmap.singleton ⟨.var 1, .negative⟩ capD.dual
private def whole : Context := own ∪ (peerE ∪ peerD)

private theorem receiver_typed (i k : Nat) (hi : i < 2) : Runtime.HasType 2 env
    (Finmap.singleton ⟨.var i, .negative⟩ (⟨k, .recvName .done⟩ : Capability))
    (.inp (.var i) .nil) := by
  apply Runtime.HasType.inpName (e := ⟨.var i, .negative⟩)
    (c := ⟨k, .recvName .done⟩) (s := .done) (guardMin_singleton _ _)
    (separated_singleton (by intro s sig hs hn; cases hn)) Finmap.lookup_singleton_eq rfl hi
  rw [Finmap.insert_singleton_eq]
  exact (end_nil ⟨.var i, .negative⟩ ⟨k, .done⟩ rfl hi
    (by intro s sig hs hn; cases hn)).lift 0

private theorem worker_typed : Runtime.HasType 2 env ∅ worker := by
  apply Runtime.HasType.serve_input Finmap.lookup_singleton_eq
  · apply Runtime.HasType.nil (Context.completed_empty.insert (by rfl))
    · intro e he
      have heq := (Finmap.mem_singleton _ _ _).mp he
      subst e
      exact Nat.zero_lt_succ 2
    · exact separated_singleton (by intro s sig hs hn; cases hn)
  · exact Context.completed_empty
  · intro e he
    exact False.elim (Finmap.notMem_empty he)
  · exact separated_empty env

private theorem network_typed : Runtime.HasType 2 env whole network := by
  have hd := Runtime.HasType.par (fun _ _ he => Finmap.notMem_empty he)
    (receiver_typed 1 3 (by decide)) worker_typed
  simp only [Finmap.union_empty] at hd
  have he := Runtime.HasType.par (by simp [Finmap.Disjoint, Finmap.mem_singleton])
    (receiver_typed 0 1 (by decide)) hd
  apply Runtime.HasType.par ?_ actor_typed he
  simp [Finmap.Disjoint, own, Finmap.mem_union,
    Finmap.mem_insert, Finmap.mem_singleton, keyE, keyD]

private theorem whole_bound : whole = Context.bind capE (Context.bind capD ∅) := by
  unfold whole own peerE peerD
  change (((∅ : Context).insert keyE capE).insert keyD capD ∪
    (((∅ : Context).insert ⟨.var 0, .negative⟩ capE.dual) ∪
      ((∅ : Context).insert ⟨.var 1, .negative⟩ capD.dual))) = _
  rw [← Finmap.insert_union, ← Finmap.insert_union, Finmap.empty_union,
    ← Finmap.insert_union, Finmap.empty_union]
  rw [Context.bind, Context.bind, Context.lift_insert, Context.lift_insert,
    Context.lift_empty, Context.lift_empty]
  change ((((∅ : Context).insert ⟨.var 1, .negative⟩ capD.dual).insert
      ⟨.var 0, .negative⟩ capE.dual).insert keyE capE).insert keyD capD =
    ((((∅ : Context).insert keyD capD).insert ⟨.var 1, .negative⟩ capD.dual).insert
      keyE capE).insert ⟨.var 0, .negative⟩ capE.dual
  rw [Finmap.insert_insert_of_ne (s := ((∅ : Context).insert ⟨.var 1, .negative⟩ capD.dual).insert
      ⟨.var 0, .negative⟩ capE.dual) (a := keyE) (a' := keyD) (by decide),
    Finmap.insert_insert_of_ne (s := (∅ : Context).insert ⟨.var 1, .negative⟩ capD.dual)
      (a := ⟨.var 0, .negative⟩) (a' := keyD) (by decide),
    Finmap.insert_insert_of_ne (s := (∅ : Context))
      (a := ⟨.var 1, .negative⟩) (a' := keyD) (by decide),
    Finmap.insert_insert_of_ne (s := ((∅ : Context).insert keyD capD).insert
      ⟨.var 1, .negative⟩ capD.dual) (a := ⟨.var 0, .negative⟩) (a' := keyE) (by decide)]

private theorem network_available : Available env network := by
  intro s sig hs
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hs)
  subst s
  exact Or.inr (Or.inr (Or.inr rfl))

/-- ONE actor owns both active channels, uses rank1 then rank3, and then invokes
an actual persistent service with the completed second endpoint. GENERAL runtime
progress, not a supplied execution, produces the connected balanced network Step. -/
theorem sequential_central_general_step :
    Runtime.HasType 2 env own actor ∧ own.lookup keyE = some capE ∧
    own.lookup keyD = some capD ∧ capE.protocol.unfold ≠ .done ∧
    capD.protocol.unfold ≠ .done ∧ Runtime.HasType 2 env whole network ∧
    Conversion.Balanced whole ∧ Available env network ∧ ∃ q, PiCalculus.Step network q := by
  have hb : Conversion.Balanced whole := by
    rw [whole_bound]
    exact (Conversion.balanced_empty.bind capD).bind capE
  have hs : ∃ q, PiCalculus.Step network q := by
    rcases network_typed.progress_balanced hb network_available with hi | hs
    · exact False.elim (hi.no_unguarded_output
        (show PiCalculus.HasUnguardedOutput network from Or.inl trivial))
    · exact hs
  refine ⟨actor_typed, ?_, Finmap.lookup_insert _, (by intro h; cases h),
    (by intro h; cases h), network_typed, hb, network_available, hs⟩
  rw [own, Finmap.lookup_insert_of_ne _ (by decide : keyE ≠ keyD)]
  exact Finmap.lookup_singleton_eq

end Cslib.SessionTypes.Endpoint.CentralRuntimeProgressTests
