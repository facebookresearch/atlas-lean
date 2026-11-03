/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeTemplateTyping

/-!
# Exact shared invocation head ownership transport

This is a head theorem, not general runtime Step preservation. The actual
transferred capability is retained literally in the unchanged combined interface.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem insert_empty_singleton (e : Key) (c : Capability) :
    (∅ : Context).insert e c = Finmap.singleton e c := rfl

/-- A declared shared invocation and ANY typed input worker preserve their EXACT
combined linear interface. The actual owned payload is substituted, not the
advertised raw protocol; completed receiver annotations remain ambient. -/
theorem HasType.shared_head {n : Nat} {Γ : ServiceEnv} {Δ Θ : Context}
    {s : Nat} {sig : ServiceSignature} {b : Name} {p q : Proc}
    (hs : Γ.lookup s = some sig) (hd : Finmap.Disjoint Δ Θ)
    (hout : HasType n Γ Δ (.out (.const s) b p))
    (hin : HasType n Γ Θ (.inp (.const s) q)) :
    HasType n Γ (Δ ∪ Θ) (.par p (PiCalculus.subst q b)) := by
  obtain ⟨e, v, he, hv, hr, hve, hpri, hp⟩ := hout.invoke_inv hs
  obtain ⟨hc, hscope, hsep, hq⟩ := hin.accept_inv hs
  rcases e with ⟨a, r⟩
  dsimp at he hr
  subst a
  subst r
  have hb := hout.lookup_closedAt hv
  have hshared := hout.separated ⟨b, sig.role⟩ v hv
  have hformal : HasType (n + 1) Γ
      ((Context.lift 0 ∅).insert ⟨.var 0, sig.role⟩ sig.capability) q := by
    simpa only [Context.lift_empty, insert_empty_singleton] using hq
  have hworker := hformal.subst_endpoint hve hb Finmap.notMem_empty hshared
  have hfresh : (⟨b, sig.role⟩ : Key) ∉ Θ := Context.fresh_of_disjoint hd hv
  have hsingleton : Finmap.Disjoint (Finmap.singleton ⟨b, sig.role⟩ v) Θ := by
    intro e he ht
    have heq := (Finmap.mem_singleton _ _ _).mp he
    exact hfresh (heq ▸ ht)
  simp only [insert_empty_singleton] at hworker
  have hworker' := hworker.weaken_completed_union hsingleton hc hscope hsep
  have hctx : Finmap.singleton ⟨b, sig.role⟩ v ∪ Θ = Θ.insert ⟨b, sig.role⟩ v := by
    rw [← insert_empty_singleton, ← Finmap.insert_union, Finmap.empty_union]
  rw [hctx] at hworker'
  have hd' : Finmap.Disjoint (Δ.erase ⟨b, sig.role⟩) (Θ.insert ⟨b, sig.role⟩ v) := by
    intro e he ht
    rcases Finmap.mem_insert.mp ht with h | ht
    · exact (Finmap.mem_erase.mp he).1 h
    · exact hd e (Finmap.mem_erase.mp he).2 ht
  have htyped := HasType.par hd' hp hworker'
  rw [Context.transfer_union hv] at htyped
  exact htyped

end Cslib.SessionTypes.Endpoint.Runtime
