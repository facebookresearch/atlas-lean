/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeRetyping
public import CSLibExt.Languages.SessionTypes.Endpoint.TypingTransport

/-!
# Static name-map conditions for unchanged shared permissions

Fixing declared constants does not by itself prevent a linear variable from
mapping to one. Nonalias is checked ONLY on actual owned keys, permitting
passive input substitution of a shared constant when var0 is not owned.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Name map fixing every declared shared constant.**
A name map leaves every declared shared constant literally fixed. -/
def FixesShared (Γ : ServiceEnv) (f : Name → Name) : Prop :=
  ∀ s sig, Γ.lookup s = some sig → f (.const s) = .const s

/-- **Nonaliasing of owned-name images with shared constants.**
Actual owned-key images cannot alias a declared shared physical name. -/
def NonAliases (Γ : ServiceEnv) (Δ : Context) (f : Name → Name) : Prop :=
  ∀ e ∈ Δ, ∀ s sig, Γ.lookup s = some sig → f e.name ≠ .const s

/-- **Binder extension preserves fixing of shared constants.**
Binder extension still fixes shared constants, which are unchanged by lifting. -/
theorem FixesShared.under {Γ : ServiceEnv} {f : Name → Name} (h : FixesShared Γ f) :
    FixesShared Γ (under f) := by
  intro s sig hs
  change liftName 0 (f (.const s)) = .const s
  rw [h s sig hs]
  rfl

/-- **Rekeying along a nonaliasing name map yields separation.**
The actual target ownership rekey has static name separation, not a desired type result. -/
theorem NonAliases.separated {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    Separated Γ (Context.rekey (Key.mapName f) Δ hf) := by
  intro e c hc s sig hs
  obtain ⟨d, hd, rfl⟩ := Context.lookup_rekey.mp hc
  exact h d (Finmap.mem_of_lookup_eq_some hd) s sig hs

/-- **Erasing an owned key preserves nonaliasing.**
Erasure restricts the actual owned domain and cannot add a name-map alias. -/
theorem NonAliases.erase {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) (e : Key) : NonAliases Γ (Δ.erase e) f := by
  intro d hd s sig hs
  exact h d (Finmap.mem_erase.mp hd).2 s sig hs

/-- **Updating an already-owned key preserves nonaliasing.**
Advancing an already-owned key leaves the name-map domain unchanged. -/
theorem NonAliases.insert_owned {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) {e : Key} (he : e ∈ Δ) (c : Capability) :
    NonAliases Γ (Δ.insert e c) f := by
  intro d hd s sig hs
  rcases Finmap.mem_insert.mp hd with rfl | hd
  · exact h d he s sig hs
  · exact h d hd s sig hs

/-- **Every name map is nonaliasing on empty ownership.**
Empty BODY ownership imposes no linear-image nonalias obligations. -/
theorem nonaliases_empty (Γ : ServiceEnv) (f : Name → Name) : NonAliases Γ ∅ f := by
  intro e he
  exact False.elim (Finmap.notMem_empty he)

/-- **Binder extension preserves nonaliasing of lifted contexts.**
Binder extension maps lifted owned names to lifted images, never new shared constants. -/
theorem NonAliases.under_lift {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) : NonAliases Γ (Context.lift 0 Δ) (under f) := by
  intro e he s sig hs hn
  obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
  change under f (liftName 0 d.name) = .const s at hn
  rw [under_lift_zero] at hn
  exact h d hd s sig hs (liftName_injective 0 hn)

/-- **Nonaliasing survives adding a received parameter under a binder.**
A newly received parameter remains var0 under the canonical binder map. -/
theorem NonAliases.under_received {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) (r : Role) (c : Capability) :
    NonAliases Γ ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) (under f) := by
  intro e he s sig hs hn
  rcases Finmap.mem_insert.mp he with he | he
  · subst e
    cases hn
  · exact h.under_lift e he s sig hs hn

/-- **Nonaliasing survives binding a private session pair.**
Both private-role keys are fresh var0; only actual outer names need nonalias transport. -/
theorem NonAliases.under_bind {Γ : ServiceEnv} {Δ : Context} {f : Name → Name}
    (h : NonAliases Γ Δ f) (c : Capability) : NonAliases Γ (Context.bind c Δ) (under f) := by
  intro e he s sig hs hn
  rcases Finmap.mem_insert.mp he with he | he
  · subst e
    cases hn
  · rcases Finmap.mem_insert.mp he with he | he
    · subst e
      cases hn
    · exact h.under_lift e he s sig hs hn

/-- **Nonaliasing restricts to the left part of a union.**
Actual left-domain restriction of an ownership union preserves map nonalias. -/
theorem NonAliases.union_left {Γ : ServiceEnv} {Δ Θ : Context} {f : Name → Name}
    (h : NonAliases Γ (Δ ∪ Θ) f) : NonAliases Γ Δ f :=
  fun e he => h e (Finmap.mem_union.mpr (Or.inl he))

/-- **Nonaliasing restricts to the right part of a union.**
Actual right-domain restriction likewise preserves map nonalias. -/
theorem NonAliases.union_right {Γ : ServiceEnv} {Δ Θ : Context} {f : Name → Name}
    (h : NonAliases Γ (Δ ∪ Θ) f) : NonAliases Γ Θ f :=
  fun e he => h e (Finmap.mem_union.mpr (Or.inr he))

/-- **Service templates are preserved by renamings fixing shared names.**
Structural templates transport through a declared-constant-fixing name map;
input BODY typing is handled separately, not hidden in this shape predicate. -/
theorem ServiceTemplate.rename {Γ : ServiceEnv} {p : Proc} {f : Name → Name}
    (h : ServiceTemplate Γ p) (hf : FixesShared Γ f) : ServiceTemplate Γ (mapProc f p) := by
  induction p generalizing f with
  | nil => trivial
  | out => exact False.elim h
  | inp a p ih =>
    obtain ⟨s, rfl, hs⟩ := h
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hs
    exact ⟨s, hf s sig hsig, hs⟩
  | par p q ihp ihq => exact ⟨ihp h.1 hf, ihq h.2 hf⟩
  | nu p ih => exact ih h hf.under
  | repl p ih => exact ih h hf
  | sum => exact False.elim h

/-- **Rekeying preserves shared invocation priority.**
Rekeying retains actual cap values and therefore shared-priority comparisons. -/
theorem InvocationPriority.rekey {sig : ServiceSignature} {Δ : Context} {f : Name → Name}
    (h : InvocationPriority sig Δ) (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    InvocationPriority sig (Context.rekey (Key.mapName f) Δ hf) := by
  intro e c hc ha
  obtain ⟨d, hd, rfl⟩ := Context.lookup_rekey.mp hc
  exact h d c hd ha

/-- **Rekeying the empty context gives the empty context.**
An empty owned context stays empty under the canonical context rekey operation. -/
theorem rekey_empty (f : Name → Name)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ (∅ : Context)}) :
    Context.rekey (Key.mapName f) ∅ hf = ∅ := by
  apply Finmap.ext_lookup
  intro e
  rw [Finmap.lookup_empty]
  apply Finmap.lookup_eq_none.mpr
  intro he
  obtain ⟨d, hd, hm⟩ := Context.mem_rekey.mp he
  exact Finmap.notMem_empty hd

/-- **Rekeying a singleton moves its key and keeps its capability.**
Rekeying a singleton moves its actual key and retains its capability verbatim. -/
theorem rekey_singleton (f : Name → Name) (e : Key) (c : Capability)
    (hf : Set.InjOn (Key.mapName f) {d | d ∈ (Finmap.singleton e c : Context)}) :
    Context.rekey (Key.mapName f) (Finmap.singleton e c) hf =
      Finmap.singleton (Key.mapName f e) c := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = Key.mapName f e
  · subst x
    rw [Finmap.lookup_singleton_eq]
    exact Context.lookup_rekey.mpr ⟨e, Finmap.lookup_singleton_eq, rfl⟩
  · have hn : x ∉ (Finmap.singleton (Key.mapName f e) c : Context) := by
      simpa only [Finmap.mem_singleton] using hx
    rw [Finmap.lookup_eq_none.mpr hn]
    apply Finmap.lookup_eq_none.mpr
    intro he
    obtain ⟨d, hd, hm⟩ := Context.mem_rekey.mp he
    have hd' := (Finmap.mem_singleton _ _ _).mp hd
    subst d
    exact hx hm.symm

/-- **Separation gives nonaliasing for binder lifting.**
Canonical binder lifting cannot send a nonshared owned name into the shared namespace. -/
theorem Separated.nonaliases_lift {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ) (k : Nat) :
    NonAliases Γ Δ (liftName k) := by
  intro e he s sig hs hn
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp he
  exact h e c hc s sig hs (liftName_injective k hn)

/-- **Separation gives nonaliasing for binder swapping.**
Canonical binder swapping likewise preserves actual owned-name nonalias. -/
theorem Separated.nonaliases_swap {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ) (k : Nat) :
    NonAliases Γ Δ (swapNameAt k) := by
  intro e he s sig hs hn
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp he
  exact h e c hc s sig hs (swapNameAt_injective k hn)

end Cslib.SessionTypes.Endpoint.Runtime
