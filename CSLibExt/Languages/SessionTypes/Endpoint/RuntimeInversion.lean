/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SharedServices

/-! # Direct inversion and source invariants of self-contained runtime typing -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Runtime typing separates owned names from shared services.**
Completed ambient annotations still obey actual shared/linear name separation. -/
theorem HasType.separated {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : Separated Γ Δ := by
  induction h with
  | nil hc hscope hs => exact hs
  | outName hg hs => exact hs
  | inpName hg hs => exact hs
  | outEndpoint hg hs => exact hs
  | inpEndpoint hg hs => exact hs
  | invoke hsig hs => exact hs
  | accept hsig hc hscope hs => exact hs
  | serve ht hp hc hscope hs => exact hs
  | @par n Γ Δ Θ p q hd hp hq ihp ihq =>
    intro e c hc s sig hs
    by_cases he : e ∈ Δ
    · rw [Finmap.lookup_union_left he] at hc
      exact ihp e c hc s sig hs
    · rw [Finmap.lookup_union_right he] at hc
      exact ihq e c hc s sig hs
  | nu hs => exact hs

/-- **Replicated runtime processes have completed ownership.**
Replication has only COMPLETED ambient ownership, not necessarily empty annotation. -/
theorem HasType.repl_completed {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.repl p)) : Δ.Completed := by
  cases h with
  | serve ht hp hc hs hd => exact hc

/-- **Typed replication has a body with empty ownership.**
Replicated BODY ownership is exactly EMPTY, while ambient annotations may be completed. -/
theorem HasType.repl_body_empty {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.repl p)) : ServiceTemplate Γ p ∧ HasType n Γ ∅ p := by
  cases h with
  | serve ht hp hc hs hd => exact ⟨ht, hp⟩

/-- **Runtime-typed processes are scoped at the ambient depth.**
Every rule derives the EXISTING canonical process-scope predicate, including
fresh service parameters and empty-capture replicated template bodies. -/
theorem HasType.closedAt {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : p.ClosedAt n := by
  induction h with
  | nil => trivial
  | outName hg hs hc hh ha hb hp ih => exact ⟨ha, hb, ih⟩
  | inpName hg hs hc hh ha hp ih => exact ⟨ha, ih⟩
  | outEndpoint hg hs hc hh hv he hne ha hb hp ih => exact ⟨ha, hb, ih⟩
  | inpEndpoint hg hs hc hh ha hp ih => exact ⟨ha, ih⟩
  | invoke hs hd hv hr he hg hb hp ih => exact ⟨trivial, hb, ih⟩
  | accept hs hc hscope hd hp ih => exact ⟨trivial, ih⟩
  | serve ht hp hc hs hd ih => exact ih
  | par hd hp hq ihp ihq => exact ⟨ihp, ihq⟩
  | nu hs hp ih => exact ih

/-- **Typing rule for a replicated input on a shared name.**
A literal shared-input replica is an admissible structural template, with
its received BODY at the fresh singleton and replica BODY at EMPTY ownership. -/
theorem HasType.serve_input {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat}
    {sig : ServiceSignature} {p : Proc} (hs : Γ.lookup s = some sig)
    (hp : HasType (n + 1) Γ (Finmap.singleton ⟨.var 0, sig.role⟩ sig.capability) p)
    (hc : Δ.Completed) (hscope : ∀ e ∈ Δ, e.name.ClosedAt n) (hd : Separated Γ Δ) :
    HasType n Γ Δ (.repl (.inp (.const s) p)) := by
  apply HasType.serve (p := .inp (.const s) p) ⟨s, rfl, Finmap.mem_of_lookup_eq_some hs⟩
    (HasType.accept hs Context.completed_empty
      (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty Γ) hp)
    hc hscope hd

/-- **Inversion of runtime typing for the nil process.**
Nil has only actual completed, scoped, separated ambient ownership. -/
theorem HasType.nil_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} (h : HasType n Γ Δ .nil) :
    Δ.Completed ∧ (∀ e ∈ Δ, e.name.ClosedAt n) ∧ Separated Γ Δ := by
  cases h with
  | nil hc hs hd => exact ⟨hc, hs, hd⟩

/-- **Inversion of runtime typing for parallel composition.**
Parallel inversion derives the actual disjoint linear split at unchanged Γ. -/
theorem HasType.par_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ (.par p q)) :
    ∃ Θ Ξ, Δ = Θ ∪ Ξ ∧ Finmap.Disjoint Θ Ξ ∧ HasType n Γ Θ p ∧ HasType n Γ Ξ q := by
  cases h with
  | par hd hp hq => exact ⟨_, _, rfl, hd, hp, hq⟩

/-- **Inversion of runtime typing for restriction.**
Restriction inversion exposes a real literal-dual bound pair, not a representative. -/
theorem HasType.nu_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.nu p)) : ∃ c, HasType (n + 1) Γ (Context.bind c Δ) p := by
  cases h with
  | nu hs hp => exact ⟨_, hp⟩

/-- **Output subjects are owned endpoints or declared shared names.**
Actual output subjects are linear-owned or declared shared constants. -/
theorem HasType.output_subject {n : Nat} {Γ : ServiceEnv} {Δ : Context} {a b : Name} {p : Proc}
    (h : HasType n Γ Δ (.out a b p)) :
    (∃ e c, e.name = a ∧ Δ.lookup e = some c) ∨
      ∃ s sig, a = .const s ∧ Γ.lookup s = some sig := by
  cases h with
  | outName hg hs hc hh ha hb hp => exact Or.inl ⟨_, _, rfl, hc⟩
  | outEndpoint hg hs hc hh hv he hne ha hb hp => exact Or.inl ⟨_, _, rfl, hc⟩
  | invoke hs hd hv hr he hg hb hp => exact Or.inr ⟨_, _, rfl, hs⟩

/-- **Output on a declared shared name is a service invocation.**
A declared shared output is necessarily an actual endpoint-transfer invocation. -/
theorem HasType.invoke_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat}
    {sig : ServiceSignature} {b : Name} {p : Proc}
    (h : HasType n Γ Δ (.out (.const s) b p)) (hs : Γ.lookup s = some sig) :
    ∃ e v, e.name = b ∧ Δ.lookup e = some v ∧ e.role = sig.role ∧
      v.Equivalent sig.capability ∧ InvocationPriority sig Δ ∧
      HasType n Γ (Δ.erase e) p := by
  generalize hsource : Name.const s = a at h
  cases h with
  | outName hg hd hc hh ha hb hp => exact False.elim (hd _ _ hc s sig hs hsource.symm)
  | outEndpoint hg hd hc hh hv he hne ha hb hp =>
    exact False.elim (hd _ _ hc s sig hs hsource.symm)
  | invoke ht hd hv hr he hg hb hp =>
    have hname := Name.const.inj hsource
    subst_vars
    have hsig := Option.some.inj (ht.symm.trans hs)
    subst sig
    exact ⟨_, _, rfl, hv, hr, he, hg, hp⟩

/-- **Inversion of runtime typing for input on a shared name.**
A declared shared input has completed ambient annotations and EXACT fresh
singleton BODY ownership, not captured ambient capabilities. -/
theorem HasType.accept_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat}
    {sig : ServiceSignature} {p : Proc}
    (h : HasType n Γ Δ (.inp (.const s) p)) (hs : Γ.lookup s = some sig) :
    Δ.Completed ∧ (∀ e ∈ Δ, e.name.ClosedAt n) ∧ Separated Γ Δ ∧
      HasType (n + 1) Γ (Finmap.singleton ⟨.var 0, sig.role⟩ sig.capability) p := by
  generalize hsource : Name.const s = a at h
  cases h with
  | inpName hg hd hc hh ha hp => exact False.elim (hd _ _ hc s sig hs hsource.symm)
  | inpEndpoint hg hd hc hh ha hp => exact False.elim (hd _ _ hc s sig hs hsource.symm)
  | accept ht hc hscope hd hp =>
    have hname := Name.const.inj hsource
    subst_vars
    have hsig := Option.some.inj (ht.symm.trans hs)
    subst sig
    exact ⟨hc, hscope, hd, hp⟩

/-- **Inversion of runtime typing for replication.**
General replica inversion retains completed/scoped/separated AMBIENT annotations
and the structurally guarded BODY typed at EXACT EMPTY ownership. -/
theorem HasType.repl_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.repl p)) :
    Δ.Completed ∧ (∀ e ∈ Δ, e.name.ClosedAt n) ∧ Separated Γ Δ ∧
      ServiceTemplate Γ p ∧ HasType n Γ ∅ p := by
  cases h with
  | serve ht hp hc hs hd => exact ⟨hc, hs, hd, ht, hp⟩

/-- **Inversion of runtime typing for a replicated shared input.**
A literal input template exposes its declared signature and fresh received BODY;
completed ambient annotations are NOT inherited by that BODY. -/
theorem HasType.service_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat} {p : Proc}
    (h : HasType n Γ Δ (.repl (.inp (.const s) p))) :
    ∃ sig, Δ.Completed ∧ Γ.lookup s = some sig ∧
      HasType (n + 1) Γ (Finmap.singleton ⟨.var 0, sig.role⟩ sig.capability) p := by
  obtain ⟨t, ht, hm⟩ := h.repl_body_empty.1
  have hn := Name.const.inj ht
  subst t
  obtain ⟨sig, hs⟩ := Finmap.mem_iff.mp hm
  exact ⟨sig, h.repl_completed, hs, (h.repl_body_empty.2.accept_inv hs).2.2.2⟩

/-- **Typed replicated shared inputs are offered services.**
Typing-derived actual literal-input offering survives completed ambient annotations. -/
theorem HasType.service_offered {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat} {p : Proc}
    (h : HasType n Γ Δ (.repl (.inp (.const s) p))) :
    ∃ sig, Offered Γ (.repl (.inp (.const s) p)) s sig := by
  obtain ⟨sig, hc, hs, hp⟩ := h.service_inv
  exact ⟨sig, hs, rfl⟩

end Cslib.SessionTypes.Endpoint.Runtime
