/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ServiceTemplates
public import CSLibExt.Languages.SessionTypes.Endpoint.SharedEnvironmentTransport
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionTyping

/-!
# Self-contained linear/session typing with guarded shared replication

Completed ambient annotations are separate from BODY capture. Shared input
bodies receive exactly their fresh endpoint; replication bodies type at EMPTY
ownership and must be structural guarded templates. No typing-up-to-Cong or
Step/progress/result field occurs in these syntax-directed rules.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Ten syntax-directed rules over canonical Pi, fixed static ranks and actual
ownership. Accept/serve may carry completed ambient annotations, never body capture. -/
inductive HasType : Nat → ServiceEnv → Context → Proc → Prop where
  | nil {n : Nat} {Γ : ServiceEnv} {Δ : Context} :
      Δ.Completed → (∀ e ∈ Δ, e.name.ClosedAt n) → Separated Γ Δ → HasType n Γ Δ .nil
  | outName {n : Nat} {Γ : ServiceEnv} {Δ : Context} {e : Key} {c : Capability}
      {b : Name} {s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Separated Γ Δ → Δ.lookup e = some c →
      c.protocol.unfold = .sendName s → e.name.ClosedAt n → b.ClosedAt n →
      HasType n Γ (Δ.insert e ⟨c.rank, s⟩) p → HasType n Γ Δ (.out e.name b p)
  | inpName {n : Nat} {Γ : ServiceEnv} {Δ : Context} {e : Key} {c : Capability}
      {s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Separated Γ Δ → Δ.lookup e = some c →
      c.protocol.unfold = .recvName s → e.name.ClosedAt n →
      HasType (n + 1) Γ (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p →
      HasType n Γ Δ (.inp e.name p)
  | outEndpoint {n : Nat} {Γ : ServiceEnv} {Δ : Context} {e d : Key} {c v : Capability}
      {k : Nat} {t s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Separated Γ Δ → Δ.lookup e = some c →
      c.protocol.unfold = .sendEndpoint d.role k t s → Δ.lookup d = some v →
      v.Equivalent ⟨k, t⟩ → e ≠ d → e.name.ClosedAt n → d.name.ClosedAt n →
      HasType n Γ ((Δ.erase d).insert e ⟨c.rank, s⟩) p →
      HasType n Γ Δ (.out e.name d.name p)
  | inpEndpoint {n : Nat} {Γ : ServiceEnv} {Δ : Context} {e : Key} {c : Capability}
      {r : Role} {k : Nat} {t s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Separated Γ Δ → Δ.lookup e = some c →
      c.protocol.unfold = .recvEndpoint r k t s → e.name.ClosedAt n →
      HasType (n + 1) Γ
        ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p →
      HasType n Γ Δ (.inp e.name p)
  | invoke {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat} {sig : ServiceSignature}
      {e : Key} {v : Capability} {p : Proc} :
      Γ.lookup s = some sig → Separated Γ Δ → Δ.lookup e = some v →
      e.role = sig.role → v.Equivalent sig.capability → InvocationPriority sig Δ →
      e.name.ClosedAt n → HasType n Γ (Δ.erase e) p → HasType n Γ Δ (.out (.const s) e.name p)
  | accept {n : Nat} {Γ : ServiceEnv} {Δ : Context} {s : Nat} {sig : ServiceSignature}
      {p : Proc} :
      Γ.lookup s = some sig → Δ.Completed → (∀ e ∈ Δ, e.name.ClosedAt n) → Separated Γ Δ →
      HasType (n + 1) Γ (Finmap.singleton ⟨.var 0, sig.role⟩ sig.capability) p →
      HasType n Γ Δ (.inp (.const s) p)
  | serve {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc} :
      ServiceTemplate Γ p → HasType n Γ ∅ p → Δ.Completed →
      (∀ e ∈ Δ, e.name.ClosedAt n) → Separated Γ Δ → HasType n Γ Δ (.repl p)
  | par {n : Nat} {Γ : ServiceEnv} {Δ Θ : Context} {p q : Proc} :
      Finmap.Disjoint Δ Θ → HasType n Γ Δ p → HasType n Γ Θ q →
      HasType n Γ (Δ ∪ Θ) (.par p q)
  | nu {n : Nat} {Γ : ServiceEnv} {Δ : Context} {c : Capability} {p : Proc} :
      Separated Γ Δ → HasType (n + 1) Γ (Context.bind c Δ) p → HasType n Γ Δ (.nu p)

/-- Real ALL7-rule induction embeds finite ranked typing, including delegation;
there is no finite-judgement constructor in the new runtime typing. -/
theorem HasType.of_finite {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : Conversion.RankedType n Δ p) (hs : Separated Γ Δ) : HasType n Γ Δ p := by
  revert hs
  induction h with
  | nil hc hscope =>
    intro hs
    exact HasType.nil hc hscope hs
  | @outName n Δ e c b s p hg hc hh ha hb hp ih =>
    intro hs
    exact HasType.outName hg hs hc hh ha hb
      (ih (hs.insert e ⟨c.rank, s⟩ (hs e c hc)))
  | @inpName n Δ e c s p hg hc hh ha hp ih =>
    intro hs
    exact HasType.inpName hg hs hc hh ha
      (ih ((hs.insert e ⟨c.rank, s⟩ (hs e c hc)).lift 0))
  | @outEndpoint n Δ e d c v k t s p hg hc hh hv he hne ha hb hp ih =>
    intro hs
    exact HasType.outEndpoint hg hs hc hh hv he hne ha hb
      (ih ((hs.erase d).insert e ⟨c.rank, s⟩ (hs e c hc)))
  | @inpEndpoint n Δ e c r k t s p hg hc hh ha hp ih =>
    intro hs
    apply HasType.inpEndpoint hg hs hc hh ha
    apply ih
    apply ((hs.insert e ⟨c.rank, s⟩ (hs e c hc)).lift 0).insert
    intro s sig hs he
    cases he
  | par hd hp hq ihp ihq =>
    intro hs
    exact HasType.par hd (ihp hs.union_left) (ihq (hs.union_right hd))
  | @nu n Δ c p hp ih =>
    intro hs
    exact HasType.nu hs (ih (hs.bind c))

end Cslib.SessionTypes.Endpoint.Runtime
