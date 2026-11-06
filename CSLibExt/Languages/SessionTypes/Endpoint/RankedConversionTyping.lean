/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionInversion
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedTyping

/-!
# Static priority refinement of semantic conversion typing

The unchanged GuardMin observes EVERY other active owned KEY before the action.
Actual equivalent payload codes and cap ranks are retained. This is finite Pi
syntax with regular type codes, not recursive process runtime.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Priority-ranked conversion typing judgement.**
Linear ownership typing with a strict priority check at every guard.
There is no reduction, enabled-edge, progress or preservation field. -/
inductive RankedType : Nat → Context → Proc → Prop where
  | nil {n : Nat} {Δ : Context} :
      Δ.Completed → (∀ e ∈ Δ, e.name.ClosedAt n) → RankedType n Δ .nil
  | outName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {b : Name} {s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Δ.lookup e = some c → c.protocol.unfold = .sendName s →
      e.name.ClosedAt n → b.ClosedAt n →
      RankedType n (Δ.insert e ⟨c.rank, s⟩) p → RankedType n Δ (.out e.name b p)
  | inpName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Δ.lookup e = some c → c.protocol.unfold = .recvName s →
      e.name.ClosedAt n →
      RankedType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p →
      RankedType n Δ (.inp e.name p)
  | outEndpoint {n : Nat} {Δ : Context} {e d : Key} {c v : Capability}
      {k : Nat} {t s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Δ.lookup e = some c →
      c.protocol.unfold = .sendEndpoint d.role k t s →
      Δ.lookup d = some v → v.Equivalent ⟨k, t⟩ → e ≠ d →
      e.name.ClosedAt n → d.name.ClosedAt n →
      RankedType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p →
      RankedType n Δ (.out e.name d.name p)
  | inpEndpoint {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {r : Role} {k : Nat} {t s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Δ.lookup e = some c →
      c.protocol.unfold = .recvEndpoint r k t s → e.name.ClosedAt n →
      RankedType (n + 1)
        ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p →
      RankedType n Δ (.inp e.name p)
  | par {n : Nat} {Δ Θ : Context} {p q : Proc} :
      Finmap.Disjoint Δ Θ → RankedType n Δ p → RankedType n Θ q →
      RankedType n (Δ ∪ Θ) (.par p q)
  | nu {n : Nat} {Δ : Context} {c : Capability} {p : Proc} :
      RankedType (n + 1) (Context.bind c Δ) p → RankedType n Δ (.nu p)

/-- **Forgetting priorities yields conversion typing.**
Forgetting guard priorities derives the existing conversion judgement. -/
theorem RankedType.hasType {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) : HasType n Δ p := by
  induction h with
  | nil hc hs => exact HasType.nil hc hs
  | outName hg hc hs ha hb hp ih => exact HasType.outName hc hs ha hb ih
  | inpName hg hc hs ha hp ih => exact HasType.inpName hc hs ha ih
  | outEndpoint hg hc hs hd hv he ha hb hp ih => exact HasType.outEndpoint hc hs hd hv he ha hb ih
  | inpEndpoint hg hc hs ha hp ih => exact HasType.inpEndpoint hc hs ha ih
  | par hd hp hq ihp ihq => exact HasType.par hd ihp ihq
  | nu hp ih => exact HasType.nu ih

/-- **Ranked typing embeds into conversion ranked typing.**
Explicit seven-case raw-ranked embedding, not theorem-value inheritance. -/
theorem RankedType.of_raw {n : Nat} {Δ : Context} {p : Proc}
    (h : Endpoint.RankedType n Δ p) : RankedType n Δ p := by
  induction h with
  | nil hc hs => exact RankedType.nil hc hs
  | outName hg hc hs ha hb hp ih => exact RankedType.outName hg hc hs ha hb ih
  | inpName hg hc hs ha hp ih => exact RankedType.inpName hg hc hs ha ih
  | outEndpoint hg hc hs hd he ha hb hp ih =>
    exact RankedType.outEndpoint hg hc hs hd (Capability.Equivalent.refl _) he ha hb ih
  | inpEndpoint hg hc hs ha hp ih => exact RankedType.inpEndpoint hg hc hs ha ih
  | par hd hp hq ihp ihq => exact RankedType.par hd ihp ihq
  | nu hp ih => exact RankedType.nu ih

/-- **Parallel inversion for conversion ranked typing.**
Ranked parallel typing exposes its actual disjoint ownership split. -/
theorem RankedType.par_inv {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ (.par p q)) :
    ∃ Γ Θ, Δ = Γ ∪ Θ ∧ Finmap.Disjoint Γ Θ ∧ RankedType n Γ p ∧ RankedType n Θ q := by
  cases h with
  | par hd hp hq => exact ⟨_, _, rfl, hd, hp, hq⟩

/-- **Restriction inversion for conversion ranked typing.**
Restriction chooses an actual literal-dual pair. -/
theorem RankedType.nu_inv {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ (.nu p)) : ∃ c, RankedType (n + 1) (Context.bind c Δ) p := by
  cases h with
  | nu hp => exact ⟨_, hp⟩

/-- **Nil typing lifts to conversion ranked typing.**
Nil adds no priority premise beyond actual completed and scoped ownership. -/
theorem RankedType.nil_of_hasType {n : Nat} {Δ : Context} (h : HasType n Δ .nil) :
    RankedType n Δ .nil := by
  obtain ⟨hc, hs⟩ := h.nil_inv
  exact RankedType.nil hc hs

end Cslib.SessionTypes.Endpoint.Conversion
