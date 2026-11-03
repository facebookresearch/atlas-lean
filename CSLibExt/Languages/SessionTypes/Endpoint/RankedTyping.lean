/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Typing
public import CSLibExt.Languages.SessionTypes.Endpoint.Priority

/-!
# Syntax-directed endpoint priority refinement

This project-authored guard discipline is a refinement of the existing seven
linear typing rules, not a port of priority-based classical processes. Natural
ranks are static per capability. Only the same polarized key is exempt; active
payloads and same-name opposite roles participate in every guard check.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Linear ownership typing with a strict priority check at every guard.
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
  | outEndpoint {n : Nat} {Δ : Context} {e d : Key} {c : Capability}
      {k : Nat} {t s : Protocol} {p : Proc} :
      GuardMin Δ e c.rank → Δ.lookup e = some c →
      c.protocol.unfold = .sendEndpoint d.role k t s →
      Δ.lookup d = some ⟨k, t⟩ → e ≠ d →
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

/-- Forgetting priorities recovers the exact existing ownership judgement. -/
theorem RankedType.hasType {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) : HasType n Δ p := by
  induction h with
  | nil hc hs => exact HasType.nil hc hs
  | outName hg hc hs ha hb hp ih => exact HasType.outName hc hs ha hb ih
  | inpName hg hc hs ha hp ih => exact HasType.inpName hc hs ha ih
  | outEndpoint hg hc hs hd he ha hb hp ih => exact HasType.outEndpoint hc hs hd he ha hb ih
  | inpEndpoint hg hc hs ha hp ih => exact HasType.inpEndpoint hc hs ha ih
  | par hd hp hq ihp ihq => exact HasType.par hd ihp ihq
  | nu hp ih => exact HasType.nu ih

/-- Output inversion exposes the priority constraint for the actual owned subject. -/
theorem RankedType.out_guard {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ GuardMin Δ e c.rank := by
  cases h with
  | outName hg hc => exact ⟨_, _, rfl, hc, hg⟩
  | outEndpoint hg hc => exact ⟨_, _, rfl, hc, hg⟩

/-- Input inversion exposes the priority constraint before either kind of receive. -/
theorem RankedType.inp_guard {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ GuardMin Δ e c.rank := by
  cases h with
  | inpName hg hc => exact ⟨_, _, rfl, hc, hg⟩
  | inpEndpoint hg hc => exact ⟨_, _, rfl, hc, hg⟩

/-- Nil has no guard: its refinement is exactly the base completed/scoped context. -/
theorem RankedType.nil_of_hasType {n : Nat} {Δ : Context}
    (h : HasType n Δ .nil) : RankedType n Δ .nil := by
  obtain ⟨hc, hs⟩ := h.nil_inv
  exact RankedType.nil hc hs

/-- Every other active owned role must rank strictly after an input subject. -/
theorem RankedType.input_other_rank {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) {d : Key} {u : Capability}
    (hd : Δ.lookup d = some u) (hu : u.protocol.unfold ≠ .done)
    (hn : d.name ≠ a) : ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.rank < u.rank := by
  obtain ⟨e, c, he, hc, hg⟩ := h.inp_guard
  exact ⟨e, c, he, hc, hg d u hd hu (fun hde => hn ((congrArg Key.name hde).trans he))⟩

/-- Refinement preserves the original disjoint parallel ownership split. -/
theorem RankedType.par_inv {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ (.par p q)) :
    ∃ Γ Ξ, Δ = Γ ∪ Ξ ∧ Finmap.Disjoint Γ Ξ ∧ RankedType n Γ p ∧ RankedType n Ξ q := by
  cases h with
  | par hd hp hq => exact ⟨_, _, rfl, hd, hp, hq⟩

/-- Refinement retains the exact protocol/rank pair installed by restriction. -/
theorem RankedType.nu_inv {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ (.nu p)) : ∃ c, RankedType (n + 1) (Context.bind c Δ) p := by
  cases h with
  | nu hp => exact ⟨_, hp⟩

/-- Every active delegated payload is included in the pre-transfer guard check. -/
theorem GuardMin.active_payload_rank {Δ : Context} {e d : Key}
    {c : Capability} {k : Nat} (hg : GuardMin Δ e k)
    (hd : Δ.lookup d = some c) (ha : c.protocol.unfold ≠ .done) (hne : e ≠ d) :
    k < c.rank := hg d c hd ha hne.symm

end Cslib.SessionTypes.Endpoint
