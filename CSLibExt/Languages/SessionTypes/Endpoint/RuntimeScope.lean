/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeTemplateTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.UnliftContext

/-!
# Exact bidirectional runtime scope transport

The shared environment, ambient depth and external linear interface are unchanged.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Reflection of a canonical lifted term retains exact owned capabilities and Γ. -/
theorem HasType.unlift {n : Nat} {Γ : ServiceEnv} {Δ : Context} {q : Proc}
    (h : HasType (n + 1) Γ Δ (liftProc 0 q)) (hΔ : ∀ e ∈ Δ, e.name ≠ .var 0) :
    HasType n Γ (Context.lower Δ hΔ) q := by
  have hl : HasType (n + 1) Γ (Context.lift 0 (Context.lower Δ hΔ)) (liftProc 0 q) := by
    rw [Context.lift_lower]
    exact h
  have ht := hl.subst_passive (b := .const 0) trivial
  change HasType n Γ (Context.lower Δ hΔ) (substProc (.const 0) 0 (liftProc 0 q)) at ht
  rw [substProc_liftProc] at ht
  exact ht

/-- Forward extrusion uses the actual disjoint split and literal bound pair. -/
theorem HasType.scope_forward {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ (.par (.nu p) q)) :
    HasType n Γ Δ (.nu (.par p (liftProc 0 q))) := by
  obtain ⟨Λ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  obtain ⟨c, hb⟩ := hp.nu_inv
  apply HasType.nu (c := c) h.separated
  rw [Context.bind_union c hd]
  exact HasType.par (Context.disjoint_bind_lift c hd) hb (hq.lift 0)

/-- Partner ownership may be restored only when actual absence DERIVES completion.
Shared nonalias is obtained from the typed owner, not a new unchecked assumption. -/
theorem HasType.insert_from_absent_partner {n : Nat} {Γ : ServiceEnv} {Δ Ξ : Context}
    {p q : Proc} {e : Key} {c : Capability} (hp : HasType n Γ Δ p) (hq : HasType n Γ Ξ q)
    (hc : (Δ ∪ Ξ).lookup e = some c) (hab : NameAbsent e.name q) (he : e.name.ClosedAt n) :
    HasType n Γ (Δ.insert e c) p := by
  by_cases hm : e ∈ Δ
  · rw [Finmap.lookup_union_left hm] at hc
    rw [Context.insert_of_lookup hc]
    exact hp
  · rw [Finmap.lookup_union_right hm] at hc
    exact hp.weaken_completed hm (hq.absent_lookup_completed hc hab) he (hq.separated e c hc)

/-- Restoring a private pair adds only actually absent completed partner roles. -/
theorem HasType.restore_scope_pair {n : Nat} {Γ : ServiceEnv} {Δ Λ Ξ : Context} {p q : Proc}
    {c : Capability} (hp : HasType (n + 1) Γ Λ p)
    (hq : HasType (n + 1) Γ Ξ (liftProc 0 q)) (hs : Context.bind c Δ = Λ ∪ Ξ) :
    HasType (n + 1) Γ ((Λ.insert (⟨.var 0, .positive⟩ : Key) c).insert
      (⟨.var 0, .negative⟩ : Key) c.dual) p := by
  have hpos : (Λ ∪ Ξ).lookup (⟨.var 0, .positive⟩ : Key) = some c := by
    rw [← hs]
    exact Context.lookup_bind_positive c Δ
  have hneg : (Λ ∪ Ξ).lookup (⟨.var 0, .negative⟩ : Key) = some c.dual := by
    rw [← hs]
    exact Context.lookup_bind_negative c Δ
  have hab := nameAbsent_fresh_lift 0 q
  have hp' := hp.insert_from_absent_partner hq hpos hab (Nat.zero_lt_succ n)
  apply hp'.insert_from_absent_partner (e := ⟨.var 0, .negative⟩) hq ?_ hab (Nat.zero_lt_succ n)
  rw [← Finmap.insert_union, Finmap.lookup_insert_of_ne _
    (by decide : (⟨.var 0, .negative⟩ : Key) ≠ (⟨.var 0, .positive⟩ : Key))]
  exact hneg

/-- Reverse extrusion derives the exact external split from actual typing and
removes only genuinely absent partner roles. No closed-hole or ready premise. -/
theorem HasType.scope_reverse {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ (.nu (.par p (liftProc 0 q)))) :
    HasType n Γ Δ (.par (.nu p) q) := by
  obtain ⟨c, hb⟩ := h.nu_inv
  obtain ⟨Λ, Ξ, hs, hd, hp, hq⟩ := hb.par_inv
  let Λ₀ := (Λ.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)
  let Ξ₀ := (Ξ.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)
  have hΛ : ∀ e ∈ Λ₀, e.name ≠ .var 0 := Context.erased_pair_outer Λ
  have hΞ : ∀ e ∈ Ξ₀, e.name ≠ .var 0 := Context.erased_pair_outer Ξ
  have hd₀ : Finmap.Disjoint Λ₀ Ξ₀ := by
    intro e he ht
    exact hd e (Finmap.mem_erase.mp (Finmap.mem_erase.mp he).2).2
      (Finmap.mem_erase.mp (Finmap.mem_erase.mp ht).2).2
  have hdl := Context.disjoint_lower hΛ hΞ hd₀
  have hsplit : Context.lift 0 Δ = Λ₀ ∪ Ξ₀ := by
    have he := congrArg (fun K : Context =>
      (K.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)) hs
    rw [Context.erase_bind_pair, Context.erase_union, Context.erase_union] at he
    exact he
  have houter : Δ = Context.lower Λ₀ hΛ ∪ Context.lower Ξ₀ hΞ := by
    apply Context.lift_zero_injective
    rw [Context.lift_union 0 hdl, Context.lift_lower, Context.lift_lower]
    exact hsplit
  have hp' : HasType (n + 1) Γ (Context.bind c (Context.lower Λ₀ hΛ)) p := by
    rw [Context.bind, Context.lift_lower, Context.restore_erased_pair]
    exact hp.restore_scope_pair hq hs
  have hab := nameAbsent_fresh_lift 0 q
  have hq' : HasType (n + 1) Γ Ξ₀ (liftProc 0 q) :=
    (hq.erase_nameAbsent (z := ⟨.var 0, .negative⟩) hab).erase_nameAbsent
      (z := ⟨.var 0, .positive⟩) hab
  have hsep : Separated Γ (Context.lower Λ₀ hΛ ∪ Context.lower Ξ₀ hΞ) := houter ▸ h.separated
  rw [houter]
  exact HasType.par hdl (HasType.nu hsep.union_left hp') (hq'.unlift hΞ)

/-- Exact canonical scope transport preserves SAME Γ, n and Δ in both directions. -/
theorem HasType.scope_iff {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc} :
    HasType n Γ Δ (.par (.nu p) q) ↔ HasType n Γ Δ (.nu (.par p (liftProc 0 q))) :=
  ⟨HasType.scope_forward, HasType.scope_reverse⟩

end Cslib.SessionTypes.Endpoint.Runtime
