/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionResources
public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionScope

/-!
# Exact scope typing for the conversion priority refinement
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- Reflection of an actual lifted term recovers every priority and context entry. -/
theorem RankedType.unlift {n : Nat} {Γ : Context} {q : Proc}
    (h : RankedType (n + 1) Γ (liftProc 0 q)) (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) :
    RankedType n (Context.lower Γ hΓ) q := by
  have hl : RankedType (n + 1) (Context.lift 0 (Context.lower Γ hΓ)) (liftProc 0 q) := by
    rw [Context.lift_lower]
    exact h
  have ht := hl.subst_passive (b := .const 0) trivial
  change RankedType n (Context.lower Γ hΓ) (substProc (.const 0) 0 (liftProc 0 q)) at ht
  rw [substProc_liftProc] at ht
  exact ht

/-- Extrusion lifts the partner's real ownership while retaining every guard. -/
theorem RankedType.scope_forward {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ (.par (.nu p) q)) :
    RankedType n Δ (.nu (.par p (liftProc 0 q))) := by
  obtain ⟨Γ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  obtain ⟨c, hb⟩ := hp.nu_inv
  apply RankedType.nu (c := c)
  rw [Context.bind_union c hd]
  exact RankedType.par (Context.disjoint_bind_lift c hd) hb (hq.lift 0)

/-- Moving a partner-owned role back requires actual absence to DERIVE
completion from conversion typing before refined completed weakening is applied. -/
theorem RankedType.insert_from_absent_partner {n : Nat} {Γ Ξ : Context} {p q : Proc}
    {e : Key} {c : Capability} (hp : RankedType n Γ p) (hq : RankedType n Ξ q)
    (hc : (Γ ∪ Ξ).lookup e = some c) (hab : NameAbsent e.name q)
    (he : e.name.ClosedAt n) : RankedType n (Γ.insert e c) p := by
  by_cases hm : e ∈ Γ
  · rw [Finmap.lookup_union_left hm] at hc
    rw [Context.insert_of_lookup hc]
    exact hp
  · rw [Finmap.lookup_union_right hm] at hc
    exact hp.weaken_completed hm (hq.hasType.absent_lookup_completed hc hab) he

/-- Restoring the bound pair adds only absent completed partner roles; all
original active ownership and inequalities of the restricted component remain. -/
theorem RankedType.restore_scope_pair {n : Nat} {Δ Γ Ξ : Context} {p q : Proc}
    {c : Capability} (hp : RankedType (n + 1) Γ p)
    (hq : RankedType (n + 1) Ξ (liftProc 0 q)) (hs : Context.bind c Δ = Γ ∪ Ξ) :
    RankedType (n + 1) ((Γ.insert (⟨.var 0, .positive⟩ : Key) c).insert
      (⟨.var 0, .negative⟩ : Key) c.dual) p := by
  have hpos : (Γ ∪ Ξ).lookup (⟨.var 0, .positive⟩ : Key) = some c := by
    rw [← hs]
    exact Context.lookup_bind_positive c Δ
  have hneg : (Γ ∪ Ξ).lookup (⟨.var 0, .negative⟩ : Key) = some c.dual := by
    rw [← hs]
    exact Context.lookup_bind_negative c Δ
  have hab := nameAbsent_fresh_lift 0 q
  have hp' := hp.insert_from_absent_partner hq hpos hab (Nat.zero_lt_succ n)
  apply hp'.insert_from_absent_partner (e := ⟨.var 0, .negative⟩) hq ?_ hab (Nat.zero_lt_succ n)
  rw [← Finmap.insert_union, Finmap.lookup_insert_of_ne _
    (by decide : (⟨.var 0, .negative⟩ : Key) ≠ (⟨.var 0, .positive⟩ : Key))]
  exact hneg

/-- Reverse extrusion derives the entire outer ownership split from typing,
removes only genuinely absent partner roles and retains all guard inequalities. -/
theorem RankedType.scope_reverse {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ (.nu (.par p (liftProc 0 q)))) :
    RankedType n Δ (.par (.nu p) q) := by
  obtain ⟨c, hb⟩ := h.nu_inv
  obtain ⟨Γ, Ξ, hs, hd, hp, hq⟩ := hb.par_inv
  let Γ₀ := (Γ.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)
  let Ξ₀ := (Ξ.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)
  have hΓ : ∀ e ∈ Γ₀, e.name ≠ .var 0 := Context.erased_pair_outer Γ
  have hΞ : ∀ e ∈ Ξ₀, e.name ≠ .var 0 := Context.erased_pair_outer Ξ
  have hd₀ : Finmap.Disjoint Γ₀ Ξ₀ := by
    intro e he ht
    exact hd e (Finmap.mem_erase.mp (Finmap.mem_erase.mp he).2).2
      (Finmap.mem_erase.mp (Finmap.mem_erase.mp ht).2).2
  have hdl := Context.disjoint_lower hΓ hΞ hd₀
  have hsplit : Context.lift 0 Δ = Γ₀ ∪ Ξ₀ := by
    have he := congrArg (fun K : Context =>
      (K.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)) hs
    rw [Context.erase_bind_pair, Context.erase_union, Context.erase_union] at he
    exact he
  have houter : Δ = Context.lower Γ₀ hΓ ∪ Context.lower Ξ₀ hΞ := by
    apply Context.lift_zero_injective
    rw [Context.lift_union 0 hdl, Context.lift_lower, Context.lift_lower]
    exact hsplit
  have hp' : RankedType (n + 1) (Context.bind c (Context.lower Γ₀ hΓ)) p := by
    rw [Context.bind, Context.lift_lower, Context.restore_erased_pair]
    exact hp.restore_scope_pair hq hs
  have hab := nameAbsent_fresh_lift 0 q
  have hq' : RankedType (n + 1) Ξ₀ (liftProc 0 q) :=
    (hq.erase_nameAbsent (z := ⟨.var 0, .negative⟩) hab).erase_nameAbsent
      (z := ⟨.var 0, .positive⟩) hab
  rw [houter]
  exact RankedType.par hdl (RankedType.nu hp') (hq'.unlift hΞ)

/-- Exact bidirectional canonical scope transport for the same refinement. -/
theorem RankedType.scope_iff {n : Nat} {Δ : Context} {p q : Proc} :
    RankedType n Δ (.par (.nu p) q) ↔ RankedType n Δ (.nu (.par p (liftProc 0 q))) :=
  ⟨RankedType.scope_forward, RankedType.scope_reverse⟩

end Cslib.SessionTypes.Endpoint.Conversion
