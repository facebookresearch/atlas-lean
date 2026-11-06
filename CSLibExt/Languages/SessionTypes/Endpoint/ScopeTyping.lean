/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Strengthening
public import CSLibExt.Languages.SessionTypes.Endpoint.EndWeakening
public import CSLibExt.Languages.SessionTypes.Endpoint.Substitution
public import CSLibExt.Languages.SessionTypes.Endpoint.UnliftContext

/-!
# Exact ownership typing transport for canonical π scope extrusion
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Inversion of endpoint typing for restriction.**
Restriction inversion exposes the actual bound dual pair. -/
theorem HasType.nu_inv {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ (.nu p)) :
    ∃ c, HasType (n + 1) (Context.bind c Δ) p := by
  cases h with
  | nu hp => exact ⟨_, hp⟩

/-- **Endpoint typing is preserved by forward scope extrusion.**
The forward canonical scope rule preserves the exact external context
and ambient depth, with the dual pair derived from restriction typing. -/
theorem HasType.scope_forward {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ (.par (.nu p) q)) :
    HasType n Δ (.nu (.par p (liftProc 0 q))) := by
  obtain ⟨Θ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  obtain ⟨c, hbody⟩ := hp.nu_inv
  apply HasType.nu (c := c)
  rw [Context.bind_union c hd]
  exact HasType.par (Context.disjoint_bind_lift c hd) hbody (hq.lift 0)

/-- **Endpoint typing absorbs a role absent from its parallel partner.**
A role missing from one component can be reattached only after actual
absence in its typed partner derives completion of the advertised capability. -/
theorem HasType.insert_from_absent_partner {n : Nat} {Γ Ξ : Context} {p q : Proc}
    {e : Key} {c : Capability} (hp : HasType n Γ p) (hq : HasType n Ξ q)
    (hc : (Γ ∪ Ξ).lookup e = some c) (hab : NameAbsent e.name q)
    (he : e.name.ClosedAt n) : HasType n (Γ.insert e c) p := by
  by_cases hm : e ∈ Γ
  · rw [Finmap.lookup_union_left hm] at hc
    rw [Context.insert_of_lookup hc]
    exact hp
  · rw [Finmap.lookup_union_right hm] at hc
    exact hp.weaken_completed hm (hq.absent_lookup_completed hc hab) he

/-- **Endpoint typing restores both bound roles to the restricted side.**
In the actual scope split, either freshly bound role can be moved
back to the restricted component only when partner absence proves it completed. -/
theorem HasType.restore_scope_pair {n : Nat} {Δ Γ Ξ : Context} {p q : Proc}
    {c : Capability} (hp : HasType (n + 1) Γ p)
    (hq : HasType (n + 1) Ξ (liftProc 0 q)) (hs : Context.bind c Δ = Γ ∪ Ξ) :
    HasType (n + 1) ((Γ.insert (⟨.var 0, .positive⟩ : Key) c).insert
      (⟨.var 0, .negative⟩ : Key) c.dual) p := by
  have hpos : (Γ ∪ Ξ).lookup (⟨.var 0, .positive⟩ : Key) = some c := by
    rw [← hs]
    exact Context.lookup_bind_positive c Δ
  have hneg : (Γ ∪ Ξ).lookup (⟨.var 0, .negative⟩ : Key) = some c.dual := by
    rw [← hs]
    exact Context.lookup_bind_negative c Δ
  have hab := nameAbsent_fresh_lift 0 q
  have hscope : (Name.var 0).ClosedAt (n + 1) := Nat.zero_lt_succ n
  have hp' := hp.insert_from_absent_partner hq hpos hab hscope
  apply hp'.insert_from_absent_partner hq ?_ hab hscope
  rw [← Finmap.insert_union, Finmap.lookup_insert_of_ne _
    (by decide : (⟨.var 0, .negative⟩ : Key) ≠ (⟨.var 0, .positive⟩ : Key))]
  exact hneg

/-- **Endpoint typing is preserved by reverse scope extrusion.**
Reverse scope transport recovers the exact external ownership split
from the actual restriction/parallel typing, with no closed-hole premise. -/
theorem HasType.scope_reverse {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ (.nu (.par p (liftProc 0 q)))) :
    HasType n Δ (.par (.nu p) q) := by
  obtain ⟨c, hbody⟩ := h.nu_inv
  obtain ⟨Γ, Ξ, hs, hd, hp, hq⟩ := hbody.par_inv
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
  have hp' : HasType (n + 1) (Context.bind c (Context.lower Γ₀ hΓ)) p := by
    rw [Context.bind, Context.lift_lower]
    rw [Context.restore_erased_pair]
    exact hp.restore_scope_pair hq hs
  have hab := nameAbsent_fresh_lift 0 q
  have hq' : HasType (n + 1) Ξ₀ (liftProc 0 q) :=
    (hq.erase_nameAbsent (z := ⟨.var 0, .negative⟩) hab).erase_nameAbsent
      (z := ⟨.var 0, .positive⟩) hab
  rw [houter]
  exact HasType.par hdl (HasType.nu hp') (hq'.unlift hΞ)

/-- **Endpoint typing is invariant under scope extrusion.**
Both directions of the canonical scope congruence preserve exact
external polarized ownership and the unchanged ambient binder depth. -/
theorem HasType.scope_iff {n : Nat} {Δ : Context} {p q : Proc} :
    HasType n Δ (.par (.nu p) q) ↔
      HasType n Δ (.nu (.par p (liftProc 0 q))) :=
  ⟨HasType.scope_forward, HasType.scope_reverse⟩

end Cslib.SessionTypes.Endpoint
