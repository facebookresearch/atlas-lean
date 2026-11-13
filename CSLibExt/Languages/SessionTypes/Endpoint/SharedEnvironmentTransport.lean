/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SharedEnvironment
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra

/-! # Static shared/linear separation under canonical ownership operations -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Erasing an actual owned key cannot create a shared/linear name alias. -/
theorem Separated.erase {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ) (e : Key) :
    Separated Γ (Δ.erase e) := by
  intro x c hx s sig hs
  by_cases he : x = e
  · subst x
    rw [Finmap.lookup_erase] at hx
    cases hx
  · rw [Finmap.lookup_erase_ne he] at hx
    exact h x c hx s sig hs

/-- Inserting a statically nonshared key preserves physical-name separation. -/
theorem Separated.insert {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ)
    (e : Key) (c : Capability) (he : ∀ s sig, Γ.lookup s = some sig → e.name ≠ .const s) :
    Separated Γ (Δ.insert e c) := by
  intro x v hx s sig hs
  by_cases hxe : x = e
  · subst x
    exact he s sig hs
  · rw [Finmap.lookup_insert_of_ne _ hxe] at hx
    exact h x v hx s sig hs

set_option backward.isDefEq.respectTransparency false in
/-- Actual binder lifting preserves nonshared physical names: constants cannot
be newly produced by lifting a linear variable. -/
theorem Separated.lift {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ) (k : Nat) :
    Separated Γ (Context.lift k Δ) := by
  intro e c he s sig hs hn
  rw [Context.lift, Context.lookup_rekey] at he
  obtain ⟨d, hd, rfl⟩ := he
  exact h d c hd s sig hs (liftName_injective k hn)

/-- A literal private pair has variable names, never declared shared constants. -/
theorem Separated.bind {Γ : ServiceEnv} {Δ : Context} (h : Separated Γ Δ) (c : Capability) :
    Separated Γ (Context.bind c Δ) := by
  apply ((h.lift 0).insert ⟨.var 0, .positive⟩ c (by intro s sig hs he; cases he)).insert
    ⟨.var 0, .negative⟩ c.dual
  intro s sig hs he
  cases he

/-- A left child of the actual ownership union retains static shared-name separation. -/
theorem Separated.union_left {Γ : ServiceEnv} {Δ Θ : Context} (h : Separated Γ (Δ ∪ Θ)) :
    Separated Γ Δ := by
  intro e c he s sig hs
  exact h e c ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some he)).trans he) s sig hs

/-- Disjointness prevents right-child lookup shadowing by the left ownership domain. -/
theorem Separated.union_right {Γ : ServiceEnv} {Δ Θ : Context} (h : Separated Γ (Δ ∪ Θ))
    (hd : Finmap.Disjoint Δ Θ) : Separated Γ Θ := by
  intro e c he s sig hs
  have hn : e ∉ Δ := fun hm => hd e hm (Finmap.mem_of_lookup_eq_some he)
  exact h e c ((Finmap.lookup_union_right hn).trans he) s sig hs

end Cslib.SessionTypes.Endpoint.Runtime
