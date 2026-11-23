/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RenameTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.ScopeTransport

/-!
# Full endpoint typing under canonical restriction swapping
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Swap ownership of two existing ambient binders without altering any role. -/
def Context.swap (k : Nat) (Δ : Context) : Context :=
  rekey (Key.mapName (swapNameAt k)) Δ
    (fun _ _ _ _ h => Key.mapName_injective (swapNameAt_injective k) h)

/-- Canonical swapping preserves full finite-process endpoint typing. -/
theorem HasType.swap {n k : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) (hk : k + 1 < n) :
    HasType n (Context.swap k Δ) (swapProc k p) := by
  have hf : Set.InjOn (Key.mapName (swapNameAt k)) {e | e ∈ Δ} := by
    intro x _ y _ hxy
    exact Key.mapName_injective (swapNameAt_injective k) hxy
  have ht := h.rename (fun a ha => (closedAt_swapName_iff n k hk a).mpr ha) hf
  simpa only [Context.swap, mapProc_swapNameAt] using ht

set_option backward.isDefEq.respectTransparency false in
/-- Swapping maps an inserted capability to the swapped role key verbatim. -/
theorem Context.swap_insert (k : Nat) (Δ : Context) (e : Key) (c : Capability) :
    Context.swap k (Δ.insert e c) =
      (Context.swap k Δ).insert (Key.mapName (swapNameAt k) e) c := by
  apply Context.rekey_insert
  intro x _ y _ hxy
  exact Key.mapName_injective (swapNameAt_injective k) hxy

/-- Two lifts put all outer names above both swapped binder indices. -/
theorem Context.swap_double_lift (Δ : Context) :
    Context.swap 0 (Context.lift 0 (Context.lift 0 Δ)) =
      Context.lift 0 (Context.lift 0 Δ) := by
  apply Context.rekey_eq
  intro e he
  obtain ⟨a, ha, rfl⟩ := Context.mem_rekey.mp he
  obtain ⟨b, _, rfl⟩ := Context.mem_rekey.mp ha
  cases b with
  | mk a r =>
    cases a with
    | const => rfl
    | var i => simp [Key.mapName, liftName, swapNameAt]

/-- Swapping nested restrictions exchanges their complete dual pairs and
fixes all lifted outer ownership, rather than forgetting any bound capability. -/
theorem Context.swap_bind_bind (Δ : Context) (c d : Capability) :
    Context.swap 0 (Context.bind d (Context.bind c Δ)) =
      Context.bind c (Context.bind d Δ) := by
  simp only [Context.bind, Context.lift_insert, Context.swap_insert,
    Context.swap_double_lift]
  simp only [Key.mapName, liftName, swapNameAt, Nat.zero_le, ↓reduceIte]
  apply Finmap.ext_lookup
  intro e
  by_cases h0p : e = (⟨.var 0, .positive⟩ : Key) <;>
    by_cases h0n : e = (⟨.var 0, .negative⟩ : Key) <;>
    by_cases h1p : e = (⟨.var 1, .positive⟩ : Key) <;>
    by_cases h1n : e = (⟨.var 1, .negative⟩ : Key) <;>
    simp_all [Finmap.lookup_insert_of_ne] <;>
    subst e <;> simp

end Cslib.SessionTypes.Endpoint
