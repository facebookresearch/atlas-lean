/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Substitution

/-!
# Inverse transport of an outer ownership context through a fresh binder
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

private theorem outer_name_roundtrip {a : Name} (ha : a ≠ .var 0) :
    liftName 0 (substName (.const 0) 0 a) = a := by
  cases a with
  | const => rfl
  | var i =>
    cases i with
    | zero => exact False.elim (ha rfl)
    | succ i => simp [substName, liftName]

/-- **Lowering then lifting an outer key returns it.**
Canonical lowering and lifting cancel for a polarized outer key,
provided it is not either role of the freshly inserted physical name. -/
theorem Key.lift_subst_outer_name (e : Key) (he : e.name ≠ .var 0) :
    Key.mapName (liftName 0) (Key.mapName (substName (.const 0) 0) e) = e := by
  cases e with
  | mk a r =>
    have hn := outer_name_roundtrip he
    simp only [Key.mapName, hn]

/-- **Lowering is injective on contexts without fresh-name keys.**
Canonical lowering is injective on an outer context with no fresh-name
role. The inverse is canonical lift, not a guessed fresh constant identity. -/
theorem Context.injOn_lower {Γ : Context}
    (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) :
    Set.InjOn (Key.mapName (substName (.const 0) 0)) {e | e ∈ Γ} := by
  intro e he d hd hed
  have hl := congrArg (Key.mapName (liftName 0)) hed
  rw [Key.lift_subst_outer_name e (hΓ e he),
    Key.lift_subst_outer_name d (hΓ d hd)] at hl
  exact hl

/-- **Lowering of an outer context past a fresh binder.**
Remove a fresh ambient binder from a finite outer ownership context. -/
def Context.lower (Γ : Context) (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) : Context :=
  Context.rekey (Key.mapName (substName (.const 0) 0)) Γ (Context.injOn_lower hΓ)

/-- **Lifting a lowered context recovers it.**
Lifting the recovered outer context restores every key and capability. -/
theorem Context.lift_lower (Γ : Context) (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) :
    Context.lift 0 (Context.lower Γ hΓ) = Γ := by
  apply Finmap.ext
  change (Γ.entries.map (fun x =>
    (⟨Key.mapName (substName (.const 0) 0) x.1, x.2⟩ :
      Sigma (fun _ : Key => Capability)))).map
      (fun x => ⟨Key.mapName (liftName 0) x.1, x.2⟩) = Γ.entries
  rw [Multiset.map_map]
  calc
    _ = Γ.entries.map id := by
      apply Multiset.map_congr rfl
      rintro ⟨e, c⟩ he
      have hem : e ∈ Γ := Multiset.mem_map_of_mem Sigma.fst he
      simp only [Function.comp_apply, Key.lift_subst_outer_name e (hΓ e hem), id_eq]
    _ = Γ.entries := Multiset.map_id _

/-- **Endpoint typing reflects through binder lifting.**
Typing an actually lifted term under outer-only ownership reflects
back to its exact recovered context; no closed-hole premise is required. -/
theorem HasType.unlift {n : Nat} {Γ : Context} {q : Proc}
    (h : HasType (n + 1) Γ (liftProc 0 q))
    (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) :
    HasType n (Context.lower Γ hΓ) q := by
  have h' : HasType (n + 1) (Context.lift 0 (Context.lower Γ hΓ)) (liftProc 0 q) := by
    rw [Context.lift_lower]
    exact h
  have ht := h'.subst_passive (b := .const 0) trivial
  change HasType n (Context.lower Γ hΓ) (substProc (.const 0) 0 (liftProc 0 q)) at ht
  rw [substProc_liftProc] at ht
  exact ht

/-- **Erasing both roles of the fresh name leaves outer keys.**
Removing both roles of var zero leaves only genuine outer-name keys. -/
theorem Context.erased_pair_outer (Γ : Context) :
    ∀ e ∈ (Γ.erase (⟨.var 0, .negative⟩ : Key)).erase
      (⟨.var 0, .positive⟩ : Key), e.name ≠ .var 0 := by
  intro e he hn
  obtain ⟨hp, he'⟩ := Finmap.mem_erase.mp he
  obtain ⟨hm, _⟩ := Finmap.mem_erase.mp he'
  cases e with
  | mk a r =>
    cases r with
    | positive => exact hp (Key.ext hn rfl)
    | negative => exact hm (Key.ext hn rfl)

/-- **Context lifting is injective.**
Canonical context lifting is injective, including recorded completed slots. -/
theorem Context.lift_zero_injective : Function.Injective (Context.lift 0) := by
  intro Γ Ξ h
  apply Finmap.ext_lookup
  intro e
  apply Option.ext
  intro c
  rw [← Context.lookup_lift (k := 0) (Δ := Γ) (e := e) (c := c),
    ← Context.lookup_lift (k := 0) (Δ := Ξ) (e := e) (c := c), h]

/-- **Lowering preserves disjointness of outer contexts.**
Lowering disjoint outer-only contexts preserves their exact key split. -/
theorem Context.disjoint_lower {Γ Ξ : Context}
    (hΓ : ∀ e ∈ Γ, e.name ≠ .var 0) (hΞ : ∀ e ∈ Ξ, e.name ≠ .var 0)
    (hd : Finmap.Disjoint Γ Ξ) :
    Finmap.Disjoint (Context.lower Γ hΓ) (Context.lower Ξ hΞ) := by
  have hU : ∀ e ∈ Γ ∪ Ξ, e.name ≠ .var 0 := by
    intro e he
    rcases Finmap.mem_union.mp he with he | he
    · exact hΓ e he
    · exact hΞ e he
  apply Context.disjoint_rekey
  · intro e he d hd hed
    exact Context.injOn_lower hU (Finmap.mem_union.mpr he) (Finmap.mem_union.mpr hd) hed
  · exact hd

end Cslib.SessionTypes.Endpoint
