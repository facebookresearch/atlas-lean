/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.FiniteContext
public import CSLibExt.Languages.SessionTypes.Endpoint.Typing

/-!
# Transport of the original finite typing API

Finite slots are lifted without changing their constant subjects. Passive
input binders remain data binders and do not introduce linear subjects.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

set_option backward.isDefEq.respectTransparency false in
/-- **Binder lift fixes the finite ownership map.**
The finite bridge's constant-only ownership is unaffected by binder lift. -/
theorem Context.lift_ofFinite (Γ : Cslib.SessionTypes.Context) (bound k : Nat)
    (r : Role) (rank : Nat → Nat) :
    Context.lift k (Context.ofFinite Γ bound r rank) =
      Context.ofFinite Γ bound r rank := by
  apply Context.rekey_eq
  intro e he
  obtain ⟨i, _, rfl⟩ := (Context.mem_ofFinite Γ bound r rank e).mp he
  rfl

private theorem active_lt_bound {Γ : Cslib.SessionTypes.Context}
    {bound a : Nat} (hbound : ∀ c, bound ≤ c → Γ c = .end)
    (ha : Γ a ≠ .end) : a < bound := by
  apply Nat.lt_of_not_ge
  intro hge
  exact ha (hbound a hge)

/-- **Finite passive-name typing embeds into endpoint typing.**
Every original finite passive-name derivation embeds with its exact
protocol obligations and a bounded finite map of either endpoint role. -/
theorem HasType.ofFinite {n : Nat} {Γ : Cslib.SessionTypes.Context} {p : Proc}
    (h : Cslib.SessionTypes.HasType n Γ p) (bound : Nat)
    (hbound : ∀ c, bound ≤ c → Γ c = .end) (r : Role) (rank : Nat → Nat) :
    HasType n (Context.ofFinite Γ bound r rank) p := by
  induction h generalizing bound with
  | @nil n Γ hΓ =>
    apply HasType.nil (Context.completed_ofFinite Γ bound r rank hΓ)
    intro e he
    obtain ⟨i, _, rfl⟩ := (Context.mem_ofFinite Γ bound r rank e).mp he
    trivial
  | @out n a Γ b s p ha hb hp ih =>
    have hab : a < bound := active_lt_bound hbound (by simp [ha])
    apply HasType.outName (e := ⟨.const a, r⟩)
      (c := ⟨rank a, Protocol.ofFinite (Γ a)⟩) (s := Protocol.ofFinite s)
    · simp [Context.lookup_ofFinite, hab]
    · simp [ha, Protocol.ofFinite, Protocol.unfold]
    · trivial
    · exact hb
    · rw [← Context.ofFinite_advance Γ bound a hab s r rank]
      apply ih
      intro c hc
      have hca : c ≠ a := by omega
      simp [Cslib.SessionTypes.advance, hca, hbound c hc]
  | @inp n a Γ s p ha hp ih =>
    have hab : a < bound := active_lt_bound hbound (by simp [ha])
    apply HasType.inpName (e := ⟨.const a, r⟩)
      (c := ⟨rank a, Protocol.ofFinite (Γ a)⟩) (s := Protocol.ofFinite s)
    · simp [Context.lookup_ofFinite, hab]
    · simp [ha, Protocol.ofFinite, Protocol.unfold]
    · trivial
    · rw [← Context.ofFinite_advance Γ bound a hab s r rank,
        Context.lift_ofFinite]
      apply ih
      intro c hc
      have hca : c ≠ a := by omega
      simp [Cslib.SessionTypes.advance, hca, hbound c hc]

end Cslib.SessionTypes.Endpoint
