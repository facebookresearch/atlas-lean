/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeFrontier

/-! # Actual complementary runtime linear guard communication -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem output_direction {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    {a b : Name} {p : Proc} (h : HasType n Γ Δ (.out a b p))
    (hn : ∀ s sig, Γ.lookup s = some sig → a ≠ .const s) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c s := by
  cases h with
  | outName hg hs hc hh ha hb hp => exact ⟨_, _, _, rfl, hc, Or.inl hh⟩
  | outEndpoint hg hs hc hh hv he hne ha hb hp => exact ⟨_, _, _, rfl, hc, Or.inr ⟨_, _, _, hh⟩⟩
  | invoke hs hd hv hr he hg hb hp => exact False.elim (hn _ _ hs rfl)

private theorem input_direction {n : Nat} {Γ : ServiceEnv} {Δ : Context} {a : Name} {p : Proc}
    (h : HasType n Γ Δ (.inp a p)) (hn : ∀ s sig, Γ.lookup s = some sig → a ≠ .const s) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧ SendsTo c.dual s := by
  obtain ⟨e, c, he, hc, hh⟩ := h.linear_input_inv hn
  rcases hh with ⟨s, hs, hp⟩ | ⟨r, k, t, s, hs, hp⟩
  · refine ⟨e, c, s.dual, he, hc, Or.inl ?_⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl
  · refine ⟨e, c, s.dual, he, hc, Or.inr ⟨r, k, t, ?_⟩⟩
    change c.protocol.dual.unfold = _
    rw [Protocol.unfold_dual, hs]
    rfl

private theorem output_direction_conflict {c d : Capability} {s t : Protocol}
    (hc : SendsTo c s) (hd : SendsTo d t) (he : d.Equivalent c.dual) : False := by
  have hm := he.2.head
  change HeadMatch Protocol.TreeEquiv d.protocol.unfold c.protocol.dual.unfold at hm
  rcases hc with hc | ⟨r, k, v, hc⟩ <;> rcases hd with hd | ⟨r', k', v', hd⟩
  all_goals
    rw [Protocol.unfold_dual, hc, hd] at hm
    cases hm

/-- **Same-name linear guards at a compatible interface communicate.**
Actual disjoint same-name linear leaves at an INITIALLY compatible interface
have opposite directions and construct a canonical Step. Shapes/nonalias are
internally exposed outputs in the GLOBAL proof, not caller readiness hypotheses. -/
theorem same_name_linear_guards_step {n : Nat} {Γ : ServiceEnv} {Λ Θ : Context}
    {g h : Proc} {a : Name} (hg : HasType n Γ Λ g) (hh : HasType n Γ Θ h)
    (hd : Finmap.Disjoint Λ Θ) (hc : Conversion.Compatible (Λ ∪ Θ))
    (hn : ∀ s sig, Γ.lookup s = some sig → a ≠ .const s)
    (sg : (∃ b p, g = .out a b p) ∨ (∃ p, g = .inp a p))
    (sh : (∃ b p, h = .out a b p) ∨ (∃ p, h = .inp a p)) :
    ∃ q, PiCalculus.Step (.par g h) q := by
  rcases sg with ⟨b, p, rfl⟩ | ⟨p, rfl⟩ <;> rcases sh with ⟨d, q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨e, c, s, he, hce, hs⟩ := output_direction hg hn
    obtain ⟨f, u, t, hf, huf, hu⟩ := output_direction hh hn
    exact False.elim (output_direction_conflict hs hu
      (Conversion.communicating_equivalent hd hce huf (he.trans hf.symm) hc))
  · exact ⟨_, PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)⟩
  · exact ⟨_, PiCalculus.Step.cong (Cong.par_comm _ _)
      (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)) (Cong.refl _)⟩
  · obtain ⟨e, c, s, he, hce, hs⟩ := input_direction hg hn
    obtain ⟨f, u, t, hf, huf, hu⟩ := input_direction hh hn
    have heq := Conversion.communicating_equivalent hd hce huf (he.trans hf.symm) hc
    exact False.elim (output_direction_conflict hs hu heq.dual)

end Cslib.SessionTypes.Endpoint.Runtime
