/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionProgress

/-!
# Global process-level progress of finite ranked conversion networks

Normalization and the minimum-ranked complementary guards are derived inside
these proofs. There is no caller frontier, readiness or progress assumption.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Conversion-ranked processes have a typed frontier normal form.**
Normalization is derived from finite syntax, then NEW ranked Cong keeps ownership. -/
theorem RankedType.frontier_normal {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) : ∃ q, Cong p q ∧ RankedType n Δ q ∧ FrontierNormal q := by
  obtain ⟨q, hc, hn⟩ := finiteLinear_frontier_normal h.hasType.finiteLinear
  exact ⟨q, hc, (RankedType.cong_iff hc).mp h, hn⟩

private theorem normal_progress {n : Nat} {Δ : Context} {p : Proc}
    (hn : FrontierNormal p) (ht : RankedType n Δ p) (hb : Balanced Δ) :
    Cong p .nil ∨ ∃ q, PiCalculus.Step p q := by
  induction hn generalizing n Δ with
  | frontier hf => exact GuardFrontier.progress hf ht hb
  | nu hn ih =>
    obtain ⟨c, hbody⟩ := ht.nu_inv
    rcases ih hbody (hb.bind c) with hc | ⟨q, hs⟩
    · exact Or.inl (Cong.trans (Cong.nu_cong hc) Cong.nu_nil)
    · exact Or.inr ⟨.nu q, PiCalculus.Step.nu hs⟩

/-- **Global progress of conversion-ranked processes at balanced interfaces.**
For a ranked-typed process at ANY balanced interface, global progress
holds, including disconnected networks.
All private channels are tracked through the derived restriction tower.
Completion means process congruence to nil, not completion of the interface. -/
theorem RankedType.progress_balanced {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) (hb : Balanced Δ) :
    Cong p .nil ∨ ∃ q, PiCalculus.Step p q := by
  obtain ⟨r, hc, ht, hn⟩ := h.frontier_normal
  rcases normal_progress hn ht hb with hnil | ⟨q, hs⟩
  · exact Or.inl (Cong.trans hc hnil)
  · exact Or.inr ⟨q, PiCalculus.Step.cong hc hs (Cong.refl _)⟩

/-- **Closed conversion-ranked networks are completed or can step.**
A closed finite ranked network is completed or takes an ACTUAL canonical
step. Ambient passive-name depth is arbitrary; no readiness witness is supplied. -/
theorem RankedType.progress_empty {n : Nat} {p : Proc} (h : RankedType n ∅ p) :
    Cong p .nil ∨ ∃ q, PiCalculus.Step p q := h.progress_balanced balanced_empty

/-- **Progress at reachable states of closed conversion-ranked networks.**
Global progress holds at every finite reachable state of a closed ranked
network. No fairness, eventual liveness or recursive termination is asserted. -/
theorem RankedType.reachable_progress {n : Nat} {p q : Proc} (h : RankedType n ∅ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    Cong q .nil ∨ ∃ r, PiCalculus.Step q r := (h.reachable_empty hr).progress_empty

end Cslib.SessionTypes.Endpoint.Conversion
