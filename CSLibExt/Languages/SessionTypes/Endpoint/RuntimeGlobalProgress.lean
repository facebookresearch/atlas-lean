/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeFrontierProgress

/-!
# Qualified GLOBAL guarded-runtime progress

The only hypotheses are actual runtime typing, semantic balance and the EXISTING
all-declared-services Available predicate. Normalization, requests, minimum active
keys and complementary guards are derived inside the proof. Idle is not Cong nil.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem normal_progress {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (hn : GuardedNormal Γ p) (ht : HasType n Γ Δ p) (hb : Conversion.Balanced Δ)
    (ha : Available Γ p) : Idle Γ p ∨ ∃ q, PiCalculus.Step p q := by
  induction hn generalizing n Δ with
  | frontier hf => exact hf.progress ht hb ha
  | nu hn ih =>
    obtain ⟨c, hp⟩ := ht.nu_inv
    rcases ih hp (hb.bind c) ha with hi | ⟨q, hs⟩
    · exact Or.inl hi
    · exact Or.inr ⟨.nu q, PiCalculus.Step.nu hs⟩

/-- GLOBAL progress at arbitrary ambient n/shared Γ/actual balanced Δ/process p,
qualified ONLY by runtime typing, INITIAL semantic balance and EXISTING persistent
availability of ALL declared signatures. Result is actual Idle syntax OR a canonical
Step. No frontier/normal form/readiness/Step/fairness/representative is supplied. -/
theorem HasType.progress_balanced {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (hb : Conversion.Balanced Δ) (ha : Available Γ p) :
    Idle Γ p ∨ ∃ q, PiCalculus.Step p q := by
  obtain ⟨r, hc, ht, hn⟩ := h.frontier_normal
  rcases normal_progress hn ht hb ((Available.cong_iff hc).mp ha) with hi | ⟨q, hs⟩
  · exact Or.inl ((Idle.cong_iff hc).mpr hi)
  · exact Or.inr ⟨q, PiCalculus.Step.cong hc hs (Cong.refl _)⟩

/-- Closed empty-interface runtime progress, at arbitrary passive-name depth,
requires the SAME actual all-declared-service availability. Idle includes waiting
replicas/accepts and nil; no termination or scheduler fairness is asserted. -/
theorem HasType.progress_empty {n : Nat} {Γ : ServiceEnv} {p : Proc}
    (h : HasType n Γ ∅ p) (ha : Available Γ p) : Idle Γ p ∨ ∃ q, PiCalculus.Step p q :=
  h.progress_balanced Conversion.balanced_empty ha

/-- Every finite canonical reduction from an initially balanced, available typed
runtime retains qualified GLOBAL progress. Safety supplies actual balanced residual
ownership/advance trace, and Available.reachable supplies current persistent syntax. -/
theorem HasType.reachable_progress {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ p) (hb : Conversion.Balanced Δ) (ha : Available Γ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) : Idle Γ q ∨ ∃ r, PiCalculus.Step q r := by
  obtain ⟨Ξ, ht, hbal, hadvance⟩ := h.reachable_balanced hb hr
  exact ht.progress_balanced hbal (ha.reachable hr)

/-- Finite reachable empty-interface states retain the same qualified progress;
this is one-step safety/progress, not all-schedules eventual responsiveness. -/
theorem HasType.reachable_progress_empty {n : Nat} {Γ : ServiceEnv} {p q : Proc}
    (h : HasType n Γ ∅ p) (ha : Available Γ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) : Idle Γ q ∨ ∃ r, PiCalculus.Step q r :=
  (h.reachable_empty hr).progress_empty (ha.reachable hr)

end Cslib.SessionTypes.Endpoint.Runtime
