/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11

open MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11Wanted

/-- Applying the refutation to the expanded conjecture yields a contradiction. -/
example (h : ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∃ (H : Type) (_ : Group H) (_ : Finite H), IsPGroup p H ∧
      Nonempty (frattini H ≃* commutator G)) : False :=
  derivedSubgroupIsFrattini_refuted h

-- Extract a single finite p-group whose derived subgroup rules out every candidate H.
example : ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    ∀ (H : Type) [Group H] [Finite H], IsPGroup p H → IsEmpty (frattini H ≃* commutator G) := by
  by_contra h
  apply derivedSubgroupIsFrattini_refuted
  intro p hp G _ _ hG
  by_contra hG'
  apply h
  refine ⟨p, G, ‹Group G›, ‹Finite G›, hp, hG, ?_⟩
  intro H _ _ hH
  exact ⟨fun e => hG' ⟨H, ‹Group H›, ‹Finite H›, hH, ⟨e⟩⟩⟩
