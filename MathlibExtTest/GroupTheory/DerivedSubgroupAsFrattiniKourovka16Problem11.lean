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
