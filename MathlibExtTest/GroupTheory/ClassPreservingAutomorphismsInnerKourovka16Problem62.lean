/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62

open MathlibExt.GroupTheory.ClassPreservingAutomorphismsInnerKourovka16Problem62Wanted

-- Extract one group for both properties. Every candidate conjugator for the outer
-- automorphism fails on an element of that same group.
example : ∃ (G : Type) (_ : Group G),
    (∀ (α : MulAut G) (g : G), IsConj (α g) g) ∧
      ∃ α : MulAut G, ∀ h : G, ∃ g : G, α g ≠ h * g * h⁻¹ := by
  by_contra! h
  apply classPreservingAutomorphismsInner_refuted
  intro G inst hc α
  obtain ⟨k, hk⟩ := h G inst hc α
  exact ⟨k, MulEquiv.ext hk⟩
