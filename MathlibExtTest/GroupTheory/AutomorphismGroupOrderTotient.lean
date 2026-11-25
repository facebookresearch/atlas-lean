/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AutomorphismGroupOrderTotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # A finite noncyclic witness to the failure of the totient bound -/

open MathlibExt.GroupTheory.AutomorphismGroupOrderTotientKourovka15Problem43Wanted

example : ∃ (G : Type) (_ : Group G) (_ : Finite G),
    ¬ IsCyclic G ∧ Nat.card (MulAut G) < (Nat.card G).totient := by
  have h := totientLeAutOrder_refuted
  unfold totientLeAutOrder at h
  push Not at h
  obtain ⟨G, g, f, hlt⟩ := h
  refine ⟨G, g, f, ?_, hlt⟩
  intro hc
  exact (ne_of_lt hlt) (IsCyclic.card_mulAut G)
