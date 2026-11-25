/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import MathlibExt.GroupTheory.KourovkaCompositionFactor

open MathlibExt.GroupTheory.KourovkaNotebookShared

private abbrev Two := Multiplicative (ZMod 2)

example : IsCompositionFactor Two Two := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Two = 2 := by
    change Nat.card (ZMod 2) = 2
    exact Nat.card_eq_fintype_card.trans (ZMod.card 2)
  refine ⟨isSimpleGroup_of_prime_card hcard, ⊤, Subgroup.IsSubnormal.top,
    (⊤ : Subgroup Two).subtype, fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩

example : ¬ IsCompositionFactor (⊥ : Subgroup Two) Two := by
  intro h
  exact not_nontrivial _ h.1.toNontrivial
