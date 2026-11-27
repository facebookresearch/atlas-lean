/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20

open MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted

-- Swapping coordinates preserves the boundary but moves the corner (0, 1).
example : Set.MapsTo (Homeomorph.prodComm unitInterval unitInterval) squareBoundary squareBoundary ∧
    Homeomorph.prodComm unitInterval unitInterval ∉ boundaryFixingHomeomorphisms := by
  constructor
  · intro p hp
    rcases hp with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro h
    have he := (mem_fixingSubgroup_iff _).mp h (0, 1) (Or.inl rfl)
    exact one_ne_zero (congrArg Prod.fst he : (1 : unitInterval) = 0)

-- Every linear order has a comparison that fails after a common right multiplication.
example (r : boundaryFixingHomeomorphisms → boundaryFixingHomeomorphisms → Prop)
    (hr : IsLinearOrder _ r) : ∃ a b c, r a b ∧ ¬ r (a * c) (b * c) := by
  by_contra! h
  exact discBoundaryFixingHomeomorphismsRightOrderable_refuted ⟨r, hr, h⟩
