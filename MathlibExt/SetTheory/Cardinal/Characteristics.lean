/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 361, Logic 362
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal Set Order

-- Logic 361: Unbounded family
def IsUnboundedFamily (F : Set (ℕ → ℕ)) : Prop :=
  ¬ ∃ g : ℕ → ℕ, ∀ f ∈ F, f ≤ᶠ[Filter.atTop] g


theorem IsUnboundedFamily.mono {F G : Set (ℕ → ℕ)} (hsub : F ⊆ G)
    (h : IsUnboundedFamily F) : IsUnboundedFamily G := by
  intro ⟨g, hg⟩
  exact h ⟨g, fun f hf => hg f (hsub hf)⟩

-- Logic 362: Bounding number

noncomputable def boundingNumber : Cardinal :=
  sInf {c : Cardinal | ∃ F : Set (ℕ → ℕ), IsUnboundedFamily F ∧ #F = c}


theorem boundingNumber_le {F : Set (ℕ → ℕ)} (h : IsUnboundedFamily F) :
    boundingNumber ≤ #F :=
  csInf_le' ⟨F, h, rfl⟩

end
