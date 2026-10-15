/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Order.Antichain
public import Mathlib.Order.SetNotation
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 36, Logic 16
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 36: Special partial order
def IsSpecial.{u} (α : Type u) [PartialOrder α] : Prop :=
  ∃ f : α → ℚ, StrictMono f

def IsUnionOfOmegaAntichains.{u} (α : Type u) [PartialOrder α] : Prop :=
  ∃ F : ℕ → Set α, (∀ n, IsAntichain (· ≤ ·) (F n)) ∧ (⋃ n, F n) = Set.univ


theorem isUnionOfOmegaAntichains_nat : IsUnionOfOmegaAntichains ℕ :=
  ⟨fun n => {n}, fun n => Set.subsingleton_singleton.isAntichain _, by ext x; simp⟩

end
