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

-- Source: Lean Definition Library (Airtable) records: Logic 16, Logic 36

/-!
# Union of ω antichains; Special partial order

## References

* Jech (for `IsUnionOfOmegaAntichains`, `IsSpecial`)
-/

namespace MetaMathlibExt

-- Logic 16: Union of ω antichains

/-- A partial order (P, ≤) is a *union of ω antichains* if P = ⋃_{n<ω} Aₙ where each Aₙ ⊆ P is an
antichain (a set of pairwise ≤-incomparable elements).
-/
def IsUnionOfOmegaAntichains.{u} (α : Type u) [PartialOrder α] : Prop :=
  ∃ F : ℕ → Set α, (∀ n, IsAntichain (· ≤ ·) (F n)) ∧ (⋃ n, F n) = Set.univ

-- Logic 36: Special partial order

/-- A partial order (α,≤) is *special* if there is a map
f : α → ℚ that is strictly increasing, i.e.\
x < y implies f(x) < f(y).  Note that f need not be injective:
nothing is required of incomparable elements.
-/
def IsSpecial.{u} (α : Type u) [PartialOrder α] : Prop :=
  ∃ f : α → ℚ, StrictMono f

end MetaMathlibExt

end
