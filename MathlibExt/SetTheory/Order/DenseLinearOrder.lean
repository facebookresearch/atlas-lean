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

public import Mathlib.Order.Defs.Unbundled
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 20
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 20: Dense linear order without endpoints
 def IsDenseLinearOrderWithoutEndpoints {α : Type*} (r : α → α → Prop) : Prop :=
    IsStrictTotalOrder α r ∧
    (∀ a b, r a b → ∃ c, r a c ∧ r c b) ∧
    (∀ a, ∃ b, r b a) ∧
    (∀ a, ∃ b, r a b)

end
