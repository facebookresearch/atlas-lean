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

public import Mathlib.Data.Finset.Card
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 31
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 31: Homogeneous set
def IsHomogeneousFor {I : Type*} {γ : Type*} (n : ℕ) (c : Finset I → γ) (H : Set I) (k : γ) : Prop :=
  ∀ s : Finset I, s.card = n → (s : Set I) ⊆ H → c s = k

end
