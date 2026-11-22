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

/-!
# Homogeneous set

## References

* Jech (for `IsHomogeneousFor`)
-/

namespace MetaMathlibExt

-- Logic 31: Homogeneous set

/-- A set H ⊆ I is *homogeneous* for a colouring c : [I]ⁿ → γ with colour k if c(s) = k for every
n-element subset s ⊆ H.
-/
def IsHomogeneousFor {I : Type*} {γ : Type*} (n : ℕ) (c : Finset I → γ) (H : Set I) (k : γ) : Prop :=
  ∀ s : Finset I, s.card = n → (s : Set I) ⊆ H → c s = k

end MetaMathlibExt

end
