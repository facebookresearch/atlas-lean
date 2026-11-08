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

public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 49, Logic 562, Logic 581

/-!
# Proper Forcing Axiom; Proper Forcing Axiom theorems (part I); Proper Forcing Axioms theorems
  (part II)

## References

* Jech (for `ProperForcingAxiom`)
-/

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 49: Proper Forcing Axiom

/-- The Proper Forcing Axiom: For any proper poset ℙ, any condition p∈ℙ, for any sequence (D_α :
α<ω₁) of dense subsets of ℙ, there is a filter G⊆ ℙ meeting every D_α and p∈ G.
-/
def ProperForcingAxiom : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsProperForcing P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ aleph 1 →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
