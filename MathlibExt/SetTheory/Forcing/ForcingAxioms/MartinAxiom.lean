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

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.PFilter
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 10, Logic 13, Logic 14, Logic 9

/-!
# `MathlibExt.SetTheory.Forcing.ForcingAxioms.MartinAxiom`

## References

* Kunen (for `IsCCC`, `MartinAxiom`)
* Handbook of Set Theory (for `IsSigmaCentered`, `MartinAxiomSigmaCentered`)
-/

namespace MetaMathlibExt

-- Logic 10: Countable chain condition in a partial order

/-- A partial order (P, ≤) has the countable chain condition (c.c.c.) if every antichain is
countable.
-/
def IsCCC (P : Type*) [PartialOrder P] : Prop :=
    ∀ A : Set P, IsAntichain (fun p q : P => ∃ r, r ≤ p ∧ r ≤ q) A → A.Countable

-- Logic 13: $\sigma$-centered posets

/-- A poset is σ-centred when it splits into countably many centered pieces: every
  finite subset of a piece has a common lower bound.
-/
def IsSigmaCentered (P : Type*) [PartialOrder P] : Prop :=
  ∃ c : P → ℕ, ∀ (n : ℕ) (s : Finset P), (∀ p ∈ s, c p = n) → ∃ r : P, ∀ p ∈ s, r ≤ p

-- Logic 14: Martin's Axiom for $\sigma$-centered posets

/-- Martin's Axiom for σ-centred posets: any σ-centered poset (P,≤), for any sequence (D_α : α<κ')
of dense subsets of the partial order for some κ'≤ κ, for any condition p∈ P, there is a filter G
meeting all D_α's and p∈ G.
-/
def MartinAxiomSigmaCentered (κ : Cardinal) : Prop :=
   ∀ (P : Type*) [PartialOrder P], IsSigmaCentered P →
     ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
     ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

-- Logic 9: Martin's Axiom

/-- MA(κ) is the statement that for any ccc poset (P,≤), for any sequence (D_α : α<κ') of dense
subsets of the partial order for some κ'≤ κ, for any condition p∈ P, there is a filter G meeting all
D_α's and p∈ G.
-/
def MartinAxiom (κ : Cardinal) : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsCCC P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
