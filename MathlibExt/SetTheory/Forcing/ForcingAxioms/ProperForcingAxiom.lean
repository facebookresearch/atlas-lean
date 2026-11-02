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

/-- **Proper Forcing Axiom.** For every proper partial order $\mathbb{P}$, every family
$\mathcal{D}$ of at most $\aleph_1$ dense subsets of $\mathbb{P}$, and every condition
$p \in \mathbb{P}$, there is a filter $G \subseteq \mathbb{P}$ with $p \in G$ that meets every
member of $\mathcal{D}$, that is, $G \cap D \neq \emptyset$ for every $D \in \mathcal{D}$.

Here a set $D \subseteq \mathbb{P}$ is dense if for every $q \in \mathbb{P}$ there is $d \in D$
with $d \le q$, and a filter is a nonempty, upward closed subset $G$ of $\mathbb{P}$ such that
any two elements of $G$ have a common lower bound in $G$.
-/
def ProperForcingAxiom : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsProperForcing P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ aleph 1 →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
