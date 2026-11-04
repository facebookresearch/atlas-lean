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

/-- **Countable chain condition.** A partial order $(P, \le)$ has the countable chain condition
(c.c.c.) if every antichain of $P$ is countable, where an antichain is a set of pairwise
incompatible elements: no two distinct members of it have a common lower bound in $P$.
-/
def IsCCC (P : Type*) [PartialOrder P] : Prop :=
    ∀ A : Set P, IsAntichain (fun p q : P => ∃ r, r ≤ p ∧ r ≤ q) A → A.Countable

-- Logic 13: $\sigma$-centered posets

/-- **σ-centered partial orders.** A partial order $P$ is $\sigma$-centered if there is a map
$c : P \to \mathbb{N}$ such that for every $n \in \mathbb{N}$, every finite set of elements $p$
with $c(p) = n$ has a common lower bound in $P$. Thus $P$ splits into countably many centered
pieces $c^{-1}(n)$; the empty set is among the finite sets, so $P$ must be nonempty.
-/
def IsSigmaCentered (P : Type*) [PartialOrder P] : Prop :=
  ∃ c : P → ℕ, ∀ (n : ℕ) (s : Finset P), (∀ p ∈ s, c p = n) → ∃ r : P, ∀ p ∈ s, r ≤ p

-- Logic 14: Martin's Axiom for $\sigma$-centered posets

/-- **Martin's axiom for σ-centered partial orders.** For a cardinal $\kappa$, this is the
statement that for every $\sigma$-centered partial order $P$, every family $\mathcal{D}$ of at
most $\kappa$ dense subsets of $P$ and every $p \in P$, there is a filter $G$ on $P$ with
$p \in G$ that meets every member of $\mathcal{D}$. Here $D \subseteq P$ is dense if every
element of $P$ has an element of $D$ below it, and a filter is a nonempty upward closed subset
of $P$ any two of whose elements have a common lower bound in it.
-/
def MartinAxiomSigmaCentered (κ : Cardinal) : Prop :=
   ∀ (P : Type*) [PartialOrder P], IsSigmaCentered P →
     ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
     ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

-- Logic 9: Martin's Axiom

/-- **Martin's axiom.** For a cardinal $\kappa$, $\mathrm{MA}(\kappa)$ is the statement that for
every partial order $P$ with the countable chain condition, every family $\mathcal{D}$ of at most
$\kappa$ dense subsets of $P$ and every $p \in P$, there is a filter $G$ on $P$ with $p \in G$
that meets every member of $\mathcal{D}$. Here $D \subseteq P$ is dense if every element of $P$
has an element of $D$ below it, and a filter is a nonempty upward closed subset of $P$ any two
of whose elements have a common lower bound in it.
-/
def MartinAxiom (κ : Cardinal) : Prop :=
  ∀ (P : Type*) [PartialOrder P], IsCCC P →
    ∀ D : Set (Set P), (∀ S ∈ D, IsCoinitial S) → Cardinal.mk D ≤ κ →
    ∀ p : P, ∃ G : Set P, Order.IsPFilter G ∧ p ∈ G ∧ ∀ S ∈ D, (G ∩ S).Nonempty

end MetaMathlibExt

end
