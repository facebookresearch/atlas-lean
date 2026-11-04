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

public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 43, Logic 44, Logic 45, Logic 46, Logic 47, Logic 48

/-!
# `MathlibExt.SetTheory.Forcing.ForcingAxioms.Proper`

## References

* Jech (for `modelConds`, `modelSets`, `IsCompatible`, `IsPredenseBelow`, `IsGenericFor`,
  `IsProperForcing`)
-/

namespace MetaMathlibExt

-- Logic 43: Conditions belonging to a model

/-- **Conditions in a model.** Let $\mathbb{P}$ be a set and $M$ a subset of the disjoint union
$\mathbb{P} \sqcup \mathcal{P}(\mathbb{P})$. The conditions in $M$ form the set $M_c$ of those
$p \in \mathbb{P}$ whose copy in the disjoint union belongs to $M$; informally,
$M_c = M \cap \mathbb{P}$. -/
def modelConds {P : Type*} (M : Set (P ⊕ Set P)) : Set P := Sum.inl ⁻¹' M

-- Logic 44: Subsets belonding to a model

/-- **Sets of conditions in a model.** Let $\mathbb{P}$ be a set and $M$ a subset of the disjoint
union $\mathbb{P} \sqcup \mathcal{P}(\mathbb{P})$. The sets of conditions in $M$ form the family
$M_s$ of those $D \subseteq \mathbb{P}$ whose copy in the disjoint union belongs to $M$;
informally, $M_s = M \cap \mathcal{P}(\mathbb{P})$. -/
def modelSets {P : Type*} (M : Set (P ⊕ Set P)) : Set (Set P) := Sum.inr ⁻¹' M

-- Logic 45: Compatibility

/-- **Compatible conditions.** Two elements $p$ and $q$ of a partial order $\mathbb{P}$ are
compatible if there is $r \in \mathbb{P}$ with $r \le p$ and $r \le q$. -/
def IsCompatible {P : Type*} [PartialOrder P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

-- Logic 46: Predense below

/-- **Predense below a condition.** A set $A \subseteq \mathbb{P}$ of elements of a partial order
$\mathbb{P}$ is predense below $q \in \mathbb{P}$ if for every $r \le q$ there is $a \in A$ such
that $r$ and $a$ are compatible.
-/
def IsPredenseBelow {P : Type*} [PartialOrder P] (A : Set P) (q : P) : Prop :=
  ∀ r ≤ q, ∃ a ∈ A, IsCompatible r a

-- Logic 47: $(M,P)$-generic condition

/-- **(M, ℙ)-generic conditions.** Let $\mathbb{P}$ be a partial order and $M$ a subset of the
disjoint union $\mathbb{P} \sqcup \mathcal{P}(\mathbb{P})$. Write $M_c$ for the set of
$p \in \mathbb{P}$ whose copy in the disjoint union lies in $M$, and $M_s$ for the set of
$D \subseteq \mathbb{P}$ whose copy lies in $M$. A condition $q \in \mathbb{P}$ is
$(M, \mathbb{P})$-generic if for every $D \in M_s$ that is dense in $\mathbb{P}$ (every element
of $\mathbb{P}$ has an element of $D$ below it), the set $D \cap M_c$ is predense below $q$: for
every $r \le q$ there are $a \in D \cap M_c$ and $s \in \mathbb{P}$ with $s \le r$ and $s \le a$.

No condition is imposed on $M$ here. In the intended application $M$ is the trace of a countable
elementary submodel of $H(\theta)$, for a sufficiently large regular cardinal $\theta$, that
contains $\mathbb{P}$; genericity depends only on $M_c$ and $M_s$, and the elementarity is
supplied by the club in the definition of proper partial orders.
-/
def IsGenericFor {P : Type*} [PartialOrder P] (M : Set (P ⊕ Set P)) (q : P) : Prop :=
  ∀ D ∈ modelSets M, IsCoinitial D → IsPredenseBelow (D ∩ modelConds M) q

-- Logic 48: Proper Forcings

/-- **Proper partial orders.** Let $\mathbb{P}$ be a partial order and let $X$ be the disjoint
union $\mathbb{P} \sqcup \mathcal{P}(\mathbb{P})$; for $M \subseteq X$ write $M_c$ for the set of
$p \in \mathbb{P}$ whose copy in $X$ lies in $M$. Then $\mathbb{P}$ is proper if there is a club
$C$ in $[X]^\omega$ such that for every $M \in C$ and every $p \in M_c$ there is an
$(M, \mathbb{P})$-generic condition $q \le p$. Here a club in $[X]^\omega$ is a family of
countable subsets of $X$ such that every countable subset of $X$ is contained in a member of the
family, and the union of every increasing sequence $M_0 \subseteq M_1 \subseteq \cdots$ of
members of the family is again a member.

The usual requirement $\mathbb{P} \in M$ is not imposed: $\mathbb{P}$ is an element of $X$ (as a
subset of itself), and since $C$ is cofinal it has members containing it.
-/
def IsProperForcing (P : Type*) [PartialOrder P] : Prop :=
  ∃ C : Set (Set (P ⊕ Set P)), IsClubOmega C ∧
    ∀ M ∈ C, ∀ p ∈ modelConds M, ∃ q ≤ p, IsGenericFor M q

end MetaMathlibExt

end
