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

public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 340, Logic 355, Logic 356, Logic 357

/-!
# `MathlibExt.SetTheory.Dichotomies.PIdeal`

## References

* Jech (for `SubsetModFinite`, `IsPIdeal`, `IsOrthogonalTo`, `PIdealDichotomy`)
-/

namespace MetaMathlibExt

-- Logic 340: Subset mod finite

/-- **Inclusion modulo finite.** For subsets $a$ and $b$ of a set $\alpha$, $a \subseteq^* b$
($a$ is almost contained in $b$) if the difference $a \setminus b$ is finite. -/
def SubsetModFinite {α : Type*} (a b : Set α) : Prop := (a \ b).Finite

-- Logic 355: P-ideal

/-- **P-ideal of countable sets.** A family $I$ of subsets of a set $\alpha$ is a P-ideal of
countable sets if every member of $I$ is countable, every subset of a member of $I$ is in $I$,
every finite subset of $\alpha$ is in $I$, $I$ is closed under binary unions, and for every
sequence $(a_n)_{n \in \mathbb{N}}$ of members of $I$ there is $b \in I$ with $a_n \subseteq^* b$
(that is, $a_n \setminus b$ is finite) for every $n$.
-/
structure IsPIdeal {α : Type*} (I : Set (Set α)) : Prop where
  countable : ∀ a ∈ I, a.Countable
  downward : ∀ a ∈ I, ∀ b ⊆ a, b ∈ I
  finite_mem : ∀ a : Set α, a.Finite → a ∈ I
  union_mem : ∀ a ∈ I, ∀ b ∈ I, a ∪ b ∈ I
  sigma_directed : ∀ f : ℕ → Set α, (∀ n, f n ∈ I) → ∃ b ∈ I, ∀ n, SubsetModFinite (f n) b

-- Logic 356: Is Orthogonal To

/-- **Orthogonality to a family of sets.** Let $I$ be a family of subsets of a set $\alpha$. A
set $X \subseteq \alpha$ is orthogonal to $I$ if $X \cap a$ is finite for every $a \in I$.
-/
def IsOrthogonalTo {α : Type*} (I : Set (Set α)) (X : Set α) : Prop :=
  ∀ a ∈ I, (X ∩ a).Finite

-- Logic 357: P-ideal dichotomy

/-- The P-ideal dichotomy (PID): for every P-ideal I of countable subsets of an uncountable
set, either some uncountable set has all its countable subsets in I, or the whole set is a
countable union of sets orthogonal to I.
-/
def PIdealDichotomy.{u} : Prop :=
  ∀ (α : Type u) (I : Set (Set α)), ¬ (Set.univ : Set α).Countable → IsPIdeal I →
    (∃ A : Set α, ¬ A.Countable ∧ ∀ x ∈ CountableSubsets α, x ⊆ A → x ∈ I) ∨
    (∃ F : ℕ → Set α, (⋃ n, F n) = Set.univ ∧ ∀ n, IsOrthogonalTo I (F n))

end MetaMathlibExt

end
