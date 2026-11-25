/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of products of two class transpositions (Kourovka Notebook Problem 18.48)

Kourovka Notebook, Problem 18.48 (S. Kohl), marked solved in the 21st issue: is it true that there
are only finitely many integers which occur as orders of products of two class transpositions? (For
the definition, see 17.57.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.48 (S. Kohl). UnsolvedMath record
UM-00701477 (`KOU-18.48`), dataset ulamai/UnsolvedMath v1.8.0.

Kourovka 17.57: for `0 ≤ r < m` let `r(m) = {r + k m | k ∈ ℤ}`; for disjoint `r₁(m₁)`, `r₂(m₂)` the
class transposition `τ_{r₁(m₁), r₂(m₂)}` interchanges `r₁ + k m₁` and `r₂ + k m₂` for each `k ∈ ℤ`
and fixes everything else (the encoding of the OpenConjectures entry
`Kourovka2175ClassTranspositionSubgroups`). Orders are positive integers; products of infinite order
(`orderOf = 0`) do not count.
-/

/-- **Residue class.** For integers $r$ and $m$, the residue class $r(m)$ is the set
$\{x \in \mathbb{Z} : x \equiv r \pmod{m}\} = \{r + k m : k \in \mathbb{Z}\}$. -/
def resClass (r m : ℤ) : Set ℤ := {x | x ≡ r [ZMOD m]}

/-- **Class transposition of two residue classes.** For integers $r_1, m_1, r_2, m_2$, write
$r_1(m_1) = r_1 + m_1\mathbb{Z}$ and $r_2(m_2) = r_2 + m_2\mathbb{Z}$ for the residue classes. A
permutation $\sigma$ of $\mathbb{Z}$ is the class transposition $\tau_{r_1(m_1), r_2(m_2)}$ when
$0 \le r_1 < m_1$ and $0 \le r_2 < m_2$, the residue classes $r_1(m_1)$ and $r_2(m_2)$ are
disjoint, $\sigma$ interchanges $r_1 + k m_1$ and $r_2 + k m_2$ for every integer $k$, and
$\sigma$ fixes every integer outside $r_1(m_1) \cup r_2(m_2)$.

This is the definition of class transpositions in Kourovka Problem 17.57. -/
def IsClassTrans (σ : Equiv.Perm ℤ) (r₁ m₁ r₂ m₂ : ℤ) : Prop :=
  0 ≤ r₁ ∧ r₁ < m₁ ∧ 0 ≤ r₂ ∧ r₂ < m₂ ∧ 0 < m₁ ∧ 0 < m₂ ∧
  Disjoint (resClass r₁ m₁) (resClass r₂ m₂) ∧
  (∀ k : ℤ, σ (r₁ + k * m₁) = r₂ + k * m₂ ∧ σ (r₂ + k * m₂) = r₁ + k * m₁) ∧
  ∀ x : ℤ, x ∉ resClass r₁ m₁ → x ∉ resClass r₂ m₂ → σ x = x

/-- **Class transpositions of the integers.** A permutation $\sigma$ of $\mathbb{Z}$ is a class
transposition when it is the class transposition $\tau_{r_1(m_1), r_2(m_2)}$ for some integers
$r_1, m_1, r_2, m_2$. -/
def IsClassTransposition (σ : Equiv.Perm ℤ) : Prop :=
  ∃ r₁ m₁ r₂ m₂ : ℤ, IsClassTrans σ r₁ m₁ r₂ m₂

/-- **Claim of Kourovka Problem 18.48.** Only finitely many positive integers occur as orders of
products $\sigma\tau$ of two class transpositions $\sigma$ and $\tau$ of $\mathbb{Z}$. -/
def classTranspositionProductOrdersFinite : Prop :=
  {k : ℕ | 0 < k ∧ ∃ σ τ : Equiv.Perm ℤ, IsClassTransposition σ ∧ IsClassTransposition τ ∧
    orderOf (σ * τ) = k}.Finite

/--
**Products of two class transpositions have only finitely many orders.** The claim of Kourovka
Problem 18.48 holds: the set of positive integers $k$ such that $\sigma\tau$ has order $k$ for some
class transpositions $\sigma$ and $\tau$ of $\mathbb{Z}$ is finite.

Iskra (2026), accepted in the Kourovka Notebook (21st issue), proves that every finite order of a
product of two class transpositions divides $840$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.48 (S. Kohl); resolution: A. Iskra,
Finite orders of products of two class transpositions divide 840, preprint, arXiv:2610.01793
(2026), abstract: if the product of two class transpositions has finite order, then its order
divides 840 (sharp); this answers Question 18.48 affirmatively, as the Kourovka Notebook (21st
issue) records, https://arxiv.org/abs/2610.01793.
-/
public theorem_wanted classTranspositionProductOrdersFinite_holds :
    classTranspositionProductOrdersFinite

end MathlibExt.GroupTheory.ClassTranspositionProductOrdersKourovka18Problem48Wanted
