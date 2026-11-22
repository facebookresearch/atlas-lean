/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Involutions in quotients by a normal closure (Kourovka Notebook Problem 18.94)

Kourovka Notebook, Archive of Solved Problems, Problem 18.94 (A. I. Sozutov): let `G` be a group
without involutions, `a` an element of it that is not a square of any element of `G`, and `n` an odd
positive integer. Is it true that the quotient `G / ⟨(aⁿ)^G⟩` does not contain involutions?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.94 (A. I.
Sozutov). UnsolvedMath record UM-00701523 (`KOU-18.94`), dataset ulamai/UnsolvedMath v1.8.0.

Without involutions means `g² = 1 → g = 1`; `⟨(aⁿ)^G⟩` is the normal closure of `aⁿ`.
-/

/-- **Sozutov's question on involutions in quotients (Kourovka 18.94).** This is the statement
that whenever $G$ is a group without involutions (if $g^2 = 1$ then $g = 1$), $a \in G$ is not the
square of any element of $G$, and $n$ is an odd natural number, the quotient of $G$ by the normal
closure of $a^n$ has no involutions: every element $y$ of the quotient with $y^2 = 1$ is $1$. -/
def involutionFreeQuotientByNonSquarePower : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, g ^ 2 = 1 → g = 1) → ∀ a : G, (¬ ∃ x : G, x ^ 2 = a) →
    ∀ n : ℕ, Odd n → ∀ y : G ⧸ Subgroup.normalClosure {a ^ n}, y ^ 2 = 1 → y = 1

/--
**Quotients by the normal closure of an odd power of a non-square can have involutions.** There
exist a group $G$ without involutions (if $g^2 = 1$ then $g = 1$), an element $a \in G$ that is
not the square of any element of $G$, and an odd natural number $n$ such that the quotient of $G$
by the normal closure of $a^n$ contains an involution, that is, an element $y \ne 1$ with
$y^2 = 1$. This answers Kourovka Problem 18.94 in the negative.

Besides an example of V. I. Trofimov, the group $G = \langle a, b \mid a^2 = b^2 \rangle$ with
$n = 1$ is an example: its quotient by the normal closure of $a$ has order $2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.94 (A. I.
Sozutov); resolution: V. I. Trofimov (example), as recorded in the Kourovka Archive, Problem 18.94,
Kourovka Archive, Problem 18.94: No, not always, by an example of V. I. Trofimov; another example: G
= ⟨a, b | a² = b²⟩ modulo ⟨a^G⟩ has order 2, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted involutionFreeQuotientByNonSquarePower_refuted :
    ¬ involutionFreeQuotientByNonSquarePower

end MathlibExt.GroupTheory.InvolutionFreeQuotientKourovka18Problem94Wanted
