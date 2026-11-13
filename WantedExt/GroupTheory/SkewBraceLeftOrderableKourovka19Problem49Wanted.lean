/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Skew braces with left-orderable multiplicative group (Kourovka Notebook Problem 19.49)

Kourovka Notebook, Archive of Solved Problems, Problem 19.49 (V. Lebed, L. Vendramin): a skew brace
is a set `B` with two group operations `+` (not necessarily abelian) and `·` such that `a (b + c) =
a b - a + a c`. Let `A` be a skew brace with left-orderable multiplicative group. Is the additive
group of `A` left-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.49 (V.
Lebed, L. Vendramin). UnsolvedMath record UM-00701597 (`KOU-19.49`), dataset ulamai/UnsolvedMath
v1.8.0.

A skew brace is a type `B` with an `AddGroup` and a `Group` structure satisfying `a * (b + c) = a *
b - a + a * c`, where `x - y = x + (-y)`. A group is left-orderable when some strict total order is
invariant under left multiplication (left addition for `+`).
-/

/-- **Left-orderable multiplication.** The multiplication of a set $B$ is left-orderable when there
is a strict total order $<$ on $B$ that is invariant under left multiplication: for all
$a, b, c \in B$, if $b < c$ then $a b < a c$. -/
def LeftOrderableMul (B : Type*) [Mul B] : Prop :=
  ∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a * b) (a * c)

/-- **Left-orderable addition.** The addition of a set $B$ is left-orderable when there is a strict
total order $<$ on $B$ that is invariant under left addition: for all $a, b, c \in B$, if $b < c$
then $a + b < a + c$. -/
def LeftOrderableAdd (B : Type*) [Add B] : Prop :=
  ∃ r : B → B → Prop, IsStrictTotalOrder B r ∧ ∀ a b c : B, r b c → r (a + b) (a + c)

/-- **Left-orderability of the additive group of a skew brace (Kourovka 19.49).** The statement
that for every skew brace $B$, that is, a set with two group structures, an addition $+$ (not
necessarily commutative) and a multiplication $\cdot$, satisfying
$a \cdot (b + c) = a \cdot b - a + a \cdot c$ for all $a, b, c \in B$: if the multiplication of
$B$ is left-orderable, then the addition of $B$ is left-orderable. -/
def skewBraceAdditiveLeftOrderable : Prop :=
  ∀ (B : Type) [AddGroup B] [Group B], (∀ a b c : B, a * (b + c) = a * b - a + a * c) →
    LeftOrderableMul B → LeftOrderableAdd B

/--
**A skew brace whose additive group is not left-orderable.** There is a skew brace $B$, that is, a
set with two group structures, an addition $+$ and a multiplication $\cdot$, satisfying
$a \cdot (b + c) = a \cdot b - a + a \cdot c$ for all $a, b, c \in B$, whose multiplication is
left-orderable but whose addition is not left-orderable. That is, the statement of Kourovka
Problem 19.49 fails.

Nasybullov's example (Example 3.1) is $\mathbb{Z}$ with addition $a \oplus b = a + (-1)^a b$ and
multiplication $a \odot b = a + b$: the multiplicative group is infinite cyclic, hence
left-orderable, while the additive group is infinite dihedral and has an element of order $2$, so
it is not left-orderable. The Kourovka Archive answers 19.49 "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 19.49 (V. Lebed, L. Vendramin); resolution: T. Nasybullov, Connections between
properties of the additive and the multiplicative groups of a two-sided skew brace, J. Algebra 540
(2019), 156-167 (arXiv:1809.09418), Example 3.1: on ℤ, a ⊕ b = a + (−1)^a b and a ⊙ b = a + b define
a skew brace with infinite cyclic multiplicative group and infinite dihedral additive group, which
has 2-torsion and so is not left-orderable, answering Problem 19.49; Kourovka Archive, Problem
19.49: No, not always, https://arxiv.org/abs/1809.09418.
-/
public theorem_wanted skewBraceAdditiveLeftOrderable_refuted : ¬ skewBraceAdditiveLeftOrderable

end MathlibExt.GroupTheory.SkewBraceLeftOrderableKourovka19Problem49Wanted
