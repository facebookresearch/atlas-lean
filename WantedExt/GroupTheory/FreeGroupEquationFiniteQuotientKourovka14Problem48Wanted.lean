/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equations over free groups and finite quotients (Kourovka Notebook Problem 14.48)

Kourovka Notebook, Archive of Solved Problems, Problem 14.48 (L. Comerford): if an equation over a
free group `F` has no solution in `F`, is there a finite quotient of `F` in which it has no
solution?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.48 (L.
Comerford). UnsolvedMath record UM-00701033 (`KOU-14.48`), dataset ulamai/UnsolvedMath v1.8.0.

An equation over `F` is an element `w` of `F ∗ F(x₀, …, xₙ₋₁)` (any number of unknowns); in the
quotient `F / N` its coefficients are mapped to `F / N`. Finite quotients are `F / N` with `N`
normal of finite index; `F` is free of any rank.
-/

/-- **Kourovka Problem 14.48 (equations over free groups in finite quotients).** The statement
that for every free group $F$ on an arbitrary set of generators, every natural number $n$ and every
equation $w$ over $F$ in the unknowns $x_0, \dots, x_{n-1}$ (an element of the free product of $F$
with the free group on $x_0, \dots, x_{n-1}$): if no $g_0, \dots, g_{n-1} \in F$ are such that
substituting $g_i$ for $x_i$ sends $w$ to $1$, then there is a normal subgroup $N$ of finite index
in $F$ such that no $h_0, \dots, h_{n-1} \in F / N$ are such that substituting $h_i$ for $x_i$ and
mapping the coefficients of $w$ to their images in $F / N$ sends $w$ to $1$. -/
def unsolvableEquationUnsolvableInFiniteQuotient : Prop :=
  ∀ (α : Type) (n : ℕ) (w : Monoid.Coprod (FreeGroup α) (FreeGroup (Fin n))),
    (∀ x : Fin n → FreeGroup α, Monoid.Coprod.lift (MonoidHom.id _) (FreeGroup.lift x) w ≠ 1) →
    ∃ (N : Subgroup (FreeGroup α)) (_ : N.Normal), N.FiniteIndex ∧
      ∀ x : Fin n → FreeGroup α ⧸ N,
        Monoid.Coprod.lift (QuotientGroup.mk' N) (FreeGroup.lift x) w ≠ 1

/--
**An unsolvable equation over a free group that is solvable in every finite quotient.** There are
a free group $F$ on some set of generators, a natural number $n$ and an equation $w$ over $F$ in
the unknowns $x_0, \dots, x_{n-1}$, that is, an element $w$ of the free product of $F$ with the
free group on $x_0, \dots, x_{n-1}$, such that no $g_0, \dots, g_{n-1} \in F$ satisfy the equation
(substituting $g_i$ for $x_i$ never sends $w$ to $1$), but for every normal subgroup $N$ of finite
index in $F$ there are $h_0, \dots, h_{n-1} \in F / N$ such that substituting $h_i$ for $x_i$ and
mapping the coefficients of $w$ to their images in $F / N$ sends $w$ to $1$.

Resolved false: the Kourovka Archive answers 14.48 "No, not always", citing Coulbois and Khelif:
some equation over a free group has no solution in it but has a solution in every finite quotient.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.48 (L.
Comerford); resolution: T. Coulbois and A. Khelif, Proc. Amer. Math. Soc. 127 (1999), no. 4,
963-965, Kourovka Archive, Problem 14.48 (answer: No, not always).
-/
public theorem_wanted unsolvableEquationUnsolvableInFiniteQuotient_refuted :
    ¬ unsolvableEquationUnsolvableInFiniteQuotient

end MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48Wanted
