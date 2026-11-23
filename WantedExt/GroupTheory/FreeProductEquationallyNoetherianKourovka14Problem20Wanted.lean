/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free products of equationally Noetherian groups (Kourovka Notebook Problem 14.20)

Kourovka Notebook, Problem 14.20 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): does a free
product of two groups have the Noetherian Equation Property if both factors have it?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeProductEquationallyNoetherianKourovka14Problem20Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.20 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov). UnsolvedMath record UM-00701005 (`KOU-14.20`), dataset ulamai/UnsolvedMath v1.8.0.

Equations and the Noetherian Equation Property as in
`HyperbolicEquationallyNoetherianKourovka14Problem19Wanted`; the free product is `Monoid.Coprod G
H`. The problem concerns two factors; free products of infinitely many equationally Noetherian
groups can fail (Groves-Hull).
-/

/-- **Evaluation of an equation at an assignment (Kourovka 14.20).** For a group $G$, let $F_n$ be
the free group on the unknowns $t_0, \dots, t_{n-1}$. For an assignment
$x = (x_0, \dots, x_{n-1}) \in G^n$, evaluation at $x$ is the group homomorphism $G * F_n \to G$
from the free product of $G$ and $F_n$ that is the identity on $G$ and sends $t_i$ to $x_i$ for
each $i < n$; it sends an equation $w \in G * F_n$ over $G$ to its value $w(x)$ at $x$. -/
def evalEquation {G : Type*} [Group G] {n : ℕ} (x : Fin n → G) :
    Monoid.Coprod G (FreeGroup (Fin n)) →* G :=
  Monoid.Coprod.lift (MonoidHom.id G) (FreeGroup.lift x)

/-- **Solution set of a system of equations (Kourovka 14.20).** For a group $G$, let $F_n$ be the
free group on the unknowns $t_0, \dots, t_{n-1}$. The solution set of a set $S \subseteq G * F_n$
of equations over $G$ is the set of assignments $x = (x_0, \dots, x_{n-1}) \in G^n$ such that
$w(x) = 1$ for every $w \in S$, where $w(x)$ is the image of $w$ under the homomorphism
$G * F_n \to G$ that is the identity on $G$ and sends $t_i$ to $x_i$. -/
def solutions {G : Type*} [Group G] {n : ℕ} (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))) :
    Set (Fin n → G) :=
  {x | ∀ w ∈ S, evalEquation x w = 1}

/-- **Equationally Noetherian groups (Kourovka 14.20).** A group $G$ is equationally Noetherian
(has the Noetherian Equation Property) if for every $n \in \mathbb{N}$ and every set $S$ of
equations over $G$ in the unknowns $t_0, \dots, t_{n-1}$, that is, every subset $S$ of the free
product $G * F_n$ of $G$ with the free group $F_n$ on $t_0, \dots, t_{n-1}$, there is a finite
subset $S_0 \subseteq S$ with the same solution set as $S$. Here the solution set of a set of
equations is the set of assignments $x = (x_0, \dots, x_{n-1}) \in G^n$ at which every equation in
it evaluates to $1$. -/
def EquationallyNoetherian (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))),
    ∃ S₀ ⊆ S, S₀.Finite ∧ solutions S₀ = solutions S

/-- **Kourovka Problem 14.20 (free products of equationally Noetherian groups).** The statement
that for all groups $G$ and $H$, if $G$ and $H$ are equationally Noetherian (have the Noetherian
Equation Property), then their free product $G * H$ is equationally Noetherian.

Kourovka Notebook Problem 14.20 is due to G. Baumslag, A. G. Myasnikov and V. N. Remeslennikov. -/
def freeProductEquationallyNoetherian : Prop :=
  ∀ (G H : Type) [Group G] [Group H], EquationallyNoetherian G → EquationallyNoetherian H →
    EquationallyNoetherian (Monoid.Coprod G H)

/--
Resolved true: the Kourovka Notebook (21st issue) answers 14.20 "Yes, it does", citing Sela's
preprint (Theorem 9.1): the free product of two equationally Noetherian groups is equationally
Noetherian. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.20 (G. Baumslag, A. G.
Myasnikov, V. N. Remeslennikov); resolution: Z. Sela, Diophantine geometry over groups X: The
elementary theory of free products of groups, preprint, arXiv:1012.0044 (2010), Section 9, Theorem
9.1: the free product of two equationally Noetherian groups is equationally Noetherian; the Kourovka
Notebook (21st issue) marks 14.20 solved (Yes, it does), citing this preprint,
https://arxiv.org/abs/1012.0044.
-/
public theorem_wanted freeProductEquationallyNoetherian_holds : freeProductEquationallyNoetherian

end MathlibExt.GroupTheory.FreeProductEquationallyNoetherianKourovka14Problem20Wanted
