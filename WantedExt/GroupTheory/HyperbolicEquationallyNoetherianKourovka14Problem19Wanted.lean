/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hyperbolic groups are equationally Noetherian (Kourovka Notebook Problem 14.19)

Kourovka Notebook, Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N. Remeslennikov): a group has
the Noetherian Equation Property if every system of equations over it in finitely many variables is
equivalent to some finite part of it. Does every hyperbolic group have it?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import MathlibExt.GroupTheory.HyperbolicGroup

@[expose] public section

namespace MathlibExt.GroupTheory.HyperbolicEquationallyNoetherianKourovka14Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov). UnsolvedMath record UM-00701004 (`KOU-14.19`), dataset ulamai/UnsolvedMath v1.8.0.

An equation over `G` in the unknowns `x₀, …, xₙ₋₁` is an element of `G ∗ F(x₀, …, xₙ₋₁)`
(`Monoid.Coprod`); its solutions are assignments `x : Fin n → G` at which it evaluates to `1`.
Equivalent systems have the same solution sets. Hyperbolic is `Group.IsHyperbolic` from `MathlibExt`
(some finite generating family has a Gromov-hyperbolic word metric).
-/

/-- **Evaluating an equation at an assignment.** Let $G$ be a group and $n$ a natural number. An
equation over $G$ in the unknowns $x_0, \dots, x_{n-1}$ is an element of the free product
$G * F(x_0, \dots, x_{n-1})$ of $G$ with the free group on $x_0, \dots, x_{n-1}$. For an assignment
$a = (a_0, \dots, a_{n-1}) \in G^n$, evaluation at $a$ is the group homomorphism
$G * F(x_0, \dots, x_{n-1}) \to G$ that is the identity on $G$ and sends each unknown $x_i$ to
$a_i$. -/
def evalEquation {G : Type*} [Group G] {n : ℕ} (x : Fin n → G) :
    Monoid.Coprod G (FreeGroup (Fin n)) →* G :=
  Monoid.Coprod.lift (MonoidHom.id G) (FreeGroup.lift x)

/-- **Solution set of a system of equations.** Let $G$ be a group, $n$ a natural number and $S$ a
set of equations over $G$ in the unknowns $x_0, \dots, x_{n-1}$, that is, a subset of the free
product $G * F(x_0, \dots, x_{n-1})$ of $G$ with the free group on $x_0, \dots, x_{n-1}$. The
solution set of $S$ is the set of assignments $a \in G^n$ at which every $w \in S$ evaluates to
$1$. -/
def solutions {G : Type*} [Group G] {n : ℕ} (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))) :
    Set (Fin n → G) :=
  {x | ∀ w ∈ S, evalEquation x w = 1}

/-- **The Noetherian Equation Property.** A group $G$ has the Noetherian Equation Property (is
equationally Noetherian) if for every natural number $n$ and every system $S$ of equations over $G$
in the unknowns $x_0, \dots, x_{n-1}$, that is, every subset $S$ of the free product
$G * F(x_0, \dots, x_{n-1})$ of $G$ with the free group on $x_0, \dots, x_{n-1}$, there is a
finite subset $S_0 \subseteq S$ whose solution set in $G^n$ equals the solution set of $S$. -/
def EquationallyNoetherian (G : Type*) [Group G] : Prop :=
  ∀ (n : ℕ) (S : Set (Monoid.Coprod G (FreeGroup (Fin n)))),
    ∃ S₀ ⊆ S, S₀.Finite ∧ solutions S₀ = solutions S

/-- **Kourovka Problem 14.19 (hyperbolic groups and the Noetherian Equation Property).** Every
word-hyperbolic group $G$ has the Noetherian Equation Property: for every natural number $n$, every
system of equations over $G$ in the unknowns $x_0, \dots, x_{n-1}$ has the same solution set in
$G^n$ as some finite subsystem.

The problem is due to G. Baumslag, A. G. Myasnikov and V. N. Remeslennikov. -/
def hyperbolicGroupEquationallyNoetherian : Prop :=
  ∀ (G : Type) [Group G], Group.IsHyperbolic G → EquationallyNoetherian G

/--
**Hyperbolic groups are equationally Noetherian.** Every word-hyperbolic group $G$ has the
Noetherian Equation Property: for every natural number $n$, every system of equations over $G$ in
the unknowns $x_0, \dots, x_{n-1}$ has the same solution set in $G^n$ as some finite subsystem.

This answers Kourovka Problem 14.19 ("Yes, it does"): Weidmann and Reinfeldt prove it for all
hyperbolic groups, and Sela had proved the torsion-free case.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.19 (G. Baumslag, A. G. Myasnikov, V. N.
Remeslennikov); resolution: R. Weidmann and C. Reinfeldt, Ann. Math. Blaise Pascal 26 (2019), no. 2,
125-214, the Kourovka Notebook (21st issue) marks 14.19 solved (Yes); the torsion-free case is due
to Z. Sela, Proc. London Math. Soc. 99 (2009), 217-273.
-/
public theorem_wanted hyperbolicGroupEquationallyNoetherian_holds :
    hyperbolicGroupEquationallyNoetherian

end MathlibExt.GroupTheory.HyperbolicEquationallyNoetherianKourovka14Problem19Wanted
