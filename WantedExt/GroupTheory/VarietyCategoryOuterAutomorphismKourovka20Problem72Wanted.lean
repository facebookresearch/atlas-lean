/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Outer automorphisms of the category of free groups of a variety (Kourovka Notebook Problem 20.72)

Kourovka Notebook, Problem 20.72 (E. Plotkin), marked solved in the 21st issue: is there a variety
of groups `Θ` such that the group of automorphisms of the category of free finitely generated groups
`Θ⁰` contains outer automorphisms?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.72 (E. Plotkin). UnsolvedMath record
UM-00701730 (`KOU-20.72`), dataset ulamai/UnsolvedMath v1.8.0.

A variety is given by a set `W` of laws in `x₀, x₁, …` (Birkhoff). Following Plotkin's setting as in
the resolving paper, `Θ⁰` has as objects the free groups `F_Θ(X)` of the variety for the finite
subsets `X` of a countable set `X⁰ = ℕ` and as morphisms all homomorphisms; `F_Θ(X)` is `FreeGroup
X` modulo its verbal subgroup. An automorphism of `Θ⁰` is a functor with a two-sided inverse
functor; it is inner when it is isomorphic to the identity functor (Definition 1.3 of the resolving
paper), and outer automorphisms exist exactly when some automorphism is not inner.
-/

open CategoryTheory

/-- **Free group of a variety on a finite set.** Let $W$ be a set of words in the free group
$F(\mathbb{N})$ on $x_0, x_1, \ldots$, defining a variety $\Theta$, and let $X \subseteq \mathbb{N}$
be finite. The free group $F_\Theta(X)$ of $\Theta$ on $X$ is the quotient of the free group $F(X)$
on $X$ by its verbal subgroup, the normal closure of the set of values $\varphi(w)$ with $w \in W$
and $\varphi \colon F(\mathbb{N}) \to F(X)$ a homomorphism. This set of values is closed under
conjugation, so the verbal subgroup is also the subgroup it generates. -/
abbrev relativelyFreeGroup (W : Set (FreeGroup ℕ)) (X : Finset ℕ) : Type :=
  FreeGroup X ⧸ Subgroup.normalClosure {g | ∃ w ∈ W, ∃ φ : FreeGroup ℕ →* FreeGroup X, φ w = g}

/-- **Plotkin's category of free groups of a variety.** Let $W$ be a set of words in the free group
on $x_0, x_1, \ldots$, defining a variety $\Theta$. The category $\Theta^0$ has one object for each
finite subset $X$ of $X^0 = \mathbb{N}$, namely the free group $F_\Theta(X)$ of $\Theta$ on $X$, and
its morphisms are all group homomorphisms between these groups. -/
abbrev ThetaZero (W : Set (FreeGroup ℕ)) : Type :=
  InducedCategory GrpCat fun X : Finset ℕ => GrpCat.of (relativelyFreeGroup W X)

/-- **Plotkin's question on outer automorphisms of the category of free groups of a variety.** The
statement that there is a set $W$ of words in the free group on $x_0, x_1, \ldots$ such that, for
the variety $\Theta$ with laws $W$, the category $\Theta^0$ of the free groups of $\Theta$ on the
finite subsets of $\mathbb{N}$ has an automorphism that is not inner: functors
$\Phi, \Psi \colon \Theta^0 \to \Theta^0$ whose composites $\Psi \circ \Phi$ and $\Phi \circ \Psi$
both equal the identity functor, with $\Phi$ not naturally isomorphic to the identity functor.
This is Kourovka Notebook Problem 20.72 (E. Plotkin). -/
def existsVarietyWithNonInnerCategoryAutomorphism : Prop :=
  ∃ (W : Set (FreeGroup ℕ)) (Φ Ψ : ThetaZero W ⥤ ThetaZero W),
    Φ ⋙ Ψ = 𝟭 _ ∧ Ψ ⋙ Φ = 𝟭 _ ∧ IsEmpty (Φ ≅ 𝟭 _)

/--
**Some variety of groups has an outer automorphism of its category of free groups.** There is a
set $W$ of words in the free group on $x_0, x_1, \ldots$ such that, for the variety $\Theta$ with
laws $W$, the category $\Theta^0$, whose objects are the free groups $F_\Theta(X)$ of $\Theta$ on
the finite subsets $X \subseteq \mathbb{N}$ and whose morphisms are all group homomorphisms, has an
automorphism that is not inner: there are functors $\Phi, \Psi \colon \Theta^0 \to \Theta^0$ whose
composites $\Psi \circ \Phi$ and $\Phi \circ \Psi$ both equal the identity functor, and $\Phi$ is
not naturally isomorphic to the identity functor.

Barbosa Fernandes and Tsurkov (Theorem 9.1) show that for the variety of metabelian groups of
exponent $4$ and nilpotency class at most $4$ (laws $x^4 = 1$, $((x_1, x_2), (x_3, x_4)) = 1$ and
$((((x_1, x_2), x_3), x_4), x_5) = 1$) the group of automorphisms of $\Theta^0$ modulo the inner
ones has order $2$. The 21st issue of the Kourovka Notebook marks 20.72 solved ("Yes, there is").

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 20.72 (E. Plotkin); resolution: R. Barbosa Fernandes and
A. Tsurkov, Automorphisms of the category of finitely generated free groups of the some subvariety
of the variety of all groups, preprint, arXiv:1909.05955 (2019), Theorem 9.1: for the variety Θ
defined by x⁴ = 1, ((x₁, x₂), (x₃, x₄)) = 1 and ((((x₁, x₂), x₃), x₄), x₅) = 1, the quotient A/Y of
the automorphism group of Θ⁰ by the inner automorphisms has order 2; Kourovka Notebook (21st issue),
Problem 20.72: Yes, there is, https://arxiv.org/abs/1909.05955.
-/
public theorem_wanted existsVarietyWithNonInnerCategoryAutomorphism_holds :
    existsVarietyWithNonInnerCategoryAutomorphism

end MathlibExt.GroupTheory.VarietyCategoryOuterAutomorphismKourovka20Problem72Wanted
