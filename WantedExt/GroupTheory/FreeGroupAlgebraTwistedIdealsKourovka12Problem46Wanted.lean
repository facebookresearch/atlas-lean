/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Twisted right ideals in the group algebra of a free group (Kourovka Notebook Problem 12.46)

Kourovka Notebook, Archive of Solved Problems, Problem 12.46 (P. A. Linnell): let `F` be free on `x,
y`, and for `|a| = |b| = 1` let `ϑ_{a,b}` be the automorphism of `ℂF` with `x ↦ a x`, `y ↦ b y`.
Given `0 ≠ α ∈ ℂF`, can we always find `a, b ∈ ℂ ∖ {1}` with `|a| = |b| = 1` such that `α ℂF ∩
ϑ_{a,b}(α) ℂF ≠ 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A.
Linnell). UnsolvedMath record UM-00700865 (`KOU-12.46`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂF` is `MonoidAlgebra ℂ F`; `ϑ_{a,b}` multiplies the coefficient of `g` by `χ(g)`, where `χ` is the
character with `χ(x) = a`, `χ(y) = b`, which is the algebra automorphism with `x ↦ a x`, `y ↦ b y`.
A nonzero element of `α ℂF ∩ ϑ_{a,b}(α) ℂF` is written `α β = ϑ_{a,b}(α) γ ≠ 0`; `a, b` are units of
absolute value 1 different from 1.
-/

/-- **Twisting character of the free group of rank two.** Let $F$ be the free group on $x, y$. For
nonzero complex numbers $a, b$, this is the homomorphism $\chi \colon F \to \mathbb{C}^\times$ with
$\chi(x) = a$ and $\chi(y) = b$. -/
noncomputable def twistCharacter (a b : ℂˣ) : FreeGroup (Fin 2) →* ℂˣ :=
  FreeGroup.lift ![a, b]

/-- **Twisting automorphism of the free group algebra.** Let $F$ be the free group on $x, y$, let
$\mathbb{C}F$ be its complex group algebra, and for nonzero complex numbers $a, b$ let $\chi$ be the
character of $F$ with $\chi(x) = a$ and $\chi(y) = b$. The map $\vartheta_{a,b}$ sends
$\alpha = \sum_{g \in F} c_g\, g \in \mathbb{C}F$ to $\sum_{g \in F} \chi(g)\, c_g\, g$.

Since $\chi$ is a homomorphism, $\vartheta_{a,b}$ is the algebra automorphism of $\mathbb{C}F$ with
$\vartheta_{a,b}(x) = a x$ and $\vartheta_{a,b}(y) = b y$. -/
noncomputable def theta (a b : ℂˣ) (α : MonoidAlgebra ℂ (FreeGroup (Fin 2))) :
    MonoidAlgebra ℂ (FreeGroup (Fin 2)) :=
  α.coeff.sum fun g c => MonoidAlgebra.single g ((twistCharacter a b g : ℂ) * c)

/-- **Linnell's twisted right ideal question (Kourovka 12.46).** Let $F$ be the free group on
$x, y$, let $\mathbb{C}F$ be its complex group algebra, and for nonzero complex numbers $a, b$ let
$\vartheta_{a,b}$ be the twisting automorphism of $\mathbb{C}F$ with $\vartheta_{a,b}(x) = a x$ and
$\vartheta_{a,b}(y) = b y$. The assertion is that for every nonzero $\alpha \in \mathbb{C}F$ there
are complex numbers $a, b \neq 1$ with $|a| = |b| = 1$ such that the right ideals
$\alpha\,\mathbb{C}F$ and $\vartheta_{a,b}(\alpha)\,\mathbb{C}F$ intersect nontrivially, that is,
$\alpha\beta = \vartheta_{a,b}(\alpha)\gamma \neq 0$ for some $\beta, \gamma \in \mathbb{C}F$. -/
def twistedRightIdealsIntersect : Prop :=
  ∀ α : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α ≠ 0 →
    ∃ a b : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ ‖(b : ℂ)‖ = 1 ∧ (a : ℂ) ≠ 1 ∧ (b : ℂ) ≠ 1 ∧
      ∃ β γ : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α * β = theta a b α * γ ∧ α * β ≠ 0

/--
**Linnell's twisted right ideal question has a negative answer (Kourovka 12.46).** Let $F$ be the
free group on $x, y$, let $\mathbb{C}F$ be its complex group algebra, and for nonzero complex
numbers $a, b$ let $\vartheta_{a,b}$ be the twisting automorphism of $\mathbb{C}F$ with
$\vartheta_{a,b}(x) = a x$ and $\vartheta_{a,b}(y) = b y$. There is a nonzero
$\alpha \in \mathbb{C}F$ such that for all complex numbers $a, b \neq 1$ with $|a| = |b| = 1$
the right ideals $\alpha\,\mathbb{C}F$ and $\vartheta_{a,b}(\alpha)\,\mathbb{C}F$ intersect only in
$0$: whenever $\beta, \gamma \in \mathbb{C}F$ satisfy $\alpha\beta = \vartheta_{a,b}(\alpha)\gamma$,
then $\alpha\beta = 0$.

The Kourovka Archive answers 12.46 "No, not always" (A. V. Tushev, 1995).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A.
Linnell); resolution: A. V. Tushev, Ukrain. Mat. Zh. 47 (1995), no. 4, 571-572, Kourovka Archive,
Problem 12.46: No, not always.
-/
public theorem_wanted twistedRightIdealsIntersect_refuted : ¬ twistedRightIdealsIntersect

end MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted
