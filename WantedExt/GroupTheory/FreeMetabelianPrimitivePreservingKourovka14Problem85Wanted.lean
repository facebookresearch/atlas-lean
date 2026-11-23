/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Primitive-preserving endomorphisms of free metabelian groups (Kourovka Notebook Problem 14.85)

Kourovka Notebook, Problem 14.85 (E. I. Timoshenko, V. Shpilrain): if an endomorphism `φ` of a free
metabelian group of rank `r` takes every primitive element to a primitive one, is `φ` necessarily an
automorphism?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.FreeMetabelianPrimitivePreservingKourovka14Problem85Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.85 (E. I. Timoshenko, V. Shpilrain).
UnsolvedMath record UM-00701070 (`KOU-14.85`), dataset ulamai/UnsolvedMath v1.8.0.

`M_n = F_n / F_n''`. A primitive element belongs to a free basis of `M_n`, i.e. it is the image of a
basis element `xᵢ` under an automorphism of `M_n`. Stated for every rank `n` (the problem notes that
ranks at most `2` were known).
-/

/-- **Free metabelian group $M_n$ (Kourovka 14.85).** For a natural number $n$, the free metabelian
group $M_n = F_n / F_n''$ of rank $n$: the quotient of the free group $F_n$ on $n$ generators by
its second derived subgroup $F_n'' = [[F_n, F_n], [F_n, F_n]]$. -/
abbrev FreeMetabelianGroup (n : ℕ) : Type :=
  FreeGroup (Fin n) ⧸ derivedSeries (FreeGroup (Fin n)) 2

/-- **Primitive elements of the free metabelian group.** Let $F_n$ be the free group on $n$
generators, let $F_n''$ be its second derived subgroup, and let $M_n = F_n / F_n''$ be the free
metabelian group of rank $n$. Let $x_0, \dots, x_{n-1}$ be the images in $M_n$ of the free
generators of $F_n$. An element $y$ of $M_n$ is primitive when $y = \sigma(x_i)$ for some
automorphism $\sigma$ of $M_n$ and some index $i$; that is, $y$ is the image of a standard basis
element under an automorphism of $M_n$. -/
def IsPrimitive {n : ℕ} (y : FreeMetabelianGroup n) : Prop :=
  ∃ (σ : FreeMetabelianGroup n ≃* FreeMetabelianGroup n) (i : Fin n),
    σ (QuotientGroup.mk (FreeGroup.of i)) = y

/-- **Primitive-preserving endomorphism problem for free metabelian groups (Kourovka 14.85).**
The statement, posed by E. I. Timoshenko and V. Shpilrain, that for every natural number $n$,
every endomorphism $\varphi$ of the free metabelian group $M_n$ of rank $n$ that maps every
primitive element of $M_n$ to a primitive element is bijective, hence an automorphism. -/
def primitivePreservingEndomorphismIsAutomorphism : Prop :=
  ∀ (n : ℕ) (φ : FreeMetabelianGroup n →* FreeMetabelianGroup n),
    (∀ y, IsPrimitive y → IsPrimitive (φ y)) → Function.Bijective φ

/--
**Primitive-preserving endomorphisms of free metabelian groups are automorphisms.** For every
natural number $n$, every endomorphism $\varphi$ of the free metabelian group $M_n$ of rank $n$
that maps every primitive element of $M_n$ to a primitive element is bijective, hence an
automorphism of $M_n$. This answers Kourovka Problem 14.85 positively.

Ionin and Semidetnov (Section 1, Answer 1.2) prove that every primitive-preserving endomorphism of
the free metabelian group $M_n$ is an automorphism; the Kourovka Notebook (21st issue) answers
Problem 14.85 "Yes, it is".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.85 (E. I.
Timoshenko, V. Shpilrain); resolution: V. Ionin and A. Semidetnov, On some more problems from the
Kourovka Notebook, preprint, arXiv:2608.29219 (2026), Section 1, Answer 1.2: every
primitive-preserving endomorphism of M_n is an automorphism (the abstract states that the solutions
were found with the assistance of large language models and checked by the authors); the Kourovka
Notebook (21st issue) marks 14.85 solved (Yes, it is), https://arxiv.org/abs/2608.29219.
-/
public theorem_wanted primitivePreservingEndomorphismIsAutomorphism_holds :
    primitivePreservingEndomorphismIsAutomorphism

end MathlibExt.GroupTheory.FreeMetabelianPrimitivePreservingKourovka14Problem85Wanted
