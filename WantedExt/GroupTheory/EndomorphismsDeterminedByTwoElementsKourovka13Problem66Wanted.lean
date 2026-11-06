/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Endomorphisms determined by their values at two elements (Kourovka Notebook Problem 13.66)

Kourovka Notebook, Archive of Solved Problems, Problem 13.66 (V. E. Shpil'rain): let `F` be a (a)
free, (b) free metabelian group of finite rank, and `M` the set of endomorphisms of `F` with
non-cyclic images. Can one choose `g, h ∈ F` such that `φ, ψ ∈ M`, `φ(g) = ψ(g)` and `φ(h) = ψ(h)`
imply `φ = ψ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.66 (V. E.
Shpil'rain). UnsolvedMath record UM-00700984 (`KOU-13.66`), dataset ulamai/UnsolvedMath v1.8.0.

Ranks `n` are arbitrary finite; for `n ≤ 1` every image is cyclic, so (a) is vacuous there. (a) is
stated for every rank; (b) is stated for every rank and refuted, which says that for some finite
rank no such pair exists ("not always"). The free metabelian group of rank `n` is `F_n / F_n''`.
-/

/-- **The free metabelian group $M_n$.** For a natural number $n$, the free metabelian group of
rank $n$ is the quotient $F_n / F_n''$ of the free group $F_n$ on $n$ generators by its second
derived subgroup $F_n'' = [F_n', F_n']$, where $F_n' = [F_n, F_n]$ is the derived subgroup of
$F_n$. -/
abbrev FreeMetabelianGroup (n : ℕ) : Type :=
  FreeGroup (Fin n) ⧸ derivedSeries (FreeGroup (Fin n)) 2

/-- **Groups whose endomorphisms with non-cyclic images are determined by two elements.** A group
$F$ has this property when there exist elements $g, h \in F$ such that any two endomorphisms
$\varphi, \psi$ of $F$ whose images are not cyclic subgroups and which satisfy
$\varphi(g) = \psi(g)$ and $\varphi(h) = \psi(h)$ are equal. -/
def DeterminedByTwoElements (F : Type) [Group F] : Prop :=
  ∃ g h : F, ∀ φ ψ : F →* F, ¬ IsCyclic φ.range → ¬ IsCyclic ψ.range → φ g = ψ g →
    φ h = ψ h → φ = ψ

/-- **Shpil'rain's two-element problem for free groups (Kourovka 13.66(a)).** For every natural
number $n$, the free group $F_n$ of rank $n$ contains two elements $g$ and $h$ such that any two
endomorphisms of $F_n$ whose images are not cyclic subgroups and which agree at $g$ and at $h$
are equal; that is, $F_n$ has its endomorphisms with non-cyclic images determined by two
elements. -/
def freeGroupEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeGroup (Fin n))

/-- **Shpil'rain's two-element problem for free metabelian groups (Kourovka 13.66(b)).** For every
natural number $n$, the free metabelian group $M_n = F_n / F_n''$ of rank $n$ (the quotient of the
free group $F_n$ of rank $n$ by its second derived subgroup) contains two elements $g$ and $h$
such that any two endomorphisms of $M_n$ whose images are not cyclic subgroups and which agree at
$g$ and at $h$ are equal. -/
def freeMetabelianEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeMetabelianGroup n)

/--
**Endomorphisms of free groups with non-cyclic images are determined by two elements.** For every
natural number $n$, the free group $F_n$ of rank $n$ contains two elements $g$ and $h$ such that
any two endomorphisms $\varphi, \psi$ of $F_n$ whose images are not cyclic subgroups and which
satisfy $\varphi(g) = \psi(g)$ and $\varphi(h) = \psi(h)$ are equal.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 13.66 (V. E. Shpil'rain); resolution: (a) D. Lee, J. Algebra 247 (2002), no. 2, 509-540; (b)
E. I. Timoshenko, Math. Notes 62 (1998), no. 5-6, 767-770, Kourovka Archive, Problem 13.66 (answers:
a) Yes, one can; b) No, not always).
-/
public theorem_wanted freeGroupEndomorphismsDeterminedByTwoElements_holds :
    freeGroupEndomorphismsDeterminedByTwoElements

/--
**Endomorphisms of free metabelian groups are not always determined by two elements.** For a
natural number $n$, let $M_n = F_n / F_n''$ be the free metabelian group of rank $n$, the quotient
of the free group $F_n$ of rank $n$ by its second derived subgroup. There is an $n$ such that for
all elements $g, h \in M_n$ there are endomorphisms $\varphi \ne \psi$ of $M_n$ whose images are
not cyclic subgroups and which satisfy $\varphi(g) = \psi(g)$ and $\varphi(h) = \psi(h)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 13.66 (V. E. Shpil'rain); resolution: (a) D. Lee, J. Algebra 247 (2002), no. 2,
509-540; (b) E. I. Timoshenko, Math. Notes 62 (1998), no. 5-6, 767-770, Kourovka Archive, Problem
13.66 (answers: a) Yes, one can; b) No, not always).
-/
public theorem_wanted freeMetabelianEndomorphismsDeterminedByTwoElements_refuted :
    ¬ freeMetabelianEndomorphismsDeterminedByTwoElements

end MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted
