/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized torsion in free products (Kourovka Notebook Problem 16.49)

Kourovka Notebook, Archive of Solved Problems, Problem 16.49 (V. M. Kopytov, N. Ya. Medvedev): is it
true that a free product of groups without generalized torsion is a group without generalized
torsion?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.CoprodI

@[expose] public section

namespace MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.49 (V. M.
Kopytov, N. Ya. Medvedev). UnsolvedMath record UM-00701241 (`KOU-16.49`), dataset
ulamai/UnsolvedMath v1.8.0.

Free products of arbitrary families of groups (`Monoid.CoprodI`), as in the problem and the
Archive's answer; Theorem 1.5 of the resolution is stated for finitely many factors. Generalized
torsion as in Problem 16.48 (`h ≠ 1` with a nonempty product of conjugates of `h` trivial).
-/

/-- **Generalized torsion element (Kourovka 16.49).** An element $h$ of a group $H$ is a generalized
torsion element when $h \ne 1$ and some nonempty product of conjugates of $h$ is trivial, that is,
$x_1^{-1} h x_1 \cdots x_k^{-1} h x_k = 1$ for some $k \ge 1$ and some $x_1, \dots, x_k \in H$. -/
def IsGeneralizedTorsion {H : Type*} [Group H] (h : H) : Prop :=
  h ≠ 1 ∧ ∃ l : List H, l ≠ [] ∧ (l.map fun x => x⁻¹ * h * x).prod = 1

/-- **Kopytov–Medvedev question on generalized torsion in free products (Kourovka 16.49).** The
statement that for every family of groups $(G_i)_{i \in I}$ none of which contains a generalized
torsion element (an element $h \ne 1$ such that some nonempty product of conjugates of $h$ is
trivial), the free product of the family contains no generalized torsion element either. -/
def freeProductNoGeneralizedTorsion : Prop :=
  ∀ (ι : Type) (G : ι → Type) [∀ i, Group (G i)],
    (∀ i, ∀ g : G i, ¬ IsGeneralizedTorsion g) → ∀ g : Monoid.CoprodI G, ¬ IsGeneralizedTorsion g

/--
**Free products of groups without generalized torsion have no generalized torsion.** For every
family of groups $(G_i)_{i \in I}$ none of which contains a generalized torsion element (an element
$h \ne 1$ such that some nonempty product of conjugates of $h$ is trivial), the free product of the
family contains no generalized torsion element.

The Kourovka Archive answers 16.49 "Yes, it is true", citing Ito, Motegi and Teragaito (2019),
whose Theorem 1.5 shows that a generalized torsion element of a free product
$G_1 \ast \cdots \ast G_n$ of torsion-free groups is conjugate to a generalized torsion element of
some factor.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.49 (V. M. Kopytov, N.
Ya. Medvedev); resolution: T. Ito, K. Motegi and M. Teragaito, Generalized torsion and decomposition
of 3-manifolds, Proc. Amer. Math. Soc. 147 (2019), no. 11, 4999-5008, arXiv:1811.07532, Theorem 1.5
(a generalized torsion element of a free product G_1 ∗ ⋯ ∗ G_n of torsion-free groups is conjugate
to a generalized torsion element of some factor); Kourovka Archive, Problem 16.49 (Yes; moreover the
generalized torsion in a free product of torsion-free groups is conjugate to a generalized torsion
of one of its factor groups), https://arxiv.org/abs/1811.07532.
-/
public theorem_wanted freeProductNoGeneralizedTorsion_holds : freeProductNoGeneralizedTorsion

end MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49Wanted
