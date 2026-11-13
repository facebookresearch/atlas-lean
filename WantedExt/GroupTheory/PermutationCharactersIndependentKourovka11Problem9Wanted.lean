/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear independence of permutation characters (Kourovka Notebook Problem 11.9)

Kourovka Notebook, Problem 11.9 (I. I. Pyatetskiĭ-Shapiro; Ya. G. Berkovich): does there exist a
finite non-soluble group `G` such that the characters induced by the trivial characters of
representatives of all conjugacy classes of subgroups of `G` are linearly independent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.9 (Ya. G. Berkovich). UnsolvedMath
record UM-00700702 (`KOU-11.9`), dataset ulamai/UnsolvedMath v1.8.0.

The induced character `1_H^G` is the permutation character of `G` on the left cosets of `H`, `g ↦
#{xH : g x H = x H}`, as a `ℚ`-valued function (linear independence of integer-valued functions over
`ℚ` and over `ℂ` agree). The family is indexed by the conjugacy classes of subgroups (orbits of
`ConjAct G` on `Subgroup G`), choosing a representative of each.
-/

/-- **Rational permutation character on the cosets of a subgroup.** For a subgroup $H$ of a group
$G$, the permutation character $1_H^G : G \to \mathbb{Q}$ sends $g \in G$ to the number of left
cosets $xH$ of $H$ with $gxH = xH$, and to $0$ when $g$ fixes infinitely many cosets. -/
noncomputable def permChar {G : Type*} [Group G] (H : Subgroup G) (g : G) : ℚ :=
  Nat.card {c : G ⧸ H // g • c = c}

open scoped Pointwise in
/-- **Finite insoluble groups with independent permutation characters (Kourovka 11.9).**
The assertion that there is a finite non-soluble group $G$ such that, choosing a representative
$H$ of each conjugacy class of subgroups of $G$, the rational-valued permutation characters
$1_H^G$ of $G$ on the left cosets of these subgroups $H$ are linearly independent over
$\mathbb{Q}$. -/
def insolubleIndependentPermutationCharacters : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ Group.IsSolvable G ∧
    LinearIndependent ℚ fun c : MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G) =>
      permChar (Quotient.out c)

/-- **No insoluble group has independent permutation characters (Kourovka 11.9).** There is no
finite non-soluble group $G$ such that, choosing a representative $H$ of each conjugacy class of
subgroups of $G$, the rational-valued permutation characters $1_H^G$ of $G$ on the left cosets of
these subgroups $H$ are linearly independent over $\mathbb{Q}$.

Brescia, Ingrosso and Trombetti prove that these permutation characters are linearly independent
if and only if $G$ is cyclic; the Kourovka Notebook (21st issue) marks 11.9 solved, "No, there
are no such groups".

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 11.9 (Ya. G. Berkovich); resolution: M. Brescia, E. Ingrosso and M. Trombetti, On the
independence of permutation characters, arXiv:2608.16957 (2026), main theorem: the characters `π_H`,
`H` over representatives of the conjugacy classes of subgroups, are linearly independent iff `G` is
cyclic; the Kourovka Notebook (21st issue) marks 11.9 solved, https://arxiv.org/abs/2608.16957.
-/
public theorem_wanted insolubleIndependentPermutationCharacters_refuted :
    ¬ insolubleIndependentPermutationCharacters

end MathlibExt.GroupTheory.PermutationCharactersIndependentKourovka11Problem9Wanted
