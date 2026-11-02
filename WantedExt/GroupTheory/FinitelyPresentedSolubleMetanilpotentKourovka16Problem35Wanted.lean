/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Metanilpotent-by-finite finitely presented soluble groups (Kourovka Notebook Problem 16.35)

Kourovka Notebook, Archive of Solved Problems, Problem 16.35 (J. R. J. Groves): is every finitely
presented soluble group nilpotent-by-nilpotent-by-finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.35 (J. R. J.
Groves). UnsolvedMath record UM-00701227 (`KOU-16.35`), dataset ulamai/UnsolvedMath v1.8.0.

(Nilpotent-by-nilpotent)-by-finite: some normal subgroup `M` of finite index has a normal nilpotent
subgroup `N` with `M / N` nilpotent (the reading nilpotent-by-(nilpotent-by-finite) is equivalent,
by Fitting's theorem). Finitely presented is `Group.IsFinitelyPresented` and soluble is
`Group.IsSolvable`.
-/

/-- **Metanilpotent-by-finite groups.** A group $G$ is (nilpotent-by-nilpotent)-by-finite when it
has a normal subgroup $M$ of finite index and a normal subgroup $N$ of $M$ such that $N$ and $M/N$
are both nilpotent. -/
def IsMetanilpotentByFinite (G : Type) [Group G] : Prop :=
  ∃ M : Subgroup G, M.Normal ∧ M.FiniteIndex ∧
    ∃ N : Subgroup M, ∃ _ : N.Normal, Group.IsNilpotent N ∧ Group.IsNilpotent (M ⧸ N)

/-- **Groves's question (Kourovka 16.35).** The proposition that every finitely presented soluble
group $G$ is (nilpotent-by-nilpotent)-by-finite, that is, $G$ has a normal subgroup $M$ of finite
index and a normal subgroup $N$ of $M$ such that $N$ and $M/N$ are both nilpotent. -/
def finitelyPresentedSolubleMetanilpotentByFinite : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G → Group.IsSolvable G →
    IsMetanilpotentByFinite G

/--
**Groves's question (Kourovka 16.35) has a negative answer.** Not every finitely presented
soluble group is (nilpotent-by-nilpotent)-by-finite: there is a finitely presented soluble group
$G$ such that for no normal subgroup $M$ of finite index in $G$ is there a normal subgroup $N$ of
$M$ with $N$ and $M/N$ both nilpotent.

Source: E. I. Khukhro and
V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.35 (J. R. J. Groves); resolution:
V. V. Bludov, letter of 27 April 2007, as recorded in the Kourovka Archive, Kourovka Archive,
Problem 16.35 (No: for a prime p, ⟨a, b, c, d | b^a = b^p, c^a = c^p, d^a = d, c^b = c, d^c = d d^b,
[d, d^b] = 1, d^p = 1⟩ is soluble of derived length 3 but not metanilpotent-by-finite).
-/
public theorem_wanted finitelyPresentedSolubleMetanilpotentByFinite_refuted :
    ¬ finitelyPresentedSolubleMetanilpotentByFinite

end MathlibExt.GroupTheory.FinitelyPresentedSolubleMetanilpotentKourovka16Problem35Wanted
