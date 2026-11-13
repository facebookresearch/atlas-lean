/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of being a derived subgroup (Kourovka Notebook Problem 21.32)

Kourovka Notebook, Problem 21.32 (P. J. Cameron), marked solved in the 21st issue: is the following
problem decidable, and if so, what is its complexity? Given a finite group `G`, is there a finite
group `H` such that the derived subgroup of `H` is isomorphic to `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.Commutator.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.IntegrableFiniteGroupDecidableKourovka21Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.32 (P. J. Cameron). UnsolvedMath record
UM-00002541 (`KOU-21.32`), dataset ulamai/UnsolvedMath v1.8.0.

A finite group is given by its multiplication table on `Fin n`, coded as a list of `n` rows of
natural numbers (a `Primcodable` type); a code satisfies the predicate when it is the table of a
group structure on `Fin n` whose group is the derived subgroup of some finite group. Decidability is
`ComputablePred`. The complexity question is not formalized.
-/

/-- **Integrable group tables.** A finite list $t = (t_0, \dots, t_{n-1})$ of finite lists of
natural numbers is an integrable group table when there is a group structure on
$\{0, \dots, n-1\}$ such that, for all $i, j < n$, the product of $i$ and $j$ is the entry of $t_i$
at index $j$, counting from $0$ (an entry missing from a short row is read as $0$), and some finite
group $H$ has derived subgroup $[H, H]$ isomorphic to this group. Lists that are not the
multiplication table of a group on $\{0, \dots, n-1\}$ do not satisfy the predicate. -/
def IsIntegrableGroupTable (t : List (List ℕ)) : Prop :=
  ∃ inst : Group (Fin t.length),
    (∀ i j : Fin t.length, ((inst.mul i j : Fin t.length) : ℕ) = (t.getD i []).getD j 0) ∧
    letI := inst
    ∃ (H : Type) (_ : Group H) (_ : Finite H), Nonempty (commutator H ≃* Fin t.length)

/-- **Kourovka Problem 21.32 (decidability of integrability).** The statement that integrable group
tables form a decidable set: some computable function decides, for every finite list
$t = (t_0, \dots, t_{n-1})$ of finite lists of natural numbers, whether $t$ is an integrable group
table, that is, whether there is a group structure on $\{0, \dots, n-1\}$ in which, for all
$i, j < n$, the product of $i$ and $j$ is the entry of $t_i$ at index $j$, counting from $0$ (an
entry missing from a short row is read as $0$), and which is isomorphic to the derived subgroup of
some finite group. -/
def integrabilityDecidable : Prop :=
  ComputablePred IsIntegrableGroupTable

/--
**Integrability of finite groups is decidable.** Integrable group tables form a decidable set: some
computable function decides, for every finite list $t = (t_0, \dots, t_{n-1})$ of finite lists of
natural numbers, whether there is a group structure on $\{0, \dots, n-1\}$ in which, for all
$i, j < n$, the product of $i$ and $j$ is the entry of $t_i$ at index $j$, counting from $0$ (an
entry missing from a short row is read as $0$), and which is isomorphic to the derived subgroup of
some finite group. That is, the decidability part of Kourovka Problem 21.32 has a positive answer.

Kalithasan and Thomas bound the order of some integral of an integrable finite group $G$ (their
Theorem 3.3 and its Corollary), which makes the problem decidable; the 21st issue of the Kourovka
Notebook marks 21.32 solved ("Yes, it is decidable, in nondeterministic quasi-polynomial time").
The complexity bound is not formalized.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.32 (P. J. Cameron); resolution:
S. Kalithasan and V. Z. Thomas, On the decidability of the integrability of finite groups, preprint,
arXiv:2602.18829 (2026), Theorem 3.3 (an integrable finite group G has an integral, a group with
derived subgroup ≅ G, of order bounded in terms of |Aut(G)|, |Z(G)|, μ(G) and d(Z(G))) and its
Corollary: integrability of a finite group is decidable; Kourovka Notebook (21st issue), Problem
21.32: Yes, it is decidable, in nondeterministic quasi-polynomial time,
https://arxiv.org/abs/2602.18829.
-/
public theorem_wanted integrabilityDecidable_holds : integrabilityDecidable

end MathlibExt.GroupTheory.IntegrableFiniteGroupDecidableKourovka21Problem32Wanted
