/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely many maximal locally soluble normal subgroups (Kourovka Notebook Problem 3.46)

Kourovka Notebook, Problem 3.46 (B. I. Plotkin), marked solved in the 21st issue: does there exist a
group having more than one, but finitely many maximal locally soluble normal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.MaximalLocallySolubleNormalKourovka3Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 3.46 (B. I. Plotkin). UnsolvedMath record
UM-00700195 (`KOU-3.46`), dataset ulamai/UnsolvedMath v1.8.0.

Locally soluble: every finitely generated subgroup is soluble. A maximal locally soluble normal
subgroup is a locally soluble normal subgroup not properly contained in another one (Mathlib's
`Maximal`). Groups in `Type`.
-/

/-- `N` is a locally soluble normal subgroup of `G`: normal, with every finitely generated
subgroup of `N` soluble. -/
def IsLocallySolubleNormal {G : Type} [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ ∀ H : Subgroup G, H ≤ N → H.FG → Group.IsSolvable H

/-- Kourovka 3.46 (B. I. Plotkin): there is a group with more than one, but finitely many, maximal
locally soluble normal subgroups. -/
def existsFinitelyManyMaximalLocallySolubleNormal : Prop :=
  ∃ (G : Type) (_ : Group G), {N : Subgroup G | Maximal IsLocallySolubleNormal N}.Finite ∧
    1 < {N : Subgroup G | Maximal IsLocallySolubleNormal N}.ncard

/--
Resolved true: van Doorn, Judin, Monticone and Morrison (Theorem 2.1; Monticone's note) construct a
group with exactly two maximal locally soluble normal subgroups. The 21st issue of the Kourovka
Notebook marks 3.46 solved ("Yes, such groups exist"; AI solution confirmed by M. Trombetti).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 3.46 (B. I. Plotkin); resolution: P.
Monticone, Kourovka Notebook Problem 3.46, solution note (17 June 2026), Kourovka Notebook site; W.
van Doorn, E. Judin, P. Monticone and D. Morrison, On some problems from the Kourovka Notebook,
preprint, arXiv:2607.17477 (2026), van Doorn-Judin-Monticone-Morrison, Theorem 2.1: a group (a
semidirect product of two groups of unitriangular ℤ²-indexed matrices with ℤ²) with exactly two
maximal locally soluble normal subgroups M₁ and M₂; an AI solution (Aristotle) confirmed by M.
Trombetti, Kourovka Notebook (21st issue), Problem 3.46: Yes, such groups exist,
https://arxiv.org/abs/2607.17477.
-/
public theorem_wanted existsFinitelyManyMaximalLocallySolubleNormal_holds :
    existsFinitelyManyMaximalLocallySolubleNormal

end MathlibExt.GroupTheory.MaximalLocallySolubleNormalKourovka3Problem46Wanted
