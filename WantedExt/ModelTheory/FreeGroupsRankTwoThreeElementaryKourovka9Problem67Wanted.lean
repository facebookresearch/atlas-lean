/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tarski's problem for free groups of ranks 2 and 3 (Kourovka Notebook Problem 9.67)

Kourovka Notebook, Archive of Solved Problems, Problem 9.67 (A. D. Taimanov (A. Tarski)): let `F_n`
be a free group of rank `n`; is it true that `Th(F₂) = Th(F₃)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.FreeGroupsRankTwoThreeElementaryKourovka9Problem67Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.67 (A. D.
Taimanov). UnsolvedMath record UM-00700600 (`KOU-9.67`), dataset ulamai/UnsolvedMath v1.8.0.

Elementary equivalence is Mathlib's `ElementarilyEquivalent` for the first-order language of groups
`groupLanguage` (MathlibExt) with the canonical structures on `FreeGroup (Fin 2)` and `FreeGroup
(Fin 3)`.
-/

open FirstOrder Language

/-- Kourovka 9.67 (A. D. Taimanov; A. Tarski's problem): the free groups of ranks `2` and `3` are
elementarily equivalent, `Th(F₂) = Th(F₃)`. -/
def freeGroupsRankTwoThreeElementarilyEquivalent : Prop :=
  letI := groupLanguageStructure (FreeGroup (Fin 2))
  letI := groupLanguageStructure (FreeGroup (Fin 3))
  groupLanguage.ElementarilyEquivalent (FreeGroup (Fin 2)) (FreeGroup (Fin 3))

/--
Resolved true: Kharlampovich-Myasnikov and Sela prove that all non-abelian free groups are
elementarily equivalent (Tarski's problem), in particular `Th(F₂) = Th(F₃)`; the Kourovka Archive
answers 9.67 "Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 9.67 (A. D. Taimanov); resolution: O. Kharlampovich and A. Myasnikov, Elementary
theory of free non-abelian groups, J. Algebra 302 (2006), 451-552; Z. Sela, Diophantine geometry
over groups VI: The elementary theory of a free group, Geom. Funct. Anal. 16 (2006), 707-730,
https://doi.org/10.1007/s00039-006-0565-8, Kourovka Archive of Solved Problems, Problem 9.67: Yes,
it is, https://doi.org/10.1016/j.jalgebra.2006.03.033.
-/
public theorem_wanted freeGroupsRankTwoThreeElementarilyEquivalent_holds :
    freeGroupsRankTwoThreeElementarilyEquivalent

end MathlibExt.ModelTheory.FreeGroupsRankTwoThreeElementaryKourovka9Problem67Wanted
