/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Definability of the derived subgroup of a free group (Kourovka Notebook Problem 1.19)

Kourovka Notebook, Archive of Solved Problems, Problem 1.19 (A. I. Mal'cev; Yu. L. Ershov): which
subgroups (subsets) are first order definable in a free group? Which subgroups are relatively
elementarily definable in a free group? In particular, is the derived subgroup first order definable
(relatively elementarily definable) in a free group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.ModelTheory.Definability
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.FreeGroupDerivedSubgroupDefinableKourovka1Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.19 (A. I.
Mal'cev; Yu. L. Ershov). UnsolvedMath record UM-00700015 (`KOU-1.19`), dataset ulamai/UnsolvedMath
v1.8.0.

Only the question on first-order definability of the derived subgroup is formalized: the
classification questions are not propositions, and relative elementary definability is not
formalized. Definable means definable in the language of groups (`groupLanguage`) with parameters
from the group, as in Kharlampovich and Myasnikov, whose language contains the free generators as
constants. Ranks `r ≥ 2` only: `[F₁, F₁]` is trivial and definable. The target is stated for some
rank `r ≥ 2`, so its refutation covers every `r ≥ 2`.
-/

open FirstOrder Language

/-- Kourovka 1.19 (A. I. Mal'cev), the question on the derived subgroup: for some rank `r ≥ 2`, the
derived subgroup `[F_r, F_r]` of the free group `F_r` is first-order definable in `F_r` by a formula
of the language of groups with parameters from `F_r`. -/
def freeGroupDerivedSubgroupDefinable : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧
    letI := groupLanguageStructure (FreeGroup (Fin r))
    (Set.univ : Set (FreeGroup (Fin r))).Definable₁ groupLanguage
      (commutator (FreeGroup (Fin r)) : Set (FreeGroup (Fin r)))

/--
Resolved false: Kharlampovich and Myasnikov (Theorem 1) prove that proper non-cyclic subgroups of a
non-abelian free group `F` of finite rank are not definable in `F` (formulas with the generators of
`F` as constants); for `r ≥ 2` the derived subgroup `[F_r, F_r]` is proper and not cyclic. The
Kourovka Archive records the solution. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 1.19 (A. I. Mal'cev; Yu. L. Ershov); resolution: O. Kharlampovich and A.
Myasnikov, Definable sets in a hyperbolic group, Int. J. Algebra Comput. 23 (2013), no. 1, 91-110,
arXiv:1111.0577, Theorem 1 (proper non-cyclic subgroups of a free group of finite rank are not
definable); Kourovka Archive, Problem 1.19, https://arxiv.org/abs/1111.0577.
-/
public theorem_wanted freeGroupDerivedSubgroupDefinable_refuted :
    ¬ freeGroupDerivedSubgroupDefinable

end MathlibExt.ModelTheory.FreeGroupDerivedSubgroupDefinableKourovka1Problem19Wanted
