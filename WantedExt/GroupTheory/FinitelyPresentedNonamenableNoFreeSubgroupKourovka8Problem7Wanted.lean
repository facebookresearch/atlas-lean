/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely presented non-amenable groups without free subgroups (Kourovka Notebook Problem 8.7)

Kourovka Notebook, Archive of Solved Problems, Problem 8.7 (R. I. Grigorchuk): does there exist a
non-amenable finitely presented group which has no free subgroups of rank `2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import MathlibExt.GroupTheory.AmenableGroup

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedNonamenableNoFreeSubgroupKourovka8Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.7 (R. I.
Grigorchuk). UnsolvedMath record UM-00700459 (`KOU-8.7`), dataset ulamai/UnsolvedMath v1.8.0.

Finitely presented is Mathlib's `Group.IsFinitelyPresented`; amenable is MathlibExt's
Følner-condition `IsAmenable`; a free subgroup of rank `2` is the image of an injective homomorphism
from `FreeGroup (Fin 2)`.
-/

/-- Kourovka 8.7 (R. I. Grigorchuk): there is a finitely presented non-amenable group with no free
subgroup of rank `2`. -/
def finitelyPresentedNonamenableNoFreeSubgroup : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ ¬ IsAmenable G ∧
    ∀ f : FreeGroup (Fin 2) →* G, ¬ Function.Injective f

/--
Resolved true: the Kourovka Archive answers 8.7 "Yes, there does", citing Ol'shanskii and Sapir
(2002), who construct a finitely presented non-amenable group without free non-cyclic subgroups, an
extension of a group of large finite exponent by a cyclic group. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.7 (R. I. Grigorchuk); resolution:
A. Yu. Ol'shanskii and M. V. Sapir, Non-amenable finitely presented torsion-by-cyclic groups, Publ.
Math. IHÉS 96 (2002), 43-169, Kourovka Archive, Problem 8.7: Yes, there does; paper, Theorem 1.1(4):
a finitely presented non-amenable group without free non-cyclic subgroups,
https://arxiv.org/abs/math/0208237.
-/
public theorem_wanted finitelyPresentedNonamenableNoFreeSubgroup_holds :
    finitelyPresentedNonamenableNoFreeSubgroup

end MathlibExt.GroupTheory.FinitelyPresentedNonamenableNoFreeSubgroupKourovka8Problem7Wanted
