/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Amenable and elementary amenable groups (Kourovka Notebook Problem 8.6)

Kourovka Notebook, Archive of Solved Problems, Problem 8.6 (R. I. Grigorchuk; question of M. M.
Day): do the classes of amenable groups and elementary groups coincide? The latter consists of
groups that can be obtained from commutative and finite groups by forming subgroups, factor-groups,
extensions, and direct limits.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import MathlibExt.GroupTheory.AmenableGroup
public import WantedExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.AmenableNotElementaryAmenableKourovka8Problem6Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.6 (R. I.
Grigorchuk; question of M. M. Day). UnsolvedMath record UM-00700458 (`KOU-8.6`), dataset
ulamai/UnsolvedMath v1.8.0.

Amenable is MathlibExt's Følner-condition `IsAmenable` (equivalent to amenability for discrete
groups). The elementary groups form the inductive class `IsElementaryAmenable` of the Kourovka 16.52
entry, reused here: finite and abelian groups, closed under isomorphisms, subgroups, quotients,
extensions and directed unions (the direct limits of the problem, up to the quotients already
allowed).
-/

open MathlibExt.GroupTheory.ElementaryAmenableVirtuallySolvableKourovka16Problem52Wanted
  (IsElementaryAmenable)

/-- Kourovka 8.6 (M. M. Day; posed by R. I. Grigorchuk): the amenable groups are exactly the
elementary amenable groups. -/
def amenableIffElementaryAmenable : Prop :=
  ∀ (G : Type) [Group G], IsAmenable G ↔ IsElementaryAmenable G

/--
Resolved false: the Kourovka Archive answers 8.6 "No", citing Grigorchuk (1983): his groups of
intermediate growth are amenable but not elementary amenable. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.6 (R. I. Grigorchuk; question of M.
M. Day); resolution: R. I. Grigorchuk, On the Milnor problem of group growth, Soviet Math. Dokl. 28
(1983), 23-26, Kourovka Archive, Problem 8.6: No (Grigorchuk), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted amenableIffElementaryAmenable_refuted : ¬ amenableIffElementaryAmenable

end MathlibExt.GroupTheory.AmenableNotElementaryAmenableKourovka8Problem6Wanted
