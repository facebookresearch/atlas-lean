/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The number of pro-locally-finite varieties of groups (Kourovka Notebook Problem 6.15)

Kourovka Notebook, Archive of Solved Problems, Problem 6.15 (A. V. Kuznetsov): a variety is said to
be pro-locally-finite if it is not locally finite while all of its proper subvarieties are locally
finite. An example: the variety of abelian groups. How many pro-locally-finite varieties of groups
are there?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Continuum
public import WantedExt.GroupTheory.GroupVarietyShared
public import WantedExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.ProLocallyFiniteVarietiesKourovka6Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.15 (A. V.
Kuznetsov). UnsolvedMath record UM-00700362 (`KOU-6.15`), dataset ulamai/UnsolvedMath v1.8.0.

A variety of groups is represented by its laws, a fully invariant subgroup `N` of `FreeGroup ℕ`
(`IsFullyInvariant` of Kourovka 3.53); the groups of the variety are those satisfying every
word of `N` (`SatisfiesLaws` of the Kourovka 11.21 module). This correspondence is a bijection
reversing inclusion, so subvarieties of the variety with laws `N` correspond to fully invariant `N'
≥ N`, proper ones to `N' > N`. Locally finite varieties are `IsLocallyFiniteVariety`. The count is
the cardinality of the set of laws of pro-locally-finite varieties.
-/

open MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted
  (IsFullyInvariant)
open MathlibExt.GroupTheory.GroupVarietyShared (IsLocallyFiniteVariety)

/-- Kourovka 6.15 (A. V. Kuznetsov): there are continuum many pro-locally-finite varieties of
groups (not locally finite, while every proper subvariety is locally finite). A variety is given by
its laws `N`, a fully invariant subgroup of `FreeGroup ℕ`; its proper subvarieties are given by the
fully invariant `N'` with `N < N'`. -/
def proLocallyFiniteVarietiesContinuum : Prop :=
  Cardinal.mk {N : Subgroup (FreeGroup ℕ) // IsFullyInvariant N ∧ ¬ IsLocallyFiniteVariety N ∧
    ∀ N' : Subgroup (FreeGroup ℕ), IsFullyInvariant N' → N < N' → IsLocallyFiniteVariety N'} =
    Cardinal.continuum

/--
Resolved true: the Kourovka Archive answers 6.15 "There are continuum of such varieties", citing
Kozhevnikov (2000): there are exactly continuum many pro-locally-finite varieties of groups (at most
continuum is automatic, as varieties correspond to subsets of the countable group `FreeGroup ℕ`).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.15 (A. V.
Kuznetsov); resolution: P. A. Kozhevnikov, On varieties of groups of large odd exponent, Dep.
1612-V00, VINITI, Moscow, 2000 (Russian), Kourovka Archive, Problem 6.15: There are continuum of
such varieties (Kozhevnikov), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted proLocallyFiniteVarietiesContinuum_holds : proLocallyFiniteVarietiesContinuum

end MathlibExt.GroupTheory.ProLocallyFiniteVarietiesKourovka6Problem15Wanted
