/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local finiteness of lattices of varieties of groups (Kourovka Notebook Problem 6.14)

Kourovka Notebook, Archive of Solved Problems, Problem 6.14 (A. V. Kuznetsov): are the following
lattices locally finite: the lattice of all locally finite varieties of groups? the lattice of all
varieties of groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.SupClosed
public import WantedExt.GroupTheory.GroupVarietyShared
public import WantedExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.VarietyLatticeNotLocallyFiniteKourovka6Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.14 (A. V.
Kuznetsov). UnsolvedMath record UM-00700361 (`KOU-6.14`), dataset ulamai/UnsolvedMath v1.8.0.

A variety of groups is represented by its laws, a fully invariant subgroup `N` of `FreeGroup ℕ`
(`IsFullyInvariant` of Kourovka 3.53); the groups of the variety are those satisfying every
word of `N` (`SatisfiesLaws` of the Kourovka 11.21 module). This correspondence is a bijection
reversing inclusion, so subvarieties of the variety with laws `N` correspond to fully invariant `N'
≥ N`, proper ones to `N' > N`. Joins and meets of varieties correspond to meets and joins of their
laws in `Subgroup (FreeGroup ℕ)`, and joins and meets of locally finite varieties are locally
finite, so a set `S` of varieties generates the sublattice dual to `latticeClosure S`. A lattice is
locally finite when every finitely generated sublattice is finite (the reading with finite intervals
is trivially false for the lattice of all varieties, whose interval below the abelian groups
contains every `𝔄_n`). Locally finite varieties are `IsLocallyFiniteVariety`: every finitely
generated group of the variety is finite.
-/

open MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted
  (IsFullyInvariant)
open MathlibExt.GroupTheory.GroupVarietyShared (IsLocallyFiniteVariety)

/-- Kourovka 6.14, first lattice (A. V. Kuznetsov): the lattice of locally finite varieties of
groups is locally finite: every finite set of locally finite varieties generates a finite
sublattice. Varieties are represented by their laws, the fully invariant subgroups of
`FreeGroup ℕ` (join and meet of varieties are meet and join of laws). -/
def locallyFiniteVarietiesLatticeLocallyFinite : Prop :=
  ∀ S : Set (Subgroup (FreeGroup ℕ)), S.Finite →
    (∀ N ∈ S, IsFullyInvariant N ∧ IsLocallyFiniteVariety N) → (latticeClosure S).Finite

/-- Kourovka 6.14, second lattice (A. V. Kuznetsov): the lattice of all varieties of groups is
locally finite. -/
def varietiesLatticeLocallyFinite : Prop :=
  ∀ S : Set (Subgroup (FreeGroup ℕ)), S.Finite → (∀ N ∈ S, IsFullyInvariant N) →
    (latticeClosure S).Finite

/--
Resolved false: the Kourovka Archive answers 6.14 "No, they are not", citing Anokhin (1999); for the
first lattice, some finite set of locally finite varieties of groups generates an infinite
sublattice. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.14
(A. V. Kuznetsov); resolution: M. I. Anokhin, Embedding lattices in lattices of varieties of groups,
Izv. Math. 63, no. 4 (1999), 649-665, Corollary 1.2 (the lattice of locally finite group varieties
is not locally finite), as stated in the zbMATH review Zbl 0966.20015; Kourovka Archive, Problem
6.14: No, they are not (Anokhin), https://doi.org/10.1070/IM1999v063n04ABEH000250.
-/
public theorem_wanted locallyFiniteVarietiesLatticeLocallyFinite_refuted :
    ¬ locallyFiniteVarietiesLatticeLocallyFinite

/--
Resolved false: the Kourovka Archive answers 6.14 "No, they are not", citing Anokhin (1999); for the
second lattice, some finite set of varieties of groups generates an infinite sublattice. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.14 (A. V. Kuznetsov);
resolution: M. I. Anokhin, Embedding lattices in lattices of varieties of groups, Izv. Math. 63, no.
4 (1999), 649-665, Corollary 1.2 (the lattice of locally finite group varieties is not locally
finite), as stated in the zbMATH review Zbl 0966.20015; Kourovka Archive, Problem 6.14: No, they are
not (Anokhin), https://doi.org/10.1070/IM1999v063n04ABEH000250.
-/
public theorem_wanted varietiesLatticeLocallyFinite_refuted : ¬ varietiesLatticeLocallyFinite

end MathlibExt.GroupTheory.VarietyLatticeNotLocallyFiniteKourovka6Problem14Wanted
