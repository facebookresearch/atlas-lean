/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_IsProartinian.lean`
and
`Definitions/Def_Deformations_Deformations_Lemmas.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

The cited upstream files are adapted from files of the Imperial College London FLT
project (https://github.com/ImperialCollegeLondon/FLT, branch `main` as of 2026-05-21, as
the upstream `ATTRIBUTION.md` records; headers checked at commit
`a7dbce8494c29858093974a612a72b6454fc5cba`). The portions of this file that come from them
are adapted from:

`FLT/Deformations/IsProartinian.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde

`FLT/Deformations/Lemmas.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/

module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.UniformSpace.Cauchy

import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Proartinian topological rings

A topological ring `R` is *proartinian* if its topology is linear (open ideals form a basis of
neighbourhoods of `0`), it is `T₀` and complete, and `R ⧸ I` is artinian for every open ideal
`I`. This is the topological condition on the coefficient rings of Galois deformation theory.

## Main definitions

* `IsProartinian R`: the topological ring `R` is proartinian.

## Main results

* `isProartinian_iff_isArtinianRing`: a discrete ring is proartinian iff it is artinian.
* `isOpen_maximalIdeal_of_isProartinian`: the maximal ideal of a proartinian local ring is open.
* `exists_maximalIdeal_pow_le_of_isProartinian`: every open ideal of a proartinian local ring
  contains a power of the maximal ideal.
* `isLocalHom_of_isContinuous_of_isProartinian`: continuous ring maps between proartinian local
  rings are local.
-/

@[expose] public section

/-- **Open maximal ideals of linearly topologized rings.** A nontrivial commutative topological
ring that is `T₀` and linearly topologized has an open maximal ideal. -/
theorem IsLinearTopology.exists_ideal_isMaximal_and_isOpen
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [Nontrivial R] [T0Space R] :
    ∃ I : Ideal R, I.IsMaximal ∧ IsOpen (X := R) I := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
    ((isClosed_singleton (x := (1 : R))).isOpen_compl.mem_nhds (x := 0) (by simp))
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (by simpa [Ideal.eq_top_iff_one] using hI')
  exact ⟨J, hJ, AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := J.toAddSubgroup) hIJ hI⟩

/-- A discrete topological group has the discrete right uniformity. -/
@[to_additive /-- A discrete additive topological group has the discrete right uniformity. -/]
instance IsTopologicalGroup.discreteUniformity
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    letI := IsTopologicalGroup.rightUniformSpace G
    DiscreteUniformity G := by
  simp only [discreteUniformity_iff_setRelId_mem_uniformity]
  exact ⟨{1}, by simp [Set.subset_def, ← div_eq_mul_inv, div_eq_one]⟩

section Proartinian

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

variable (R) in
/-- **Proartinian rings.** A topological ring is *proartinian* if its topology is linear, `T₀`
and complete, and the quotient by every open ideal is an artinian ring. -/
class IsProartinian : Prop extends IsLinearTopology R R, T0Space R,
    letI := IsTopologicalAddGroup.rightUniformSpace R; CompleteSpace R where
  /-- The quotient by an open ideal is artinian. -/
  isArtinianRing_quotient (I : Ideal R) : IsOpen (X := R) I → IsArtinianRing (R ⧸ I)

attribute [instance low] IsProartinian.toIsLinearTopology
  IsProartinian.toT0Space IsProartinian.toCompleteSpace

/-- **Discrete proartinian rings.** A discrete ring is proartinian if and only if it is
artinian. -/
theorem isProartinian_iff_isArtinianRing [DiscreteTopology R] :
    IsProartinian R ↔ IsArtinianRing R := by
  constructor <;> intro
  · have := IsProartinian.isArtinianRing_quotient (⊥ : Ideal R) (isOpen_discrete _)
    exact (RingEquiv.quotientBot R).surjective.isArtinianRing
  · exact ⟨fun I _ ↦ inferInstance⟩

instance [DiscreteTopology R] [IsArtinianRing R] : IsProartinian R := by
  rwa [isProartinian_iff_isArtinianRing]

section IsLocalRing

open IsLocalRing

variable [IsLocalRing R] [IsLocalRing S]

/-- **The maximal ideal is open.** The maximal ideal of a proartinian local ring is open. -/
theorem isOpen_maximalIdeal_of_isProartinian [IsProartinian R] :
    IsOpen (X := R) (maximalIdeal R) := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.exists_ideal_isMaximal_and_isOpen R
  exact (isMaximal_iff _).mp hI ▸ hI'

/-- **Open ideals contain a power of the maximal ideal.** Every open ideal of a proartinian local
ring contains a power of the maximal ideal. -/
theorem exists_maximalIdeal_pow_le_of_isProartinian [IsProartinian R]
    (I : Ideal R) (hI : IsOpen (X := R) I) :
    ∃ n, maximalIdeal R ^ n ≤ I := by
  have := IsProartinian.isArtinianRing_quotient I hI
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

/-- **Continuous maps are local.** A continuous ring map between proartinian local rings is
local. -/
theorem isLocalHom_of_isContinuous_of_isProartinian
    [IsProartinian R] (f : R →+* S) [IsProartinian S] (h : Continuous f) : IsLocalHom f := by
  constructor
  intro a ha
  by_contra ha'
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian ((maximalIdeal S).comap f)
    (isOpen_maximalIdeal_of_isProartinian.preimage h)
  exact hn (Ideal.pow_mem_pow ha' n) (by simpa using ha.pow n)

end IsLocalRing

end Proartinian
