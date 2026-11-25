/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_ProartinianCompact.lean`
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
-/

module

public import MathlibExt.RingTheory.Deformations.ProartinianCat

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Compactness of proartinian rings with finite residue field

A proartinian local ring with finite residue field is compact: each quotient by an open ideal is
an artinian local ring with finite residue field, hence finite, so the ring is totally bounded,
and it is complete by assumption. In particular every object of `ProartinianCat 𝓞` is compact
when the residue field of `𝓞` is finite.

## Main results

* `IsArtinianRing.finite_of_finite_residueField`: an artinian local ring with finite residue
  field is finite.
* `IsProartinian.compactSpace_of_finite_residueField`: a proartinian local ring with finite
  residue field is compact.
* `Deformation.ProartinianCat.instCompactSpace`: objects of `ProartinianCat 𝓞` are compact when
  `ResidueField 𝓞` is finite.
-/

@[expose] public section

universe u

open CategoryTheory Function IsLocalRing Filter Topology Set Pointwise

/-- An artinian local ring with finite residue field is finite. -/
theorem IsArtinianRing.finite_of_finite_residueField (R : Type*) [CommRing R] [IsArtinianRing R]
    [IsLocalRing R] [Finite (ResidueField R)] : Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson R
  rw [ringJacobson_eq_maximalIdeal] at hn
  have h1 : Finite (R ⧸ maximalIdeal R) := ‹Finite (ResidueField R)›
  have h2 : Finite (R ⧸ maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

namespace IsProartinian

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLocalRing R] [IsProartinian R] [Finite (ResidueField R)]

/-- In a proartinian local ring with finite residue field, every open ideal has finite
index. -/
theorem finite_quotient_of_isOpen (I : Ideal R) (hI : IsOpen (X := R) I) :
    Finite (R ⧸ I) := by
  by_cases hI' : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI'
    exact Finite.of_subsingleton
  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (ResidueField.map (Ideal.Quotient.mk I)) := by
    have hcomp : Function.Surjective
        (ResidueField.map (Ideal.Quotient.mk I) ∘ residue R) := by
      rw [show ResidueField.map (Ideal.Quotient.mk I) ∘ residue R
            = residue (R ⧸ I) ∘ Ideal.Quotient.mk I from
          funext fun r ↦ ResidueField.map_residue _ r]
      exact (residue_surjective).comp Ideal.Quotient.mk_surjective
    exact hcomp.of_comp
  have : Finite (ResidueField (R ⧸ I)) := .of_surjective _ hsurj
  exact IsArtinianRing.finite_of_finite_residueField (R ⧸ I)

/-- A proartinian local ring with finite residue field is compact. -/
theorem compactSpace_of_finite_residueField : CompactSpace R := by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, completeSpace_iff_isComplete_univ.mp inferInstance⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨I, hI_open, hI_sub⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU
  have : Finite (R ⧸ I) := finite_quotient_of_isOpen I hI_open
  obtain ⟨sec, hsec⟩ := (Ideal.Quotient.mk_surjective (I := I)).hasRightInverse
  refine ⟨Set.range sec, Set.finite_range sec, fun x _ ↦ ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨sec (Ideal.Quotient.mk I x), ⟨_, rfl⟩, ?_⟩
  refine Set.mem_vadd_set.mpr ⟨x - sec (Ideal.Quotient.mk I x), hI_sub ?_, ?_⟩
  · change x - sec (Ideal.Quotient.mk I x) ∈ I
    rw [← Ideal.Quotient.eq]
    exact (hsec _).symm
  · change sec (Ideal.Quotient.mk I x) + (x - sec (Ideal.Quotient.mk I x)) = x
    abel

end IsProartinian

namespace Deformation.ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

instance instFiniteResidueField [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    Finite (ResidueField A) :=
  .of_surjective _ (IsResidueAlgebra.algebraMap_bijective 𝓞 A).surjective

instance instCompactSpace [Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    CompactSpace A :=
  IsProartinian.compactSpace_of_finite_residueField

end Deformation.ProartinianCat
