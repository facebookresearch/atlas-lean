/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_IsResidueAlgebra.lean`
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

The cited upstream file is adapted from a file of the Imperial College London FLT project
(https://github.com/ImperialCollegeLondon/FLT, branch `main` as of 2026-05-21, as the
upstream `ATTRIBUTION.md` records; header checked at commit
`a7dbce8494c29858093974a612a72b6454fc5cba`). The portions of this file that come from it
are adapted from:

`FLT/Deformations/IsResidueAlgebra.lean` (FLT):
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Javier López-Contreras, Kevin Buzzard
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue algebras

Let `𝓞` be a commutative ring and `A` a local `𝓞`-algebra. We say `A` is a *residue algebra*
over `𝓞` if `𝓞` surjects onto the residue field of `A`. When `𝓞` is local and the structure map
is local, the residue fields of `𝓞` and `A` are then isomorphic.

## Main definitions

* `IsResidueAlgebra 𝓞 A`: the map `𝓞 → ResidueField A` is surjective.
* `IsResidueAlgebra.algEquiv`: the isomorphism `ResidueField 𝓞 ≃ₐ[𝓞] ResidueField A`.
* `IsResidueAlgebra.preimage`: a chosen element of `𝓞` with the same residue as a given `r : A`.
-/

@[expose] public section

open Function IsLocalRing

variable (𝓞 : Type*) [CommRing 𝓞]

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]

/-- **Residue algebras.** A local `𝓞`-algebra `A` is a *residue algebra* if `𝓞` surjects onto the
residue field of `A`. -/
class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 (ResidueField A))

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

theorem algebraMap_surjective : Surjective (algebraMap 𝓞 (ResidueField A)) := isSurjective'

variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
/-- **Residue fields of a residue algebra.** If `𝓞` is local and `A` is a residue algebra over
`𝓞` whose structure map is local, the induced map of residue fields is bijective. -/
theorem algebraMap_bijective : Bijective (algebraMap (ResidueField 𝓞) (ResidueField A)) := by
  have hsurj1 := IsLocalRing.residue_surjective (R := 𝓞)
  have hsurj2 := IsResidueAlgebra.algebraMap_surjective 𝓞 A
  exact ⟨(algebraMap (ResidueField 𝓞) (ResidueField A)).injective,
    (Function.Surjective.of_comp_iff (algebraMap (ResidueField 𝓞) (ResidueField A)) hsurj1).mp
      hsurj2⟩

variable [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
/-- **Residue field isomorphism.** If `𝓞` is local and `A` is a residue algebra over `𝓞` whose
structure map is local, the residue fields of `𝓞` and `A` are isomorphic, through the map
induced by `algebraMap 𝓞 A`. -/
noncomputable def algEquiv : ResidueField 𝓞 ≃ₐ[𝓞] ResidueField A :=
  .ofBijective (IsScalarTower.toAlgHom _ _ _) (algebraMap_bijective _ _)

instance [IsLocalRing 𝓞] : IsResidueAlgebra 𝓞 𝓞 := ⟨IsLocalRing.residue_surjective⟩

/-- The residue field of `𝓞` is a residue algebra over `𝓞`. -/
instance residueField [IsLocalRing 𝓞] : IsResidueAlgebra 𝓞 (ResidueField 𝓞) where
  isSurjective' := by
    rw [IsScalarTower.algebraMap_eq 𝓞 (ResidueField 𝓞), RingHom.coe_comp]
    exact IsLocalRing.residue_surjective.comp IsLocalRing.residue_surjective

variable {A}

theorem exists_sub_mem_maximalIdeal (r : A) : ∃ a, r - algebraMap 𝓞 A a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 _ (residue _ r)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm

/-- **Chosen residue preimage.** For a residue algebra `A` over `𝓞`, a chosen element of `𝓞`
congruent to `r` modulo the maximal ideal of `A`. -/
noncomputable def preimage (r : A) : 𝓞 := (exists_sub_mem_maximalIdeal 𝓞 r).choose

theorem preimage_spec (r : A) : r - algebraMap 𝓞 A (preimage 𝓞 r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal 𝓞 r).choose_spec

theorem residue_preimage (r : A) :
    residue _ (algebraMap _ _ (preimage 𝓞 r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec 𝓞 r)).symm

end IsResidueAlgebra
