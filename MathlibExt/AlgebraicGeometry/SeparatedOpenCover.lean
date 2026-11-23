/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.lean`
and
`P2M/Sol/S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A morphism `g : N ⟶ S` is separated if, for some open cover `𝒰` of `N`,
the overlap map induced on every pair of pieces of the cover is a closed
immersion. -/
theorem IsSeparated.of_isClosedImmersion_mapDesc_openCover
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g) fun ij => ?_
  obtain ⟨i, j⟩ := ij
  have hsq := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) g
  change IsClosedImmersion (pullback.snd (pullback.diagonal g)
    (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)))
  have key : hsq.isoPullback.inv ≫ pullback.mapDesc (𝒰.f i) (𝒰.f j) g =
      pullback.snd (pullback.diagonal g)
        (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _)
          (Category.comp_id _) (Category.comp_id _)) := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_snd.symm
  rw [← key]
  haveI := h i j
  infer_instance

end AlgebraicGeometry
