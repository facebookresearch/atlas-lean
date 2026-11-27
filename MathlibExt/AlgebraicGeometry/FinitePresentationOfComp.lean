/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType.lean`
and
`P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType.lean`
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

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If a composite of scheme morphisms is locally of finite presentation and
the second morphism is locally of finite type, then the first morphism is
locally of finite presentation. -/
public theorem locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g))
    (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by
  have : HasRingHomProperty (affineLocally RingHom.FinitePresentation)
      RingHom.FinitePresentation :=
    ⟨RingHom.finitePresentation_isLocal, rfl⟩
  have : HasRingHomProperty (affineLocally RingHom.FiniteType) RingHom.FiniteType :=
    ⟨RingHom.finiteType_isLocal, rfl⟩
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at h ⊢
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType] at hg
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := affineLocally RingHom.FinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict
      (P := affineLocally RingHom.FinitePresentation) h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict
      (P := affineLocally RingHom.FiniteType) hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := affineLocally RingHom.FinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (affineLocally RingHom.FinitePresentation) (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (HasRingHomProperty.comp_of_isOpenImmersion
      (affineLocally RingHom.FiniteType) U.1.ι g hg) inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := affineLocally RingHom.FinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (affineLocally RingHom.FinitePresentation) U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine
    (P := affineLocally RingHom.FinitePresentation)] at h ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := affineLocally RingHom.FiniteType)] at hg
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

end AlgebraicGeometry
