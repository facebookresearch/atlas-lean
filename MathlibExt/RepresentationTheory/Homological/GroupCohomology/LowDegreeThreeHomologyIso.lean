/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree

/-!
# The concrete quotient model for third group cohomology

The explicit degree-three inhomogeneous short complex identifies ordinary
third group cohomology with its concrete kernel/image quotient.  This is
the degree-three analogue of Mathlib's `groupCohomology.H2Iso`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory ShortComplex

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Ordinary H3 identified with the concrete homology quotient of the
explicit degree-three inhomogeneous short complex. -/
noncomputable def H3Iso (A : Rep k G) :
    H3 A ≅ (shortComplexH3 A).moduleCatLeftHomologyData.H :=
  (leftHomologyIso _).symm ≪≫
    (leftHomologyMapIso' (isoShortComplexH3 A) _ _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem π_comp_H3Iso_hom (A : Rep k G) :
    π A 3 ≫ (H3Iso A).hom =
      (isoCocycles₃ A).hom ≫
        (shortComplexH3 A).moduleCatLeftHomologyData.π := by
  simp only [H3Iso, isoCocycles₃, π,
    HomologicalComplex.homologyπ, Iso.trans_hom, Iso.symm_hom,
    leftHomologyMapIso'_hom, cyclesMapIso'_hom]
  rw [ShortComplex.homologyπ_comp_leftHomologyIso_inv_assoc]
  exact ShortComplex.leftHomologyπ_naturality'
    (isoShortComplexH3 A).hom
    ((inhomogeneousCochains A).sc 3).leftHomologyData
    (shortComplexH3 A).moduleCatLeftHomologyData

end groupCohomology
