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
# The concrete quotient description of third group cohomology

Let k be a commutative ring, G a group, and A a k-linear representation in universe u. The
coordinate short complex C²(G,A)→C³(G,A)→C⁴(G,A) identifies H³(G,A) with ker(δ₃)/im(δ₂).

The isomorphism sends the class of a cycle in the inhomogeneous complex to the quotient class of
its triple-variable coordinate cocycle. It commutes with the cycle projections, so it preserves
representatives as well as the cohomology objects.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory ShortComplex

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. There is a k-module isomorphism H³(G,A)≅ker(δ₃)/im(δ₂) obtained from the degree-three
short-complex coordinate isomorphism. It sends a class represented by z:G³→A to the quotient
class of the same three-cocycle. For b:G×G→A, δ₂b(g,h,i)=ρ(g)b(h,i)-b(gh,i)+b(g,hi)-b(g,h). The
differential is δ₃z(g,h,i,j)=ρ(g)z(h,i,j)-z(gh,i,j)+z(g,hi,j)-z(g,h,ij)+z(g,h,i). -/
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
