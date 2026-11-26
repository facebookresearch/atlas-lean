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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH2
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupOneTwoProjection

/-!
# The finite-index cup projection formula in degrees one and two

Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A,B k-linear
G-representations in universe u. For x∈H¹(G,A) and y∈H²(H,Res_H B), the projection formula is
cor³_{A⊗B}(i_{H,*}(res¹_H x∪y))=x∪cor²_B(y).

Here i_H:Res_H A⊗Res_H B≅Res_H(A⊗B) is the tensor-restriction isomorphism. It transports the
subgroup cup from tensor products of restricted coefficients to the restricted ambient tensor
coefficient before corestriction. The degree-three and degree-two corestrictions are independent
of the chosen right transversal.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, H≤G a finite-index subgroup, and A,B k-linear
G-representations in universe u. For x∈H¹(G,A), y∈H²(H,Res_H B), and i_H:Res_H A⊗Res_H
B≅Res_H(A⊗B), one has cor³_{A⊗B}(i_{H,*}(res¹_H x∪y))=x∪cor²_B(y) in H³(G,A⊗_k B). The first cup
is taken with the restricted coefficients, then transported by i_H. -/
theorem corestrictionH3_cupOneTwo
    (A B : Rep k G) (H : Subgroup G) [H.FiniteIndex]
    (x : H1 A) (y : H2 (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH3 (A ⊗ B)
        (map (MonoidHom.id H)
          (Rep.resTensorIso (Subgroup.subtype H) A B).hom 3
          (cupOneTwo
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (map (Subgroup.subtype H) (𝟙 _) 1 x) y)) =
      cupOneTwo A B x (corestrictionH2 B y) := by
  unfold corestrictionH3 corestrictionH2
  exact corestrictionH3OfRightTransversal_cupOneTwo
    A B (default : H.RightTransversal) x y

end groupCohomology
