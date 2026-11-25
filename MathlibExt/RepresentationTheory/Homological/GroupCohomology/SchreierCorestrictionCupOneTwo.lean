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
# Canonical degree-three cup projection formula

Canonical finite-index degree-three corestriction satisfies the `(1,2)` cup
projection formula `cor(res(x) cup y) = x cup cor(y)`.  This follows by
specializing the chosen-transversal formula to the default transversal used
by canonical corestriction.

No field-theoretic, Kummer, norm-residue, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Canonical finite-index `H¹ × H² → H³` cup projection formula:
`cor(res(x) cup y) = x cup cor(y)`. -/
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
