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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwoIndependence
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupProjection
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH1

/-!
# Canonical finite-index corestriction in degree two

The degree-two independence theorem for right-transversal Schreier transfer
allows one right transversal to be chosen internally.  This file packages the
resulting canonical finite-index map, identifies it with the map attached to
every supplied right transversal, and records its cocycle representative
formula.

Together with canonical degree-one corestriction, the chosen-transversal cup
projection formula gives the canonical `H¹ × H¹ → H²` projection formula.
No norm-residue comparison, Kummer--Steinberg vanishing, or higher-degree
corestriction is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Canonical finite-index corestriction on `H²`, obtained by choosing a
right transversal. -/
noncomputable def corestrictionH2 (A : Rep k G) [H.FiniteIndex] :
    groupCohomology.H2 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H2 A :=
  corestrictionH2OfRightTransversal A (default : H.RightTransversal)

/-- Canonical `H²` corestriction agrees with the map from every supplied
finite right transversal. -/
theorem corestrictionH2_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH2 A = corestrictionH2OfRightTransversal A T := by
  unfold corestrictionH2
  exact corestrictionH2OfRightTransversal_independent A _ T

/-- Representative formula for canonical `H²` corestriction, computed using
any supplied finite right transversal. -/
theorem corestrictionH2_H2π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH2 A
        (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A) z) =
      groupCohomology.H2π A (corestrictionCocyclesTwo A T z) := by
  rw [corestrictionH2_eq_of_rightTransversal,
    corestrictionH2OfRightTransversal_H2π]

/-- Canonical finite-index cup projection formula:
`cor(res(x) ∪ y) = x ∪ cor(y)`.  The coefficient comparison is the
identity-on-carriers restriction/tensor isomorphism. -/
theorem corestrictionH2_cupOneOne
    (A B : Rep k G) (H : Subgroup G) [H.FiniteIndex]
    (x : groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH2 (A ⊗ B)
        (groupCohomology.map (MonoidHom.id H)
          (Rep.resTensorIso (Subgroup.subtype H) A B).hom 2
          (groupCohomology.cupOneOne
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (groupCohomology.map (Subgroup.subtype H) (𝟙 _) 1 x) y)) =
      groupCohomology.cupOneOne A B x (corestrictionH1 B y) := by
  unfold corestrictionH2 corestrictionH1
  exact corestrictionH2OfRightTransversal_cupOneOne
    A B (default : H.RightTransversal) x y

end groupCohomology
