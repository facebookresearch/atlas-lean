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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThreeIndependence

/-!
# Canonical finite-index corestriction in degree three

The degree-three independence theorem for right-transversal Schreier transfer
allows one right transversal to be chosen internally.  This file packages the
resulting canonical finite-index `H³` map, identifies it with the map attached
to every supplied right transversal, and records its cocycle representative
formula.

Coefficient naturality is provided in a downstream module.  No field,
Kummer, norm-residue, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Canonical degree-three corestriction for a finite-index subgroup. -/
noncomputable def corestrictionH3 (A : Rep k G) [H.FiniteIndex] :
    H3 (Rep.res (Subgroup.subtype H) A) →ₗ[k] H3 A :=
  corestrictionH3OfRightTransversal A
    (default : H.RightTransversal)

/-- Canonical degree-three corestriction is computed by every chosen right
transversal. -/
theorem corestrictionH3_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH3 A = corestrictionH3OfRightTransversal A T :=
  corestrictionH3OfRightTransversal_independent A
    (default : H.RightTransversal) T

/-- Representative formula for canonical degree-three corestriction, using
an arbitrary chosen right transversal. -/
@[simp]
theorem corestrictionH3_H3π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH3 A
        (H3π (Rep.res (Subgroup.subtype H) A) z) =
      H3π A (corestrictionCocyclesThree A T z) := by
  rw [corestrictionH3_eq_of_rightTransversal A T,
    corestrictionH3OfRightTransversal_H3π]

end groupCohomology
