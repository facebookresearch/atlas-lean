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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferIndependence

/-!
# Canonical finite-index corestriction in degree one

Mathlib supplies an inhabited type of right transversals for every subgroup.
The chosen-transversal degree-one transfer is independent of that choice, so
choosing the default transversal defines a canonical finite-index
corestriction map on `H¹`.

The public comparison theorem identifies the canonical map with the map from
every supplied right transversal.  The representative formula may therefore
be computed using whichever transversal is convenient.  No degree-two
corestriction, cup projection formula, finite-etale comparison, norm-residue
map, or Kummer-Steinberg vanishing is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Canonical degree-one corestriction for a finite-index subgroup. -/
noncomputable def corestrictionH1 (A : Rep k G) [H.FiniteIndex] :
    groupCohomology.H1 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H1 A :=
  corestrictionH1OfRightTransversal A
    (default : H.RightTransversal)

/-- The canonical degree-one corestriction is computed by every chosen right
transversal. -/
theorem corestrictionH1_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH1 A = corestrictionH1OfRightTransversal A T :=
  corestrictionH1OfRightTransversal_independent A
    (default : H.RightTransversal) T

/-- Representative formula for canonical degree-one corestriction, using an
arbitrary chosen right transversal. -/
@[simp]
theorem corestrictionH1_H1π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH1 A
        (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A) f) =
      groupCohomology.H1π A (corestrictionCocyclesOne A T f) := by
  rw [corestrictionH1_eq_of_rightTransversal A T,
    corestrictionH1OfRightTransversal_H1π]

end groupCohomology
