/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# The finite-index coinduction counit

For a finite-index subgroup `H ≤ G`, induction and coinduction are naturally
isomorphic. This supplies the canonical coinduction/restriction counit

`Coind_H^G (Res_H^G A) ⟶ A`.

The explicit bar-resolution comparison in `SchreierShapiroComparison` proves
that inverse Schreier Shapiro followed by this coefficient counit is the
established `schreierCorestriction` map in every degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Rep

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

/-- The canonical finite-index coinduction/restriction counit on a
`G`-representation. -/
noncomputable def corestrictionCounit (A : Rep k G) :
    coind H.subtype (Rep.res H.subtype A) ⟶ A := by
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact (coindResAdjunction k H).counit.app A

end groupCohomology
