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
# Coinduction counit for a finite-index subgroup

Let k be a commutative ring, G a group and H≤G a finite-index subgroup.
The finite-index induction/coinduction isomorphism gives the adjunction
Coind_H^G ⊣ Res_H^G and its coefficient counit
Coind_H^G(Res_H^G A)→A for a k-linear G-representation A.
This is the coefficient map used after inverse Shapiro in the
finite-index corestriction comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Rep

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

/-- For a commutative ring k, a group G, a finite-index subgroup H
and a k-linear G-representation A, this is the counit
Coind_H^G(Res_H^G A)→A of the finite-index coinduction/restriction
adjunction. The scalar ring and group both have universe u. -/
noncomputable def corestrictionCounit (A : Rep k G) :
    coind H.subtype (Rep.res H.subtype A) ⟶ A := by
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact (coindResAdjunction k H).counit.app A

end groupCohomology
