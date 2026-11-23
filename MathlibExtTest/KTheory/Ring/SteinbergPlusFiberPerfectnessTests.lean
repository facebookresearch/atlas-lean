/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberPerfectness

/-! # A client of perfectness of the original fiber fundamental group -/

noncomputable section

universe u v

namespace AlgebraicKTheory.StableGL

/-- Every homomorphism from the actual fiber total group to a commutative group is trivial. -/
theorem independentPlusFiber_commGroup_hom_trivial_test
    (R : Type u) [Ring R] (A : Type v) [CommGroup A]
    (f : FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) →* A) :
    f = 1 := by
  let _ := independentPlusFiberFundamental_isPerfect R
  ext g
  change f g = 1
  exact MonoidHom.mem_ker.mp
    ((Abelianization.commutator_subset_ker f) Group.IsPerfect.mem_commutator)

end AlgebraicKTheory.StableGL

end
