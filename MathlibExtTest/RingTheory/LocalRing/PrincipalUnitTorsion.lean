/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.PrincipalUnitTorsion

/-! # Consumers for tame torsion in principal units -/

namespace IsLocalRingPrincipalUnitTorsionTest

universe u

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource {A : Type u} [CommRing A] [IsLocalRing A]
    {u : A} (hu : u - 1 ∈ IsLocalRing.maximalIdeal A) {n : ℕ}
    (hn : IsUnit (n : A)) (hun : u ^ n = 1) : u = 1 :=
  IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hu hn hun

end IsLocalRingPrincipalUnitTorsionTest
