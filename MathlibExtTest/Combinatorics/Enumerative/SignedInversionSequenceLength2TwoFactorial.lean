/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2TwoFactorial

open MetaMathlibExt

-- All three sets permit both signs at length one, the smallest length in the theorem.
example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} 1 = 2 ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} 1 = 2 ∧
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} 1 = 2 := by
  exact signedInvAvoidCount_eq_two_mul_factorial 1 (by decide)

example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩} 2 = 4 := by
  exact (signedInvAvoidCount_eq_two_mul_factorial 2 (by decide)).1

example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
        ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩} 3 = 12 := by
  exact (signedInvAvoidCount_eq_two_mul_factorial 3 (by decide)).2.1

example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, true⟩,
        ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩} 4 = 48 := by
  exact (signedInvAvoidCount_eq_two_mul_factorial 4 (by decide)).2.2
