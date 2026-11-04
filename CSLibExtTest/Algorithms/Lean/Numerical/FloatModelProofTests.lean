/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.FloatModel

/-! Nonvacuous applications of both universal clauses to actual core-model operands. -/

namespace Float.Model.ProofTests

open Cslib.Algorithms.Lean.FloatingPoint

theorem add_two_subnormal_inputs :
    (Float.Model.add (Float.Model.ofBits 0x000fffffffffffff)
      (Float.Model.ofBits 0x0000000000000001)).toRat? =
        some (fl 53 ((4503599627370495 : Rat) * 2 ^ (-1074 : Int) +
          (2 : Rat) ^ (-1074 : Int))) :=
  Float.Model.toRat?_add _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem add_signed_zero_input :
    (Float.Model.add (Float.Model.ofBits 0x8000000000000000)
      (Float.Model.ofBits 0x0010000000000000)).toRat? =
        some (fl 53 ((0 : Rat) + (2 : Rat) ^ (-1022 : Int))) :=
  Float.Model.toRat?_add _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem mul_subnormal_input :
    (Float.Model.mul (Float.Model.ofBits 0x0000000000000001)
      (Float.Model.ofBits 0x4330000000000000)).toRat? =
        some (fl 53 ((2 : Rat) ^ (-1074 : Int) * (4503599627370496 : Rat))) :=
  Float.Model.toRat?_mul _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem mul_negative_near_tie :
    (Float.Model.mul (Float.Model.ofBits 0x3ff0000000000001)
      (Float.Model.ofBits 0xbfefffffffffffff)).toRat? =
        some (fl 53 (((1 : Rat) + (2 : Rat) ^ (-52 : Int)) *
          -((1 : Rat) - (2 : Rat) ^ (-53 : Int)))) :=
  Float.Model.toRat?_mul _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

#check @Float.Model.toRat?_add
#check @Float.Model.toRat?_mul
#print axioms Float.Model.toRat?_add
#print axioms Float.Model.toRat?_mul
#print axioms add_two_subnormal_inputs
#print axioms add_signed_zero_input
#print axioms mul_subnormal_input
#print axioms mul_negative_near_tie

end Float.Model.ProofTests
