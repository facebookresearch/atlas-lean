/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Float.Model

/-! Kernel-checked values of the actual core model; no hardware float evaluation. -/

namespace Float.Model.Tests

/-- The two zero signs have the same rational value. -/
theorem signed_zeros :
    (Float.Model.ofBits 0).toRat? = some 0 ∧
    (Float.Model.ofBits 0x8000000000000000).toRat? = some 0 := by
  decide +kernel

/-- Signed finite examples exercise a negative exponent and a negative sign. -/
theorem finite_values :
    (Float.Model.ofBits 0x3fe0000000000000).toRat? = some (1 / 2) ∧
    (Float.Model.ofBits 0xbff0000000000000).toRat? = some (-1) := by
  decide +kernel

/-- Neither infinity nor canonical NaN is assigned a rational value. -/
theorem nonfinite_values :
    (Float.Model.ofBits 0x7ff0000000000000).toRat? = none ∧
    (Float.Model.ofBits 0xfff0000000000000).toRat? = none ∧
    (Float.Model.ofBits 0x7ff8000000000000).toRat? = none := by
  decide +kernel

#print axioms Float.Model.toRat?
#print axioms Float.Model.toRat?_eq
#print axioms Float.Model.isSome_toRat?
#print axioms signed_zeros
#print axioms finite_values
#print axioms nonfinite_values
#print axioms Float.Model.unpack
#print axioms Float.Model.pack
#print axioms Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow

end Float.Model.Tests
