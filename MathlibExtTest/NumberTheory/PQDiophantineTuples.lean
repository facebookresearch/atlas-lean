/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PQDiophantineTuples

namespace MetaMathlibExt

/-- `(a, b, c) = (1, 3, 8)`: `9` does not divide `25`. -/
example : ¬(1 * 8 + 1 ∣ 3 * 8 + 1) :=
  not_mul_add_one_dvd_mul_add_one (by decide) (by decide) (by decide)

#print axioms not_mul_add_one_dvd_mul_add_one

end MetaMathlibExt
