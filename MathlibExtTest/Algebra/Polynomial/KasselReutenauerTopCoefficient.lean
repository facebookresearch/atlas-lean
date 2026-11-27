/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.KasselReutenauerTopCoefficient

/-! # Tests for the top Kassel–Reutenauer coefficients -/

namespace MetaMathlibExt

-- The two index endpoints agree when `n = 1`.
example : kasselReutenauerCoeff 1 0 = 1 :=
  kasselReutenauerCoeff_eq_one 1 0 (by decide) (by decide) (by decide)

-- At the lower index bound, the proper divisor `4` is at the excluded endpoint.
example : kasselReutenauerCoeff 8 3 = 1 :=
  kasselReutenauerCoeff_eq_one 8 3 (by decide) (by decide) (by decide)

example : kasselReutenauerCoeff 8 7 = 1 :=
  kasselReutenauerCoeff_eq_one 8 7 (by decide) (by decide) (by decide)

-- The moved definition remains computable, including outside the top range.
example : kasselReutenauerCoeff 6 0 = 2 := by decide

end MetaMathlibExt
