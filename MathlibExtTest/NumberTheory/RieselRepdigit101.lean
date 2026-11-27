/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RieselRepdigit101

namespace MetaMathlibExt

-- The least admissible base and length give the ordinary single-digit repdigit formula.
example : IsRieselNumber (101 * (180 ^ 171 - 1) / 179) :=
  isRieselNumber_repstring_101 (b := 180) (t := 171) (by decide) (by decide)

-- Advance both parameters by a full period and take the least positive exponent.
example : ¬ (repstring 11184990 101 0 411 * 2 - 1).Prime := by
  have hk := isRieselNumber_repstring_101 (b := 11184990) (t := 411) (by decide) (by decide)
  simpa only [pow_one] using hk.2 1 le_rfl

end MetaMathlibExt
