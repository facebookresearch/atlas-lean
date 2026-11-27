/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumber

/-!
# Tests for `reducedFormsOfDiscriminant` and `gaussClassNumber`
-/

namespace MetaMathlibExt.GaussClassNumberTest

-- Of `x² ± xy + y²`, the boundary rule (`b ≥ 0` when `|b| = a`) keeps only `b = 1`.
example : reducedFormsOfDiscriminant (-3) = {(1, 1, 1)} := by
  decide +kernel

-- The search finds the imprimitive form `2x² + 2y²`, which the class number does not count.
example : reducedFormsOfDiscriminant (-16) = {(1, 0, 4), (2, 0, 2)} ∧
    gaussClassNumber (-16) = 1 := by
  decide +kernel

-- Both `2x² ± xy + 3y²` are reduced, since `|b| < a < c`.
example : reducedFormsOfDiscriminant (-23) = {(1, 1, 6), (2, -1, 3), (2, 1, 3)} ∧
    gaussClassNumber (-23) = 3 := by
  decide +kernel

-- `x² + 5y²` and `2x² + 2xy + 3y²` are the reduced forms of discriminant `-20`.
example : gaussClassNumber (-20) = 2 := by
  decide +kernel

-- Nonnegative discriminants have no reduced forms.
example : reducedFormsOfDiscriminant 0 = ∅ ∧ gaussClassNumber 5 = 0 := by
  decide +kernel

end MetaMathlibExt.GaussClassNumberTest
