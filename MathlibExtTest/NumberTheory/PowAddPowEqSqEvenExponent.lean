/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PowAddPowEqSqEvenExponent

/-! # Tests for evenness of the first exponent in `n^x + (5p)^y = z^2` -/

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- The residue 2 admits a solution with both exponents positive.
example : Even 6 := even_of_pos_exp 2 3 6 2 17 (by decide) (Or.inl rfl) (by decide) rfl

-- The residue 3 admits a solution at the endpoints x = 0 and y = 1.
example : Even 0 := even_of_pos_exp 3 3 0 1 4 (by decide) (Or.inr rfl) (by decide) rfl

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
