/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily35

/-! # Tests for Choudhry's family (3.5) with square symmetric functions -/

namespace MathlibExtTest.NumberTheory
namespace ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily35

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- Choudhry's Table 1 lists this triple at `(s, t) = (1, 2)`.
example : HasSquareElementarySymmetricFunctions 28880 81225 537920 := by
  convert hasSquareElementarySymmetricFunctions_family35 1 2 using 1 <;> rfl

-- A vanishing parameter gives two zero entries.
example : HasSquareElementarySymmetricFunctions 0 1 0 := by
  convert hasSquareElementarySymmetricFunctions_family35 0 1 using 1 <;> rfl

-- Both parameters are nonzero, but `s ^ 4 - t ^ 4 = 0`.
example : HasSquareElementarySymmetricFunctions 128 0 128 := by
  convert hasSquareElementarySymmetricFunctions_family35 1 (-1) using 1 <;> rfl

end ThreeIntegersSymmetricSquaresHasSquareElementarySymmetricFunctionsFamily35
end MathlibExtTest.NumberTheory
