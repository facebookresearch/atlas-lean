/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresFamily36

/-! # Tests for Choudhry's family (3.6) of integer triples with square symmetric functions -/

namespace MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily36

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- Choudhry's Table 1 lists this triple at `(s, t) = (1, 2)`.
example : HasSquareElementarySymmetricFunctions 302580 107584 16245 :=
  hasSquareElementarySymmetricFunctions_family36 1 2

-- Equal nonzero parameters make `s ^ 2 - t ^ 2` vanish.
example : HasSquareElementarySymmetricFunctions 0 64 0 :=
  hasSquareElementarySymmetricFunctions_family36 1 1

end MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily36
