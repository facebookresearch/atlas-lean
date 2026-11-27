/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar

/-!
# Tests for the one-Sylvester count of consecutive star numbers

Concrete instances of the one-Sylvester formula.
-/

namespace MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar

open MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted

example : pSylvesterStarCount 1 6 = 6313 := by
  simpa using pSylvesterCount_one_star 6 (by decide)

example : pSylvesterStarCount 1 10 = 27441 := by
  simpa using pSylvesterCount_one_star 10 (by decide)

end MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar
