/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.SuperMZumkellerIsSuperMZumkellerFourNotKmPerfect

/-!
# Tests for four being super-m-Zumkeller but not `k`-m-perfect
-/

namespace MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerFourNotKmPerfect

open MathlibExt.NumberTheory.SuperMZumkellerWanted

-- Four is super-m-Zumkeller.
example : IsSuperMZumkeller 4 :=
  isSuperMZumkeller_four_not_kmPerfect.left

-- Four is not `2`-m-perfect.
example : ¬ IsKMPerfect 2 4 :=
  isSuperMZumkeller_four_not_kmPerfect.right 2 le_rfl

-- Four is not `5`-m-perfect.
example : ¬ IsKMPerfect 5 4 :=
  isSuperMZumkeller_four_not_kmPerfect.right 5 (by decide)

end MathlibExtTest.NumberTheory.SuperMZumkellerIsSuperMZumkellerFourNotKmPerfect
