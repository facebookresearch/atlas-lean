/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessVieta

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessVieta

open MetaMathlibExt

-- The root (3, 3, 3) for k = 0 jumps to (3, 6, 3).
example : IsInducedGenSecondMarkovSolution 0 3 6 3 := by
  have h : IsInducedGenSecondMarkovSolution 0 3 3 3 :=
    ⟨by decide, by decide, by decide, by decide, ⟨1, by decide⟩, ⟨1, by decide⟩,
      ⟨1, by decide⟩⟩
  have hv := IsInducedGenSecondMarkovSolution.vieta h
  have he : (3 : ℤ) * 3 - 3 - (0 : ℤ) ^ 2 - 2 * (0 : ℤ) = 6 := by decide
  simpa [he] using hv.1

-- The root (5, 5, 5) for k = 1 jumps to (5, 17, 5).
example : IsInducedGenSecondMarkovSolution 1 5 17 5 := by
  have h : IsInducedGenSecondMarkovSolution 1 5 5 5 :=
    ⟨by decide, by decide, by decide, by decide, ⟨1, by decide⟩, ⟨1, by decide⟩,
      ⟨1, by decide⟩⟩
  have hv := IsInducedGenSecondMarkovSolution.vieta h
  have he : (5 : ℤ) * 5 - 5 - (1 : ℤ) ^ 2 - 2 * (1 : ℤ) = 17 := by decide
  simpa [he] using hv.1

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessVieta
