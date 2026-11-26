/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCubeSquareNeighbors

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

-- The upper neighbor of 23³ is 2³ · 39², so the lower neighbor cannot have the same form.
example : ¬ ∃ p y : ℕ, p.Prime ∧ 0 < y ∧ (23 : ℤ) ^ 3 - 1 = (p : ℤ) ^ 3 * (y : ℤ) ^ 2 := by
  rintro ⟨p, y, hp, hy, h⟩
  exact not_exists_prime_cube_square_neighbors_of_cube
    ⟨p, 2, 23, y, 39, hp, by decide, by decide, hy, by decide, h, by decide⟩

end MathlibExt.NumberTheory.PowerfulNumbersWanted
