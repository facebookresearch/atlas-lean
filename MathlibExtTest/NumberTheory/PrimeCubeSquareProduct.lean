/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCubeSquareProduct

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

-- The right side allows any integer y, including zero, but x = 0 never works.
example (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (y : ℤ) :
    64 * (0 : ℤ) ^ 6 - 1 ≠ (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2 :=
  fun h ↦ not_exists_sixty_four_mul_pow_six_sub_one_eq ⟨p, q, 0, y, hp, hq, h⟩

-- No distinctness hypothesis is needed on the primes.
example (p : ℕ) (hp : p.Prime) (x y : ℤ) :
    64 * x ^ 6 - 1 ≠ (p : ℤ) ^ 3 * (p : ℤ) ^ 3 * y ^ 2 :=
  fun h ↦ not_exists_sixty_four_mul_pow_six_sub_one_eq ⟨p, p, x, y, hp, hp, h⟩

-- For x = -1 the left side is 63; the theorem covers negative x as well.
example (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (y : ℤ) :
    64 * (-1 : ℤ) ^ 6 - 1 ≠ (p : ℤ) ^ 3 * (q : ℤ) ^ 3 * y ^ 2 :=
  fun h ↦ not_exists_sixty_four_mul_pow_six_sub_one_eq ⟨p, q, -1, y, hp, hq, h⟩

end MathlibExt.NumberTheory.PowerfulNumbersWanted
