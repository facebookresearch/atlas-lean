/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PracticalPolygonalSumsEventuallyTwo

namespace MetaMathlibExt

-- The smallest allowed value of `s` gives sums with two squares.
example : ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
    IsPracticalNumber q ∧ n = q + x ^ 2 + y ^ 2 := by
  simpa only [Nat.polygonalNumber_four] using eventually_practical_add_two_polygonal 4 (by decide)

-- At an odd value of `s`, both summands have the pentagonal closed form.
example : ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
    IsPracticalNumber q ∧ n = q + (3 * x ^ 2 - x) / 2 + (3 * y ^ 2 - y) / 2 := by
  simpa only [Nat.polygonalNumber_five] using eventually_practical_add_two_polygonal 5 (by decide)

end MetaMathlibExt
