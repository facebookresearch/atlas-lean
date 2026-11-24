/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.LinearCongruenceSolutions

namespace MetaMathlibExt

-- The two representatives for `-4 * x ≡ -2 [ZMOD 6]` are `2` and `5`.
example : ((Finset.range 6).filter fun x : ℕ => (-4 : ℤ) * x ≡ -2 [ZMOD 6]).card = 2 :=
  (linear_congruence_solutions (a := -4) (b := -2) (m := 6) (hm := by decide)).2.1 (by decide)

-- A negative translation index still gives a nonnegative representative modulo the gcd.
example : ∃ u : ℕ, u < 2 ∧ (-4 : ℤ) ≡ -1 + u * 3 [ZMOD 6] :=
  ((linear_congruence_solutions (-4) (-2) 6 (by decide)).2.2 (-1) (by decide) (-4)).mp (by decide)

example : (-4 : ℤ) * 5 ≡ -2 [ZMOD 6] :=
  ((linear_congruence_solutions (-4) (-2) 6 (by decide)).2.2 (-1) (by decide) 5).mpr
    ⟨0, by decide, by decide⟩

example : ¬ ∃ x : ℤ, (-4 : ℤ) * x ≡ -3 [ZMOD 6] :=
  fun h => (by decide : ¬ (2 : ℤ) ∣ -3)
    ((linear_congruence_solutions (-4) (-3) 6 (by decide)).1.mp h)

-- A zero coefficient gives all representatives when the modulus divides the right-hand side.
example : ((Finset.range 4).filter fun x : ℕ => (0 : ℤ) * x ≡ -8 [ZMOD 4]).card = 4 :=
  (linear_congruence_solutions 0 (-8) 4 (by decide)).2.1 (by decide)

example : ((Finset.range 1).filter fun x : ℕ => (-7 : ℤ) * x ≡ -5 [ZMOD 1]).card = 1 :=
  (linear_congruence_solutions (-7) (-5) 1 (by decide)).2.1 (by decide)

end MetaMathlibExt
