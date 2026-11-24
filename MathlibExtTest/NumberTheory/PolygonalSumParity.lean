/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PolygonalSumParity

namespace MetaMathlibExt

-- The witnesses also work at different positive representatives of their classes.
example (n : ℕ) (hn : 0 < n) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      Nat.polygonalNumber 5 (x + 4) + Nat.polygonalNumber 5 (y + 8) ≡ n [MOD 2] := by
  obtain ⟨x, y, hx, hy, h⟩ := exists_polygonal_add_polygonal_modEq_two n 5 hn (by decide)
  refine ⟨x, y, hx, hy, h (x + 4) (y + 8) (by omega) (by omega) ?_ ?_⟩
  all_goals
    unfold Nat.ModEq
    omega

end MetaMathlibExt
