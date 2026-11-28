/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GridLRamseyThree1804

/-! # The 1804 bound for colorings defined on the one-based finite board -/

namespace MetaMathlibExt.gridLRamseyProperty_three_1804

private abbrev Coord := Set.Icc (1 : ℕ) 1804

example (c : Coord × Coord → Fin 3) :
    ∃ x y u v : Coord, ∃ d : ℕ, 0 < d ∧ (x : ℕ) + d = u ∧ (y : ℕ) + d = v ∧
      c (x, y) = c (u, y) ∧ c (u, y) = c (u, v) := by
  let coord (t : ℕ) : Coord := ⟨max 1 (min t 1804), by constructor <;> omega⟩
  obtain ⟨x, y, d, hx, hy, hd, hxd, hyd, h₁, h₂⟩ :=
    gridLRamseyProperty_three_1804 fun (a, b) => c (coord a, coord b)
  have leg (t : ℕ) (ht : 0 < t) (htd : t + d ≤ 1804) :
      (coord t : ℕ) + d = coord (t + d) := by
    change max 1 (min t 1804) + d = max 1 (min (t + d) 1804)
    omega
  exact ⟨coord x, coord y, coord (x + d), coord (y + d), d, hd, leg x hx hxd, leg y hy hyd, h₁, h₂⟩

end MetaMathlibExt.gridLRamseyProperty_three_1804
