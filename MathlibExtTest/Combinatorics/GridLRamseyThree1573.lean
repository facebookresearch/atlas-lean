/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GridLRamseyThree1573
import Mathlib.Order.Interval.Set.ProjIcc

/-! # The 1573 bound for a coloring defined only on the finite board -/

namespace MetaMathlibExt.gridLRamseyProperty_three_1573

private abbrev Coord := Set.Icc (1 : ℕ) 1573

example (c : Coord × Coord → Fin 3) :
    ∃ x y u v : Coord, ∃ d : ℕ, 0 < d ∧ (x : ℕ) + d = u ∧ (y : ℕ) + d = v ∧
      c (x, y) = c (u, y) ∧ c (u, y) = c (u, v) := by
  let coord := Set.projIcc (1 : ℕ) 1573 (by decide)
  obtain ⟨x, y, d, hx, hy, hd, hxd, hyd, h₁, h₂⟩ :=
    gridLRamseyProperty_three_1573 fun (a, b) => c (coord a, coord b)
  have leg (t : ℕ) (ht : 0 < t) (htd : t + d ≤ 1573) :
      (coord t : ℕ) + d = coord (t + d) := by
    simp only [coord, Set.coe_projIcc]
    omega
  exact ⟨coord x, coord y, coord (x + d), coord (y + d), d, hd, leg x hx hxd, leg y hy hyd, h₁, h₂⟩

end MetaMathlibExt.gridLRamseyProperty_three_1573
