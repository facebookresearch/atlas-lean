/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Sharp cell bounds for two-by-two tables with fixed margins -/

namespace MetaMathlibExt

@[expose] public section

/-- **Cell bounds from the margins of a two-by-two table.** Let $r_1,r_2$ be the row totals,
$c_1,c_2$ the column totals, and $n=r_1+r_2=c_1+c_2$. The possible top-left entries $x$ of a
nonnegative table are exactly those between $\max(0,r_1+c_1-n)$ and $\min(r_1,c_1)$, for both
natural counts and real masses. The other three entries are $r_1-x$, $c_1-x$, and
$n+x-(r_1+c_1)$, in top-right, bottom-left, and bottom-right order. For natural counts the last
subtraction is taken only after adding $x$ to $n$. The real formulation does not separately
assume nonnegative margins: either side of the equivalence implies their nonnegativity. -/
theorem two_by_two_cell_bounds :
    (∀ {r₁ r₂ c₁ c₂ x : ℕ}, r₁ + r₂ = c₁ + c₂ →
      ((∃ y z w : ℕ, x + y = r₁ ∧ z + w = r₂ ∧ x + z = c₁ ∧ y + w = c₂) ↔
        r₁ + c₁ - (r₁ + r₂) ≤ x ∧ x ≤ min r₁ c₁)) ∧
    (∀ {r₁ r₂ c₁ c₂ x : ℝ}, r₁ + r₂ = c₁ + c₂ →
      ((∃ y z w : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ 0 ≤ w ∧
        x + y = r₁ ∧ z + w = r₂ ∧ x + z = c₁ ∧ y + w = c₂) ↔
        max 0 (r₁ + c₁ - (r₁ + r₂)) ≤ x ∧ x ≤ min r₁ c₁)) := by
  constructor
  · intro r₁ r₂ c₁ c₂ x htotal
    constructor
    · rintro ⟨y, z, w, hy, hw, hz, hc₂⟩
      exact ⟨by omega, le_min (by omega) (by omega)⟩
    · rintro ⟨hlo, hhi⟩
      obtain ⟨hr, hc⟩ := le_min_iff.mp hhi
      exact ⟨r₁ - x, c₁ - x, r₁ + r₂ + x - (r₁ + c₁), by omega, by omega, by omega, by omega⟩
  · intro r₁ r₂ c₁ c₂ x htotal
    constructor
    · rintro ⟨y, z, w, hx, hy₀, hz₀, hw₀, hy, hw, hz, hc₂⟩
      exact ⟨max_le hx (by linarith), le_min (by linarith) (by linarith)⟩
    · rintro ⟨hlo, hhi⟩
      obtain ⟨hx, hlo⟩ := max_le_iff.mp hlo
      obtain ⟨hr, hc⟩ := le_min_iff.mp hhi
      exact ⟨r₁ - x, c₁ - x, r₁ + r₂ + x - (r₁ + c₁), hx, sub_nonneg.mpr hr,
        sub_nonneg.mpr hc, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end

end MetaMathlibExt
