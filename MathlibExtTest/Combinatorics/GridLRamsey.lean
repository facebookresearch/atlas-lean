/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GridLRamsey
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases

/-! # Tests for monochromatic L-shapes in grid colorings -/

namespace MetaMathlibExt.exists_mono_L_of_forced_blue_diagonal

-- Three forced blue points suffice on the 4 × 4 grid, even when every other
-- point below their diagonal has the third color.
example :
    let c : ℕ × ℕ → Fin 3 := fun (x, y) => if x = y then 0 else if x = y + 1 then 1 else 2
    ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ 4 ∧ y + d ≤ 4 ∧
      c (x, y) = c (x + d, y) ∧ c (x + d, y) = c (x + d, y + d) := by
  intro c
  exact exists_mono_L_of_forced_blue_diagonal 4 (by decide) c 0 1 (by decide) 1 (by decide)
    {1, 2, 3} (by dsimp only [c]; decide) (by decide)

-- At equality in the pair count, the 3 × 3 coloring from the statement has no monochromatic L.
private def boundaryColor : ℕ × ℕ → Fin 3
  | (3, 1) => 2
  | (2, 1) | (3, 2) | (2, 3) => 1
  | _ => 0

example :
    let X : Finset ℕ := {1, 2}
    X.card.choose 2 = 3 - 2 ∧
      (∀ x ∈ X, 0 < x ∧ x + 1 ≤ 3 ∧ boundaryColor (x + 1, x) = 1 ∧
        boundaryColor (x, x) = 0 ∧ boundaryColor (x + 1, x + 1) = 0) ∧
      ¬ ∃ x y d : ℕ, 0 < x ∧ 0 < y ∧ 0 < d ∧ x + d ≤ 3 ∧ y + d ≤ 3 ∧
        boundaryColor (x, y) = boundaryColor (x + d, y) ∧
        boundaryColor (x + d, y) = boundaryColor (x + d, y + d) := by
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨x, y, d, hx, hy, hd, hxd, hyd, h₁, h₂⟩
  have : x ≤ 2 := by omega
  have : y ≤ 2 := by omega
  have : d ≤ 2 := by omega
  interval_cases x <;> interval_cases y <;> interval_cases d
    <;> simp +decide at *

end MetaMathlibExt.exists_mono_L_of_forced_blue_diagonal

namespace MetaMathlibExt.exists_gridLRamseyProperty

-- In a grid whose columns cycle through the k colors, each monochromatic L has k ∣ d.
-- Thus even the least grid size supplied by the theorem must exceed k.
open scoped Classical in
example (k : ℕ) (hk : 0 < k) : k < Nat.find (exists_gridLRamseyProperty k hk) := by
  have hn := (Nat.find_spec (exists_gridLRamseyProperty k hk)).2
  let stripes (p : ℕ × ℕ) : Fin k := ⟨p.1 % k, Nat.mod_lt _ hk⟩
  obtain ⟨x, y, d, hx, _, hd, hxd, _, hcolor, _⟩ := hn stripes
  have hmod : x ≡ x + d [MOD k] := congrArg Fin.val hcolor
  have hkd := Nat.le_of_dvd hd (Nat.left_modEq_add_iff.mp hmod)
  omega

end MetaMathlibExt.exists_gridLRamseyProperty
