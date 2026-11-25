/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.GridLRamseyThree772

/-! # The three-color L bound on a zero-based finite grid -/

namespace MetaMathlibExt.gridLRamseyProperty_three_772

-- A coloring defined only on the finite board has witnesses with ordinary, nonwrapping offsets.
example (c : Fin 772 × Fin 772 → Fin 3) :
    ∃ x y u v : Fin 772, ∃ d : ℕ, 0 < d ∧ x.val + d = u.val ∧ y.val + d = v.val ∧
      c (x, y) = c (u, y) ∧ c (u, y) = c (u, v) := by
  let idx (t : ℕ) := Fin.ofNat 772 (t - 1)
  obtain ⟨x, y, d, hx, hy, hd, hxd, hyd, h₁, h₂⟩ :=
    gridLRamseyProperty_three_772 fun (a, b) => c (idx a, idx b)
  have offset (t : ℕ) (ht : 0 < t) (htd : t + d ≤ 772) :
      (idx t).val + d = (idx (t + d)).val := by
    change (t - 1) % 772 + d = (t + d - 1) % 772
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨idx x, idx y, idx (x + d), idx (y + d), d, hd, offset x hx hxd, offset y hy hyd, h₁, h₂⟩

end MetaMathlibExt.gridLRamseyProperty_three_772
