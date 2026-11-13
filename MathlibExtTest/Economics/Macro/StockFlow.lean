/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.StockFlow
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.StockFlow` -/

namespace MathlibExtTest.Economics.Macro.StockFlow

-- Different horizon and flows from the pinned example:
-- K t = 50 + 4 * t with inflow 6, outflow 1, other change -1 at n = 3.
example : (fun t : ℕ => (50 + 4 * t : ℝ)) 3
    = (fun t : ℕ => (50 + 4 * t : ℝ)) 0 + (∑ t ∈ Finset.range 3, (6 : ℝ)) -
      (∑ t ∈ Finset.range 3, (1 : ℝ)) + (∑ t ∈ Finset.range 3, (-1 : ℝ)) := by
  have h := MathlibExt.Economics.Macro.StockFlow.stock_eq_initial_add_flows
    (K := fun t : ℕ => (50 + 4 * t : ℝ))
    (inflow := fun _ => (6 : ℝ)) (outflow := fun _ => (1 : ℝ))
    (otherChange := fun _ => (-1 : ℝ)) 3 (fun t _ => by simp; ring)
  exact h

-- A finite record: the accounting is given only for the periods `t < 2` (the path jumps to
-- `0` from period `2` on), which is all the identity at `n = 2` uses.
example : (fun t : ℕ => if t ≤ 2 then (10 + 5 * t : ℝ) else 0) 2
    = (fun t : ℕ => if t ≤ 2 then (10 + 5 * t : ℝ) else 0) 0 +
      (∑ _t ∈ Finset.range 2, (7 : ℝ)) - (∑ _t ∈ Finset.range 2, (4 : ℝ)) +
      (∑ _t ∈ Finset.range 2, (2 : ℝ)) := by
  refine MathlibExt.Economics.Macro.StockFlow.stock_eq_initial_add_flows
    (K := fun t : ℕ => if t ≤ 2 then (10 + 5 * t : ℝ) else 0)
    (inflow := fun _ => (7 : ℝ)) (outflow := fun _ => (4 : ℝ))
    (otherChange := fun _ => (2 : ℝ)) 2 (fun t ht => ?_)
  have h1 : t ≤ 2 := by omega
  have h2 : t + 1 ≤ 2 := by omega
  simp only [h1, h2, ite_true]
  push_cast
  ring

end MathlibExtTest.Economics.Macro.StockFlow
