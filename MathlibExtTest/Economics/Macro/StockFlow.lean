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
-- K t = 50 + 4 * t with inflow 6, outflow 1, valuation -1 at n = 3.
example : (fun t : ℕ => (50 + 4 * t : ℝ)) 3
    = (fun t : ℕ => (50 + 4 * t : ℝ)) 0 + (∑ t ∈ Finset.range 3, (6 : ℝ)) -
      (∑ t ∈ Finset.range 3, (1 : ℝ)) + (∑ t ∈ Finset.range 3, (-1 : ℝ)) := by
  have h := MathlibExt.Economics.Macro.StockFlow.stock_eq_initial_add_flows
    (K := fun t : ℕ => (50 + 4 * t : ℝ))
    (inflow := fun _ => (6 : ℝ)) (outflow := fun _ => (1 : ℝ))
    (valuation := fun _ => (-1 : ℝ)) (fun t => by simp; ring) 3
  exact h

end MathlibExtTest.Economics.Macro.StockFlow
