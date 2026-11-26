/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic properties of Bond comminution energy

For positive sizes and a common work index, the stipulated inverse-square-root
energy law telescopes across consecutive size reductions. The equation is taken
as a model, not derived from particle mechanics.
-/

namespace Domains.Chemistry.MineralProcessing.BondEnergy

/-- For the stipulated Bond equation, nonnegative energy is equivalent to the product
size not exceeding the feed size. Energies telescope across stages with one work index.
Dividing sizes by a million converts micrometres to metres and changes the numerical
size coefficient from `10` to `1 / 100`. Scaling energy and the work index together by
`1000 / 907.18474` changes their mass basis from a US short ton to a metric tonne.

Source for the equation: F. C. Bond, basic work-index equation as reproduced in
[Bond Work Index Formula-Equation](https://www.911metallurgist.com/blog/bond-work-index-formula-equation/).
The conclusions concern this equation, not its empirical accuracy. -/
public theorem bond_energy_identities (wi feed middle product : ℝ) (hwi : 0 < wi)
    (hfeed : 0 < feed) (_hmiddle : 0 < middle) (hproduct : 0 < product) :
    let energy (w f p : ℝ) := 10 * w * (1 / Real.sqrt p - 1 / Real.sqrt f)
    (0 ≤ energy wi feed product ↔ product ≤ feed) ∧
    energy wi feed middle + energy wi middle product = energy wi feed product ∧
    energy wi feed product = (1 / 100) * wi *
      (1 / Real.sqrt (product / 1000000) - 1 / Real.sqrt (feed / 1000000)) ∧
    (1000 / 907.18474) * energy wi feed product =
      energy ((1000 / 907.18474) * wi) feed product := by
  dsimp only
  have hsf : 0 < Real.sqrt feed := Real.sqrt_pos.2 hfeed
  have hsp : 0 < Real.sqrt product := Real.sqrt_pos.2 hproduct
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 10) hwi),
      sub_nonneg, div_le_div_iff₀ hsf hsp, one_mul, one_mul]
    exact Real.sqrt_le_sqrt_iff hfeed.le
  · ring
  · have hs : Real.sqrt (1000000 : ℝ) = 1000 := by
      convert Real.sqrt_sq (show 0 ≤ (1000 : ℝ) by norm_num) using 1
      norm_num
    rw [Real.sqrt_div hproduct.le, Real.sqrt_div hfeed.le, hs]
    field_simp [ne_of_gt hsf, ne_of_gt hsp]
    ring
  · ring

end Domains.Chemistry.MineralProcessing.BondEnergy
