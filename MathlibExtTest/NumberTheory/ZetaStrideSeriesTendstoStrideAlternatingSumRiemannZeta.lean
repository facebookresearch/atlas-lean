/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta
import Mathlib.Tactic.NormNum

/-!
# Tests for the alternating stride sum series

Concrete stride sums and instances of convergence to the Riemann zeta function.
-/

namespace MathlibExtTest.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta

open Filter Topology

example : MetaMathlibExt.strideAlternatingSum 2 1 4 = -(1 / 4 : ℝ) := by
  norm_num [MetaMathlibExt.strideAlternatingSum, Finset.sum_range_succ]

example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (2 * ((n : ℝ) + 1) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
      MetaMathlibExt.strideAlternatingSum 1 1 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 2)) := by
  convert MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta
    1 1 (by decide) (by decide) using 1 <;> norm_num [add_assoc]

example : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
    (2 * ((n : ℝ) + 1) + 3) / (((n : ℝ) + 1) * ((n : ℝ) + 4)) *
      MetaMathlibExt.strideAlternatingSum 3 2 (n + 1) : ℝ) : ℂ))
    atTop (𝓝 (riemannZeta 3)) := by
  convert MetaMathlibExt.tendsto_strideAlternatingSum_riemannZeta
    3 2 (by decide) (by decide) using 1 <;> norm_num [add_assoc]

end MathlibExtTest.NumberTheory.ZetaStrideSeriesTendstoStrideAlternatingSumRiemannZeta
