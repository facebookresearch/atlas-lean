/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

namespace MathlibExt.Analysis.Complex.LaurentSeriesWanted

/--
Laurent expansion on an annulus: if `f : ℂ → ℂ` is holomorphic on the annulus
`{z | r < ‖z - c‖ < R}`, then there are coefficients `a : ℤ → ℂ` such that
`f z = ∑' n : ℤ, a n * (z - c)^n` (unconditional sum) at every point of the annulus.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "Laurent series"; L. V. Ahlfors, Complex Analysis, 3rd ed.,
Ch. 5, §1.3 (the Laurent series).
-/
theorem_wanted laurentExpansion
    {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R}) :
    ∃ a : ℤ → ℂ, ∀ z ∈ {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R},
      HasSum (fun n : ℤ => a n * (z - c) ^ n) (f z)

end MathlibExt.Analysis.Complex.LaurentSeriesWanted
