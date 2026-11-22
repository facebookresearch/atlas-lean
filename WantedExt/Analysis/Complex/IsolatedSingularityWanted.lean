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

@[expose] public section

open Set Filter Topology Metric

namespace MathlibExt.Analysis.Complex.IsolatedSingularityWanted

/--
Classification of isolated singularities (trichotomy): if `f : ℂ → ℂ` is holomorphic on a
punctured ball around `c`, then either `f` extends to a holomorphic function on the whole
ball (removable singularity), or `‖f z‖ → ∞` as `z → c` (pole), or the image of every
punctured ball around `c` is dense in `ℂ` (essential singularity, Casorati–Weierstrass).

The essential case alone is proved as
`MathlibExt.Analysis.Complex.CasoratiWeierstrass.casoratiWeierstrass` (non-meromorphic implies
dense image); the missing content here is the meromorphic split into the removable and pole
cases and their packaging with it.

Sources: Mathlib `docs/undergrad.yaml`, section "Functions on one complex variable",
entry "isolated singularities"; L. V. Ahlfors, Complex Analysis, 3rd ed.,
Ch. 4, §3.1 and §3.2 (removable singularities; zeros, poles and the Casorati-Weierstrass
theorem).
-/
theorem_wanted isolatedSingularity_trichotomy
    {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r \ {c})) :
    (∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧
      Set.EqOn f g (Metric.ball c r \ {c})) ∨
    Filter.Tendsto (fun z => ‖f z‖) (𝓝[≠] c) Filter.atTop ∨
    ∀ r' : ℝ, 0 < r' → Dense (f '' (Metric.ball c r' \ {c}))

end MathlibExt.Analysis.Complex.IsolatedSingularityWanted
