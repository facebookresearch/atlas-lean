/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/ODE/BVPComparison.lean` (leanprover/lean-eval), at commit
38361be884302c7edce1908c4aef8296eb2cb27e, for the statement of `bvp_comparison`
(manifest `manifests/problems/bvp_comparison.toml`, rev 1, submitter Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

lean-eval ships no `NOTICE` file. ATLAS converted the benchmark theorem into a wanted
declaration in the `MathlibExt.Analysis.BVPComparisonWanted` namespace and restated its
docstring. The statement moved from `WantedExt/Analysis/BVPComparisonWanted.lean` when
ATLAS added the proof.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-!
# Comparison principle for the Dirichlet problem on the unit interval

The second derivative inequality makes the difference of the two functions convex.
Its maximum on the closed interval is therefore attained at an endpoint.
-/

public section

namespace MathlibExt.Analysis.BVPComparisonWanted.Analysis.ODE

open Set

set_option linter.dupNamespace false in
/-- **Comparison principle for the Dirichlet problem on $[0, 1]$.** Let $J \subseteq \mathbb{R}$
be an open set containing $[0, 1]$, and let $u, v : \mathbb{R} \to \mathbb{R}$ be functions
that are differentiable at every point of $J$ and whose derivatives $u'$ and $v'$ are
differentiable at every point of $J$. If $-u''(x) \le -v''(x)$ for every $x \in (0, 1)$,
$u(0) \le v(0)$ and $u(1) \le v(1)$, then $u(x) \le v(x)$ for every $x \in [0, 1]$.

Source: Standard maximum-principle argument; Protter-Weinberger. Via
leanprover/lean-eval@38361be, problem `bvp_comparison`. -/
theorem bvp_comparison
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x := by
  have hcont : ContinuousOn (u - v) J :=
    hJ_open.continuousOn_iff.mpr fun x hx ↦ ((hu x hx).sub (hv x hx)).continuousAt
  have hsub : Ioo (0 : ℝ) 1 ⊆ J := Ioo_subset_Icc_self.trans hJ_sub
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (u - v) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc ..) (hcont.mono hJ_sub)
      (f' := deriv u - deriv v) (f'' := deriv (deriv u) - deriv (deriv v))
    all_goals rw [interior_Icc]
    · exact fun x hx ↦ ((hu x (hsub hx)).sub (hv x (hsub hx))).hasDerivWithinAt
    · exact fun x hx ↦ ((hu' x (hsub hx)).sub (hv' x (hsub hx))).hasDerivWithinAt
    · exact fun x hx ↦ sub_nonneg.mpr (neg_le_neg_iff.mp (hineq x hx))
  intro x hx
  have hmax := hconv.le_max_of_mem_Icc (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr zero_le_one) hx
  exact sub_nonpos.mp (hmax.trans (max_le (sub_nonpos.mpr hu0) (sub_nonpos.mpr hu1)))

end MathlibExt.Analysis.BVPComparisonWanted.Analysis.ODE
