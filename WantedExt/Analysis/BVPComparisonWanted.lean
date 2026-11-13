/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Comparison principle for the Dirichlet BVP

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.BVPComparison` — bvp_comparison (manifest `manifests/problems/bvp_comparison.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.BVPComparisonWanted` namespace. Mathematical
statements are unchanged. Source: Standard maximum-principle argument; Protter-Weinberger.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MathlibExt.Analysis.BVPComparisonWanted
namespace Analysis
namespace ODE

/-!
Comparison principle for the second-order Dirichlet boundary value problem.

If `u, v` are `C²` on an open interval `J` containing `[0, 1]` and satisfy
  `-u''(x) ≤ -v''(x)` on `(0, 1)`,
together with the boundary inequalities `u 0 ≤ v 0` and `u 1 ≤ v 1`, then `u ≤ v` on
`[0, 1]`.

This is the simplest 1D maximum principle. Direct convex argument: `(u - v)'' ≥ 0` on
`(0, 1)` so `u - v` is convex on `[0, 1]`, hence bounded above by its chord, which is
non-positive at the endpoints. A perturbation proof: `ψ := (u - v) - δ x(1 - x)` is
strictly convex (`ψ'' ≥ 2δ > 0`); a strictly convex function attains its supremum at the
boundary, where `ψ ≤ 0`; let `δ → 0`.
-/

/- **Comparison principle for the Dirichlet BVP.** If two functions are `C²` on an open
interval `J` containing `[0, 1]`, satisfy `-u'' ≤ -v''` on the interior, and are ordered
at the boundary, then `u ≤ v` throughout `[0, 1]`. -/
/-- **Comparison principle for the Dirichlet problem on $[0, 1]$.** Let $J \subseteq \mathbb{R}$
be an open set containing $[0, 1]$, and let $u, v : \mathbb{R} \to \mathbb{R}$ be functions
that are differentiable at every point of $J$ and whose derivatives $u'$ and $v'$ are
differentiable at every point of $J$. If $-u''(x) \le -v''(x)$ for every $x \in (0, 1)$,
$u(0) \le v(0)$ and $u(1) \le v(1)$, then $u(x) \le v(x)$ for every $x \in [0, 1]$.

Source: Standard maximum-principle argument; Protter-Weinberger. Via leanprover/lean-eval@38361be, problem `bvp_comparison`. -/
public theorem_wanted bvp_comparison
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x

end ODE
end Analysis

end MathlibExt.Analysis.BVPComparisonWanted
