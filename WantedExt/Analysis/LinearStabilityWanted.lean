/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear ODE with negative-real-part eigenvalues is asymptotically stable

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.LinearStability` — linear_ode_asymptotic_stability (manifest `manifests/problems/linear_ode_asymptotic_stability.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.LinearStabilityWanted` namespace. Mathematical
statements are unchanged. Source: Classical linear stability theory; Hirsch-Smale-Devaney.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

namespace MathlibExt.Analysis.LinearStabilityWanted
namespace Analysis
namespace ODE

/-!
Linear stability of `x' = A x` when every eigenvalue of `A` has negative real part.

For `A : Matrix (Fin n) (Fin n) ℂ` such that every (complex) eigenvalue `μ` of `A`
satisfies `μ.re < 0`, every solution of `x' = A x` decays to zero in norm.

Stating this in real coordinates uses the embedding `A : Matrix (Fin n) (Fin n) ℝ ↪
Matrix (Fin n) (Fin n) ℂ` and asks about the *complex* eigenvalues. The proof requires
the matrix exponential, the Jordan / triangularisation form, and a uniform bound of the
form `‖exp (t A)‖ ≤ C · exp(α t)` for some `α < 0`.
-/

open scoped Matrix

/- **Asymptotic stability of a linear ODE with eigenvalues in the open left half-plane.**

Let `A : Matrix (Fin n) (Fin n) ℝ`. Suppose every (complex) eigenvalue of the
complexification of `A` has strictly negative real part. Then every solution of the
linear ODE `x'(t) = A · x(t)` tends to `0` in norm as `t → ∞`. -/
/-- **Asymptotic stability of linear ODEs with eigenvalues in the open left half-plane.** Let
$n \ge 0$ and let $A$ be a real $n \times n$ matrix such that every complex eigenvalue $\mu$ of $A$
(an eigenvalue of $A$ viewed as a complex matrix acting on $\mathbb{C}^n$) satisfies
$\operatorname{Re} \mu < 0$. Let $x : \mathbb{R} \to \mathbb{R}^n$ be a function that, at every
$t > 0$, is differentiable with derivative $x'(t) = A\,x(t)$. Then $\|x(t)\| \to 0$ as
$t \to \infty$, where $\|\cdot\|$ is the sup norm on $\mathbb{R}^n$.

Source: Classical linear stability theory; Hirsch-Smale-Devaney. Via leanprover/lean-eval@38361be, problem `linear_ode_asymptotic_stability`. -/
public theorem_wanted linear_ode_asymptotic_stability
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0)

end ODE
end Analysis

end MathlibExt.Analysis.LinearStabilityWanted
