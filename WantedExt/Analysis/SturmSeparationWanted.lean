/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sturm separation theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.SturmSeparation` — sturm_separation (manifest `manifests/problems/sturm_separation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.SturmSeparationWanted` namespace. Mathematical
statements are unchanged. Source: C. Sturm, Mémoire sur les équations différentielles linéaires du second ordre, 1836.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MathlibExt.Analysis.SturmSeparationWanted
namespace Analysis
namespace ODE

/-!
Sturm separation theorem.

Two linearly independent (in the Wronskian sense) solutions of the second-order linear
homogeneous equation
  `y'' + p(x) y' + q(x) y = 0`
have interlacing zeros: between any two consecutive zeros of one solution lies exactly
one zero of the other.

Hypotheses are localized to an open interval `J` containing `[a, b]`.

Proof sketch: on `(a, b)` the function `f := y₂ / y₁` is well-defined (since `y₁ ≠ 0` on
the open interval) and differentiable; its derivative equals `-W / y₁²` where `W` is the
Wronskian, which has constant sign. So `f` is strictly monotone on `(a, b)`. The boundary
values force `y₂` to vanish in `(a, b)`, and strict monotonicity shows there can be at
most one such zero.
-/

/- **Sturm separation theorem.** Suppose `y₁, y₂ : ℝ → ℝ` are `C²` solutions on an open
interval `J` containing `[a, b]` of the linear homogeneous ODE `y'' + p y' + q y = 0`
with `p, q` continuous on `J`, and their Wronskian is nonzero at some point of `J`. If
`a < b ∈ J` are consecutive zeros of `y₁` (i.e. `y₁ a = y₁ b = 0` and `y₁ x ≠ 0` on
`(a, b)`), then `y₂` has exactly one zero in `(a, b)`. -/
/-- Source: C. Sturm, Mémoire sur les équations différentielles linéaires du second ordre, 1836. Via leanprover/lean-eval@38361be, problem `sturm_separation`. -/
public theorem_wanted sturm_separation
    (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0

end ODE
end Analysis

end MathlibExt.Analysis.SturmSeparationWanted
