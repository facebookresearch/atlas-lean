/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Poincaré–Siegel linearisation theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.PoincareSiegel` — poincare_siegel_linearisation (manifest `manifests/problems/poincare_siegel_linearisation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.PoincareSiegelWanted` namespace. Mathematical
statements are unchanged. Source: C. L. Siegel, *Iteration of analytic functions*, Annals of Math. 43 (1942), 607-612. Earlier formal-power-series version: H. Poincaré thèse (1879). Listed as §83 (additional statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.PoincareSiegelWanted
namespace ComplexAnalysis

/-!
# Poincaré–Siegel linearisation theorem

If `f : ℂ → ℂ` is holomorphic near `0` with `f 0 = 0` and multiplier
`f'(0) = λ = e^{2πiα}` for a Diophantine `α`, then `f` is locally
analytically conjugate to the rotation `z ↦ λ z`: there is a holomorphic
germ `u(z) = z + O(z²)` with `f(u(z)) = u(λ z)` near `0` — an analytic
solution of the Schröder equation.
-/

/-- A real `α` is **Diophantine** if there are `C > 0` and `τ : ℝ` such
that `C / |q|^τ ≤ |α − p/q|` for all integers `p, q` with `q ≠ 0`. The
exponent τ is implicitly ≥ 2 by Dirichlet's theorem. This implies α is
irrational, so `e^{2πiα}` is not a root of unity. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ C τ : ℝ, 0 < C ∧ ∀ p q : ℤ, q ≠ 0 →
    C / |(q : ℝ)| ^ τ ≤ |α - (p : ℝ) / (q : ℝ)|

/- **Poincaré–Siegel linearisation theorem.** If `α` is Diophantine,
`λ = e^{2πiα}`, and `f` is holomorphic near `0` with `f 0 = 0` and
`f'(0) = λ`, then there is a holomorphic germ `u` with `u 0 = 0`,
`u'(0) = 1`, and `f(u z) = u(λ z)` for `z` near `0`. -/
/-- Source: C. L. Siegel, *Iteration of analytic functions*, Annals of Math. 43 (1942), 607-612. Earlier formal-power-series version: H. Poincaré thèse (1879). Listed as §83 (additional statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `poincare_siegel_linearisation`. -/
public theorem_wanted poincare_siegel
    (α : ℝ) (_hα : IsDiophantine α)
    (lam : ℂ) (_hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (_hf0 : f 0 = 0)
    (_hmult : deriv f 0 = lam) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (lam * z)

end ComplexAnalysis

end MathlibExt.Analysis.PoincareSiegelWanted
