/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pointwise and Cesàro convergence of Fourier series (Dirichlet, Fejér)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FourierConvergence` — fourier_dirichlet_fejer (manifest `manifests/problems/fourier_dirichlet_fejer.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FourierConvergenceWanted` namespace. The
definitions `fourierPartialSum` and `fourierCesaroMean` and the proved Fejér statement moved to
`MathlibExt.Analysis.Fourier.Fejer`. Mathematical
statements are unchanged. Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Analysis.Fourier.Fejer

@[expose] public section

namespace MathlibExt.Analysis.FourierConvergenceWanted
namespace Analysis

/-!
# Pointwise and Cesàro convergence of Fourier series

§46 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Dirichlet's pointwise convergence theorem** (main): for a `C¹` 2π-periodic
  complex function `f`, the symmetric Fourier partial sums
  `S_N(f)(x) = ∑_{n = -N}^{N} f̂_n e^{inx}` converge to `f(x)` at every `x ∈ ℝ`.
* **Fejér's theorem** (additional): for a merely *continuous* 2π-periodic `f`,
  the Cesàro means `σ_N(f) = (S_0 + ⋯ + S_N)/(N+1)` of the partial sums converge
  to `f` uniformly on `ℝ`. It is proved as
  `MathlibExt.Analysis.Fourier.tendstoUniformly_fourierCesaroMean`, next to the
  definitions `fourierPartialSum` and `fourierCesaroMean`.

mathlib has the circle, the Fourier characters, `fourierCoeffOn`, the `L²`
Fourier series, and uniform convergence under `ℓ¹`-summability
(`hasSum_fourier_series_of_summable`). It has neither the Dirichlet kernel nor
the statement that `C¹` forces pointwise convergence of the symmetric partial
sums — the `C¹` bound `|f̂_n| ≤ C/n` is not `ℓ¹`-summable, so the summable case
does not apply — and it has no Fejér kernel, Cesàro means, or Fejér theorem. The
symmetric partial-sum order `Finset.Icc (-N) N` is essential, since the Fourier
series of a `C¹` function need not converge absolutely.
-/

open Filter Topology MathlibExt.Analysis.Fourier

/- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
/-- Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fourier_dirichlet_fejer`. -/
public theorem_wanted dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x))

end Analysis

end MathlibExt.Analysis.FourierConvergenceWanted
