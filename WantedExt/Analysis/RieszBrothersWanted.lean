/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Riesz brothers' theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.RieszBrothers` — riesz_brothers_theorem (manifest `manifests/problems/riesz_brothers_theorem.toml`, rev 1, submitter Yongxi Lin, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RieszBrothersWanted` namespace. Mathematical
statements are unchanged. Source: W. Rudin, Real and Complex Analysis; N. K. Nikolski, Operators, Functions, and Systems: An Easy Reading, Volume I: Hardy, Hankel, and Toeplitz.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.VectorMeasure.Integral

@[expose] public section

namespace MathlibExt.Analysis.RieszBrothersWanted
namespace Analysis

/-!
# Riesz brothers' theorem

The Riesz brothers' theorem says that a complex Borel measure on the circle
whose positive analytic moments vanish is absolutely continuous with respect to
Haar measure.

-/

open MeasureTheory

/- **Riesz brothers' theorem.** Let `μ` be a complex Borel measure on
the unit circle such that `∫ z^n dμ = 0` for every `n ≥ 1`. Then `μ` is
absolutely continuous with respect to Haar measure. The usual density
formulation follows by applying the Radon–Nikodym theorem to this conclusion;
the hypothesis transfers the Fourier-vanishing property to that density. This
corollary is not part of the formal statement here. -/
/-- **F. and M. Riesz theorem.** Let $\mu$ be a complex Borel measure on the circle
$\mathbb{T} = \mathbb{R}/\mathbb{Z}$. If $\int_{\mathbb{T}} e^{2\pi i n z} \, d\mu(z) = 0$ for
every integer $n \ge 1$, then $\mu$ is absolutely continuous with respect to the Haar probability
measure on $\mathbb{T}$.

Source: W. Rudin, Real and Complex Analysis; N. K. Nikolski, Operators, Functions, and Systems: An Easy Reading, Volume I: Hardy, Hankel, and Toeplitz. Via leanprover/lean-eval@38361be, problem `riesz_brothers_theorem`. -/
public theorem_wanted riesz_brothers_theorem (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n → ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0) :
    μ ≪ᵥ AddCircle.haarAddCircle.toENNRealVectorMeasure

end Analysis

end MathlibExt.Analysis.RieszBrothersWanted
