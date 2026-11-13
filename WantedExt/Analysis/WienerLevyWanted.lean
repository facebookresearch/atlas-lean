/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wiener–Lévy theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.WienerLevy` — wiener_levy_analytic_calculus (manifest `manifests/problems/wiener_levy_analytic_calculus.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.WienerLevyWanted` namespace. Mathematical
statements are unchanged. Source: P. Lévy, Sur la convergence absolue des séries de Fourier, Compositio Math. 1 (1935), 1-14; N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.WienerLevyWanted
namespace Analysis.WienerLevy

/-!
# Wiener–Lévy theorem (analytic functional calculus)

§226 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. The
Wiener–Lévy theorem: if `φ` is complex-analytic on a neighbourhood of the
range of a Wiener-algebra function `f`, then the composition `φ ∘ f` is again
in the Wiener algebra.

mathlib has the additive circle, the Fourier characters `fourier`, Fourier
coefficients `fourierCoeff`, and `hasSum_fourier_series_of_summable`, but not
the Wiener algebra or its analytic functional calculus.
-/

open Set
open scoped ComplexConjugate Real

noncomputable section

variable {T : ℝ} [Fact (0 < T)]

/-- **Wiener algebra on the circle.** Let $T > 0$. A continuous function
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ lies in the Wiener algebra when the family of its
Fourier coefficients $\hat f(n) = \frac{1}{T} \int_0^T f(x) e^{-2\pi i n x / T} \, dx$,
$n \in \mathbb{Z}$, is summable in $\mathbb{C}$.

For complex families, summability is equivalent to $\sum_{n \in \mathbb{Z}} |\hat f(n)| < \infty$,
so these are the functions with absolutely convergent Fourier series. -/
def InWienerAlgebra (f : C(AddCircle T, ℂ)) : Prop :=
  Summable (fourierCoeff f)

/- **Wiener–Lévy theorem.** If `φ` is complex-analytic on a neighbourhood of
the range of a Wiener-algebra function `f`, then the composed function
`φ ∘ f` is again in the Wiener algebra. -/
/-- **Wiener–Lévy theorem.** Let $T > 0$, and let $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be a
continuous function in the Wiener algebra. Let $U \subseteq \mathbb{C}$ be an open set containing
the range of $f$, and let $\varphi : \mathbb{C} \to \mathbb{C}$ be analytic at every point of $U$.
Then there is a continuous function $g : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ with
$g(x) = \varphi(f(x))$ for every $x$, and $g$ lies in the Wiener algebra.

Source: P. Lévy, Sur la convergence absolue des séries de Fourier, Compositio Math. 1 (1935), 1-14; N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226. Via leanprover/lean-eval@38361be, problem `wiener_levy_analytic_calculus`. -/
public theorem_wanted wiener_levy_analytic_calculus (f : C(AddCircle T, ℂ))
    (φ : ℂ → ℂ) (U : Set ℂ) (hf : InWienerAlgebra f)
    (hU : IsOpen U) (hrange : range f ⊆ U)
    (hφ : AnalyticOnNhd ℂ φ U) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = φ (f x)) ∧ InWienerAlgebra g

end

end Analysis.WienerLevy

end MathlibExt.Analysis.WienerLevyWanted
