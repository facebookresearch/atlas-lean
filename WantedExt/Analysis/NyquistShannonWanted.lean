/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nyquist–Shannon sampling theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.NyquistShannon` — nyquist_shannon_sampling (manifest `manifests/problems/nyquist_shannon_sampling.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.NyquistShannonWanted` namespace. Mathematical
statements are unchanged. Source: C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.NyquistShannonWanted
namespace Analysis.NyquistShannon

/-!
# Nyquist–Shannon sampling theorem

`nyquist_shannon_sampling`: a Schwartz function whose Fourier transform is
supported in the Nyquist band `[-1/2, 1/2]` (mathlib's `e^{-2π i x ξ}`
convention) is reconstructed from its integer samples by the Whittaker–Shannon
cardinal series `f(t) = ∑_{n : ℤ} f(n) * sinc(π(n - t))`. Trusted helpers
(`sinc`, `FourierSupportedInNyquist`) are non-holes. Mathlib has Schwartz space,
the Fourier transform, inversion, Plancherel and Poisson summation, but not the
sampling theorem. Category-(b) candidate from §179 of the Knill survey.
-/

open scoped FourierTransform SchwartzMap
open Set

/-- **Unnormalised cardinal sine.** The function $\operatorname{sinc} \colon \mathbb{R} \to
\mathbb{C}$ is defined by $\operatorname{sinc}(x) = \frac{\sin x}{x}$ for $x \neq 0$ and
$\operatorname{sinc}(0) = 1$, the value that removes the singularity at $0$. Its values are real.

The Whittaker–Shannon interpolation formula evaluates $\operatorname{sinc}$ at $0$ at the integer
sample points, so the value at $0$ is part of the definition. -/
noncomputable def sinc (x : ℝ) : ℂ :=
  if x = 0 then 1 else ((Real.sin x / x : ℝ) : ℂ)

/-- **Fourier support in the Nyquist band.** A Schwartz function
$f \colon \mathbb{R} \to \mathbb{C}$ has Fourier support in the Nyquist band when its Fourier
transform $\hat f(\xi) = \int_{\mathbb{R}} f(x)\, e^{-2\pi i x \xi}\, dx$ vanishes at every real
$\xi$ outside the closed interval $[-\frac12, \frac12]$. -/
def FourierSupportedInNyquist (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) → 𝓕 f ξ = 0

/-- **Nyquist–Shannon sampling theorem (Whittaker–Shannon interpolation formula).** Let
$\operatorname{sinc}(x) = \frac{\sin x}{x}$ for real $x \neq 0$ and $\operatorname{sinc}(0) = 1$,
and let $f \colon \mathbb{R} \to \mathbb{C}$ be a Schwartz function whose Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} f(x)\, e^{-2\pi i x \xi}\, dx$ vanishes at every real $\xi$
outside $[-\frac12, \frac12]$. Then for every real $t$ the series
$\sum_{n \in \mathbb{Z}} f(n) \operatorname{sinc}(\pi(n - t))$ is summable over $\mathbb{Z}$
(unconditionally convergent) and
$$
f(t) = \sum_{n \in \mathbb{Z}} f(n) \operatorname{sinc}(\pi(n - t)).
$$

Source: C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179. Via leanprover/lean-eval@38361be, problem `nyquist_shannon_sampling`.
-/
public theorem_wanted nyquist_shannon_sampling (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f) :
    ∀ t : ℝ,
      Summable (fun n : ℤ ↦ f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))) ∧
        f t =
          ∑' n : ℤ, f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))

end Analysis.NyquistShannon

end MathlibExt.Analysis.NyquistShannonWanted
