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

/-- The unnormalised cardinal sine, with the removable singularity filled by
the standard value `1`.  Knill writes `sinc x = sin x / x`; the reconstruction
formula evaluates this at `0` when `t` is an integer, so the total version is
the faithful formal spelling. -/
noncomputable def sinc (x : ℝ) : ℂ :=
  if x = 0 then 1 else ((Real.sin x / x : ℝ) : ℂ)

/-- The Fourier transform of `f` is supported in the Nyquist band for
mathlib's `e^{-2π i x ξ}` Fourier convention, namely `[-1/2, 1/2]`. -/
def FourierSupportedInNyquist (f : 𝓢(ℝ, ℂ)) : Prop :=
  ∀ ξ : ℝ, ξ ∉ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) → 𝓕 f ξ = 0

/-- **Nyquist--Shannon sampling theorem / Whittaker--Shannon interpolation
formula** for Schwartz functions with Fourier support in the mathlib-convention
Nyquist band `[-1/2, 1/2]`.

The explicit `Summable` conjunct records the convergence content of the
cardinal series, rather than relying only on Lean's total `tsum`.
Source: C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179. Via leanprover/lean-eval@38361be, problem `nyquist_shannon_sampling`.
-/
public theorem_wanted nyquist_shannon_sampling (f : 𝓢(ℝ, ℂ)) (hf : FourierSupportedInNyquist f) :
    ∀ t : ℝ,
      Summable (fun n : ℤ ↦ f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))) ∧
        f t =
          ∑' n : ℤ, f (n : ℝ) * sinc (Real.pi * ((n : ℝ) - t))

end Analysis.NyquistShannon

end MathlibExt.Analysis.NyquistShannonWanted
