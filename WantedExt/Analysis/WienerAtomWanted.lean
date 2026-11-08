/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wiener's atom-detection formula

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.WienerAtom` — wiener_atom_detection (manifest `manifests/problems/wiener_atom_detection.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.WienerAtomWanted` namespace. Mathematical
statements are unchanged. Source: N. Wiener, The Fourier Integral and Certain of its Applications (1933). Listed as §66 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.WienerAtomWanted
namespace Analysis

/-!
# Wiener's atom-detection formula

§66 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For a
probability measure `μ` on the circle `𝕋 = ℝ/2πℤ` with Fourier coefficients
`μ̂_k = ∫ e^{ikx} dμ(x)`, the Cesàro average of `|μ̂_k|²` converges to the sum of
the squared masses of the atoms of `μ`:
`lim_{N→∞} (1/N) ∑_{k=1}^{N} |μ̂_k|² = ∑_{x} μ({x})²`.
The Cesàro average of squared Fourier moduli detects exactly the pure-point part
of `μ`.

mathlib provides `AddCircle`, the Fourier characters `fourier`, and related
Fourier theory for functions, but it does not package Fourier coefficients of
measures or this Wiener atom-detection theorem (`grep -rn 'Wiener' Mathlib/`
finds no result on `lim (1/N) ∑ |μ̂_k|²` for measures on the circle). The
one-line measure coefficient `fourierCoeffMeasure μ k := ∫ x, fourier k x ∂μ` is
supplied here.
-/

open MeasureTheory Filter Topology Real Complex

/-- The `k`-th Fourier coefficient of a Borel measure `μ` on the circle
`AddCircle (2π)`: `μ̂_k := ∫ exp(i k x) dμ(x)`. With mathlib's normalisation
`fourier k x = exp(2π i k x / T)`, taking `T = 2π` gives `exp(i k x)`. -/
noncomputable def fourierCoeffMeasure (μ : Measure (AddCircle (2 * Real.pi)))
    (k : ℤ) : ℂ :=
  ∫ x, fourier k x ∂μ

/- **Wiener's atom-detection formula** (§66). For a probability measure `μ` on
the circle `𝕋 = ℝ/2πℤ`, the Cesàro average of `|μ̂_k|²` for `k = 1, …, N`
converges to the sum of the squared masses of the atoms of `μ`. The right-hand
side is automatically summable: the atoms of a finite measure are at most
countable and their masses are bounded by `μ(𝕋) = 1`. -/
/-- Source: N. Wiener, The Fourier Integral and Certain of its Applications (1933). Listed as §66 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `wiener_atom_detection`. -/
public theorem_wanted wiener_atom_detection
    (μ : Measure (AddCircle (2 * Real.pi))) [IsProbabilityMeasure μ] :
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure μ k‖ ^ 2)
      atTop
      (𝓝 (∑' x : AddCircle (2 * Real.pi), ((μ {x}).toReal) ^ 2))

end Analysis

end MathlibExt.Analysis.WienerAtomWanted
