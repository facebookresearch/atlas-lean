/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mandelbrot set is connected (Douady–Hubbard)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.Mandelbrot` — mandelbrot_connected (manifest `manifests/problems/mandelbrot_connected.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.MandelbrotWanted` namespace. Mathematical
statements are unchanged. Source: A. Douady and J. H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.MandelbrotWanted
namespace ComplexAnalysis
namespace MandelbrotProblem

/-!
# Mandelbrot set is connected (Douady–Hubbard)

The Mandelbrot set `M = { c ∈ ℂ | T_c^n(0) stays bounded }`, where
`T_c(z) = z² + c`, is the parameter set for which the critical orbit
of `0` under the quadratic family is bounded. Douady and Hubbard proved
in 1982 (full development 1984–85) that `M` is connected.
-/

open Function

/-- The quadratic family member `T_c(z) = z² + c`. -/
def Tc (c : ℂ) (z : ℂ) : ℂ := z ^ 2 + c

/-- The **Mandelbrot set** `M = { c ∈ ℂ | T_c^n(0) stays bounded }`. -/
def Mandelbrot : Set ℂ :=
  { c : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ M }

/- **Mandelbrot set is connected** (Douady–Hubbard). -/
/-- Source: A. Douady and J. H. Hubbard, *Étude dynamique des polynômes complexes I, II*, Publ. Math. Orsay 84-02, 85-04. Listed as §62 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `mandelbrot_connected`. -/
public theorem_wanted mandelbrot_connected : IsConnected Mandelbrot

end MandelbrotProblem
end ComplexAnalysis

end MathlibExt.Analysis.MandelbrotWanted
