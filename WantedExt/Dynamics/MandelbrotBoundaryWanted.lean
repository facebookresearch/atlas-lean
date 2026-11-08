/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hausdorff dimension of the Mandelbrot boundary (Shishikura)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.MandelbrotBoundary` — mandelbrot_boundary_dimh (manifest `manifests/problems/mandelbrot_boundary_dimh.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.MandelbrotBoundaryWanted` namespace. Mathematical
statements are unchanged. Source: M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. 147 (1998). Listed as §260 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §260.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.MandelbrotBoundaryWanted
namespace Dynamics.MandelbrotBoundary

/-!
# Hausdorff dimension of the Mandelbrot boundary (Shishikura)

`mandelbrot_boundary_dimh`: the boundary of the Mandelbrot set has Hausdorff
dimension `2`. The helpers `Tc` (the quadratic family `z ↦ z² + c`) and
`Mandelbrot` (the bounded critical-orbit locus) set up the statement over
mathlib's existing `dimH`. Mathlib has no complex-dynamics, Mandelbrot set, or
Shishikura dimension API. Category-(b) candidate from §260 of the Knill survey.
-/

open Function MeasureTheory

/-- The quadratic family member `T_c(z) = z² + c`. -/
def Tc (c : ℂ) (z : ℂ) : ℂ :=
  z ^ 2 + c

/-- The **Mandelbrot set** `M = { c ∈ ℂ | T_c^n(0) stays bounded }`. -/
def Mandelbrot : Set ℂ :=
  { c : ℂ | ∃ R : ℝ, ∀ n : ℕ, ‖(Tc c)^[n] 0‖ ≤ R }

/- **Shishikura's theorem** (§260). The boundary of the Mandelbrot set has
Hausdorff dimension `2`. -/
/-- Source: M. Shishikura, The Hausdorff dimension of the boundary of the Mandelbrot set and Julia sets, Ann. of Math. 147 (1998). Listed as §260 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §260. Via leanprover/lean-eval@38361be, problem `mandelbrot_boundary_dimh`. -/
public theorem_wanted mandelbrot_boundary_dimh :
    dimH (frontier Mandelbrot) = 2

end Dynamics.MandelbrotBoundary

end MathlibExt.Dynamics.MandelbrotBoundaryWanted
