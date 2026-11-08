/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Weak Morse inequalities

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.WeakMorseInequality` — weak_morse_inequality (manifest `manifests/problems/weak_morse_inequality.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.WeakMorseInequalityWanted` namespace. Mathematical
statements are unchanged. Source: M. Morse, The Calculus of Variations in the Large, AMS Colloq. Publ. 18 (1934). Listed as §40 additional statement in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.MorseTheoryShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.MorseTheoryShared

open scoped ContDiff

namespace MathlibExt.Geometry.WeakMorseInequalityWanted
namespace Geometry
namespace WeakMorseInequality

/-!
# Weak Morse inequalities

§40 of Knill's *Some Fundamental Theorems in Mathematics* (an additional
statement of the section; the boxed main theorem is the strong Morse
inequality). For a Morse function `f` on a closed smooth finite-dimensional
manifold `M`,

`b_k(M) ≤ c_k(f)` for every `k`,

i.e. the `k`-th Betti number is bounded by the number of Morse-index-`k`
critical points. Follows from the strong Morse inequality but is often
proved directly via the Morse-Smale CW structure.

mathlib has the smooth-manifold framework, `mfderiv`, higher Fréchet
derivatives, and `singularHomologyFunctor` but no Morse functions, Morse
index, critical-point counts, Betti numbers (as a named definition), or
the weak Morse inequality. The Challenge ships seven helper definitions.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory

/- A point `x ∈ M` is a **critical point** of `f` if `mfderiv f x = 0`. -/
/- **Local Hessian** of `f` at `x`, in the preferred extended chart. -/
/- A critical point `x` is **non-degenerate** when the local Hessian has
trivial radical. -/
/- A **Morse function** on `M` is `C^∞`, has finitely many critical points,
and every critical point is non-degenerate. -/
/- The **Morse index** of `f` at `x`. -/
/- `morseCount f k = c_k(f)`. -/
/- `b_k(M) := dim_ℝ H_k(M; ℝ)`. -/
/- **Weak Morse inequalities.** For a Morse function `f` on a closed
smooth finite-dimensional Hausdorff manifold `M` and every `k ∈ ℕ`,
`b_k(M) ≤ c_k(f)`. -/
/-- Source: M. Morse, The Calculus of Variations in the Large, AMS Colloq. Publ. 18 (1934). Listed as §40 additional statement in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `weak_morse_inequality`. -/
public theorem_wanted weak_morse_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] (f : M → ℝ) (_hf : IsMorseFunction I f) (k : ℕ) :
    bettiNumber M k ≤ morseCount I f k

end WeakMorseInequality
end Geometry

end MathlibExt.Geometry.WeakMorseInequalityWanted
