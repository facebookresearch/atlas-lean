/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Morse inequalities

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.MorseInequalities` — morse_inequality (manifest `manifests/problems/morse_inequality.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.MorseInequalitiesWanted` namespace. Mathematical
statements are unchanged. Source: M. Morse, The Calculus of Variations in the Large, AMS Colloq. Publ. 18 (1934). Listed as §40 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.MorseTheoryShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.MorseTheoryShared

open scoped ContDiff

namespace MathlibExt.Geometry.MorseInequalitiesWanted
namespace Geometry
namespace MorseInequalities

/-!
# Morse inequalities (Marston Morse, 1934)

§40 of Knill's *Some Fundamental Theorems in Mathematics*. For a Morse
function `f` on a closed smooth finite-dimensional manifold `M`,

`∑_{j≤k} (−1)^{k−j} c_j(f) ≥ ∑_{j≤k} (−1)^{k−j} b_j(M)`

for every `k`, where `c_j` is the number of critical points of `f` of Morse
index `j` and `b_j` is the `j`-th Betti number of `M`.

mathlib has the smooth-manifold framework, `mfderiv`, higher Fréchet
derivatives, and `singularHomologyFunctor` — but no Morse functions, Morse
index, critical-point counts, Betti numbers (as a named definition), or
the Morse inequalities. The Challenge ships seven helper definitions
(`IsCriticalPoint`, `localHessian`, `IsNondegenerateCritical`,
`IsMorseFunction`, `morseIndex`, `morseCount`, `bettiNumber`,
`alternatingPartialSum`) on top of mathlib.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory


/- A point `x ∈ M` is a **critical point** of `f` if `mfderiv f x = 0`. -/
/- **Local Hessian** of `f` at `x`, in the preferred extended chart. -/
/- A critical point `x` is **non-degenerate** when the local Hessian, viewed
as a symmetric bilinear form on `E`, has trivial radical. -/
/- A **Morse function** on `M` is `C^∞`, has finitely many critical points,
and every critical point is non-degenerate. -/
/- The **Morse index** of `f` at `x` — the supremum of dimensions of
subspaces of `E` on which the local Hessian is negative-definite. -/
/- `morseCount f k` is the number `c_k(f)` of Morse-index-`k` critical points. -/
/- `b_k(M) := dim_ℝ H_k(M; ℝ)`, the `k`-th Betti number with real
coefficients. -/
/-- The alternating partial sum `∑_{j=0}^{k} (−1)^{k−j} a_j`. -/
def alternatingPartialSum (a : ℕ → ℕ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * (a j : ℤ)

/- **Morse inequalities** (Marston Morse, 1934). For a Morse function `f`
on a closed smooth finite-dimensional Hausdorff manifold `M` and every `k ∈ ℕ`,
`∑_{j≤k}(−1)^{k−j} c_j(f) ≥ ∑_{j≤k}(−1)^{k−j} b_j(M)`. -/
/-- Source: M. Morse, The Calculus of Variations in the Large, AMS Colloq. Publ. 18 (1934). Listed as §40 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `morse_inequality`. -/
public theorem_wanted morse_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] (f : M → ℝ) (_hf : IsMorseFunction I f) (k : ℕ) :
    alternatingPartialSum (bettiNumber M) k ≤
      alternatingPartialSum (morseCount I f) k

end MorseInequalities
end Geometry

end MathlibExt.Geometry.MorseInequalitiesWanted
