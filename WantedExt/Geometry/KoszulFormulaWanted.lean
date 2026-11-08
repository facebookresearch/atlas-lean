/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Koszul formula

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.KoszulFormula` — koszul_formula (manifest `manifests/problems/koszul_formula.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.KoszulFormulaWanted` namespace. Mathematical
statements are unchanged. Source: J.-L. Koszul (course notes, 1950s); cf. do Carmo, Riemannian Geometry. Listed as §38 additional statement in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.MetricCompatibilityShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.MetricCompatibilityShared

namespace MathlibExt.Geometry.KoszulFormulaWanted
namespace Geometry
namespace KoszulFormula

/-!
# Koszul formula

§38 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (an
additional statement of the section on Riemannian geometry; the boxed
main theorem is the Levi-Civita fundamental theorem). For any smooth
torsion-free metric-compatible covariant derivative `cov` on the tangent
bundle of a Riemannian manifold, the inner product `⟨∇_X Y, Z⟩` is
determined by the metric and Lie brackets via

`2 ⟨∇_X Y, Z⟩ = X·⟨Y, Z⟩ + Y·⟨X, Z⟩ − Z·⟨X, Y⟩`
`               − ⟨X, [Y, Z]⟩ − ⟨Y, [X, Z]⟩ + ⟨Z, [X, Y]⟩`.

This is the **Koszul formula** — the explicit identity that *forces*
uniqueness of the Levi-Civita connection.

mathlib has the covariant-derivative / Riemannian-bundle / Lie-bracket
machinery but no metric-compatibility predicate and no Koszul formula
(`grep -ri Koszul`: no relevant hits). One helper definition
(`IsMetricCompatible`, ~½ page) is added here.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

/- A covariant derivative `cov` on `TM` is **compatible with the
Riemannian metric** if `v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all
smooth vector fields `Y, Z` and every point/direction `(x, v)`. -/
/- **Koszul formula.** For any smooth torsion-free metric-compatible
covariant derivative `cov` on `TM`, `2 ⟨∇_X Y, Z⟩` equals the cyclic sum
of directional derivatives `X·⟨Y, Z⟩ + Y·⟨X, Z⟩ − Z·⟨X, Y⟩` minus the
Lie-bracket cyclic sum `⟨X, [Y, Z]⟩ + ⟨Y, [X, Z]⟩ − ⟨Z, [X, Y]⟩`. -/
/-- Source: J.-L. Koszul (course notes, 1950s); cf. do Carmo, Riemannian Geometry. Listed as §38 additional statement in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `koszul_formula`. -/
public theorem_wanted koszul_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (X Y Z : Π x : M, TangentSpace I x)
    (_hX : CMDiff ∞ (T% X)) (_hY : CMDiff ∞ (T% Y)) (_hZ : CMDiff ∞ (T% Z))
    (x : M) :
    2 * inner ℝ (cov Y x (X x)) (Z x) =
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x (X x)
      + mvfderiv I (fun y : M => inner ℝ (X y) (Z y)) x (Y x)
      - mvfderiv I (fun y : M => inner ℝ (X y) (Y y)) x (Z x)
      - inner ℝ (X x) (mlieBracket I Y Z x)
      - inner ℝ (Y x) (mlieBracket I X Z x)
      + inner ℝ (Z x) (mlieBracket I X Y x)

end KoszulFormula
end Geometry

end MathlibExt.Geometry.KoszulFormulaWanted
