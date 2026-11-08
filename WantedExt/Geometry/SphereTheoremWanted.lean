/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Differentiable sphere theorem (Brendle–Schoen), Topological sphere theorem (Berger–Klingenberg–Rauch)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.SphereTheorem` — sphere_theorem_differentiable (manifest `manifests/problems/sphere_theorem_differentiable.toml`, rev 1, submitter Kim Morrison, status active); sphere_theorem_topological (manifest `manifests/problems/sphere_theorem_topological.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.SphereTheoremWanted` namespace. Mathematical
statements are unchanged. Source: S. Brendle & R. Schoen, *Manifolds with 1/4-pinched curvature are space forms*, J. AMS 22 (2009). Knill, *Some fundamental theorems in mathematics*, §121. M. Berger; W. Klingenberg; H. E. Rauch (topological sphere theorem, 1951–1961). Knill, *Some fundamental theorems in mathematics*, §121.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.MetricCompatibilityShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.MetricCompatibilityShared

namespace MathlibExt.Geometry.SphereTheoremWanted
namespace Geometry.SphereTheorem

/-!
# The sphere theorems (Berger–Klingenberg–Rauch; Brendle–Schoen)

`sphere_theorem`: a closed, simply-connected, strictly quarter-pinched Riemannian
manifold is homeomorphic to the standard sphere (Berger–Klingenberg–Rauch 1960).
`differentiable_sphere_theorem`: under the same hypotheses it is diffeomorphic to
the sphere (Brendle–Schoen 2007, via Ricci flow). The trusted helpers
(`IsMetricCompatible`, `curv`, `QuarterPinched`) are non-holes; following §38,
the Levi-Civita connection is hypothesized as a smooth torsion-free
metric-compatible covariant derivative (Mathlib has the covariant-derivative
interface but does not yet construct Levi-Civita). Mathlib has no Riemann
curvature tensor, sectional curvature, pinching, or Ricci flow.

Category-(b) candidates from §121 of the Knill survey.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/- A covariant derivative `cov` is **compatible with the Riemannian metric**:
`v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩`. -/
/-- The **Riemann curvature tensor** of `cov` on smooth vector fields:
`R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`. -/
noncomputable def curv (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun x =>
    cov (fun y => cov Z y (Y y)) x (X x)
      - cov (fun y => cov Z y (X y)) x (Y x)
      - cov Z x (mlieBracket I X Y x)

/-- The manifold is **strictly quarter-pinched**: every sectional curvature
`K = ⟨R(X,Y)Y, X⟩` at an orthonormal pair lies in Knill's interval `(1, 4]`. -/
def QuarterPinched
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (X Y : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
    ∀ x : M,
      inner ℝ (X x) (X x) = (1 : ℝ) → inner ℝ (Y x) (Y x) = (1 : ℝ) →
      inner ℝ (X x) (Y x) = (0 : ℝ) →
      (1 : ℝ) < inner ℝ (curv cov X Y Y x) (X x) ∧
        inner ℝ (curv cov X Y Y x) (X x) ≤ (4 : ℝ)

/- **Topological sphere theorem** (Berger–Klingenberg–Rauch 1960). A closed,
simply-connected, smooth `d`-manifold (`d ≥ 2`) whose Levi-Civita connection is
strictly quarter-pinched is homeomorphic to the standard `d`-sphere. -/
/-- Source: M. Berger; W. Klingenberg; H. E. Rauch (topological sphere theorem, 1951–1961). Knill, *Some fundamental theorems in mathematics*, §121. Via leanprover/lean-eval@38361be, problem `sphere_theorem_topological`. -/
public theorem_wanted sphere_theorem
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (_hpinch : QuarterPinched cov) :
    Nonempty
      (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1)

/- **Differentiable sphere theorem** (Brendle–Schoen 2007). Under the same
hypotheses, `M` is diffeomorphic to the standard `d`-sphere. -/
/-- Source: S. Brendle & R. Schoen, *Manifolds with 1/4-pinched curvature are space forms*, J. AMS 22 (2009). Knill, *Some fundamental theorems in mathematics*, §121. Via leanprover/lean-eval@38361be, problem `sphere_theorem_differentiable`. -/
public theorem_wanted differentiable_sphere_theorem
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (_hpinch : QuarterPinched cov) :
    Nonempty
      (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯
        (sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1))

end Geometry.SphereTheorem

end MathlibExt.Geometry.SphereTheoremWanted
