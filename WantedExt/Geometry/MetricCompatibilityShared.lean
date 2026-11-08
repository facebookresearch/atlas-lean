/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared metric-compatibility predicate

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the Koszul formula, Levi-Civita, and sphere-theorem wanted entries. The definition is the trusted (non-hole) helper from leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e, distributed under the Apache License, Version 2.0; unchanged apart from the namespace.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

@[expose] public section

open Bundle
open scoped ContDiff Manifold

namespace MathlibExt.Geometry.MetricCompatibilityShared

/-- A covariant derivative `cov` is **compatible with the Riemannian metric**:
`v · ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all smooth vector fields `Y, Z`
and every point/direction `(x, v)`. -/
def IsMetricCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (Y Z : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ (x : M) (v : TangentSpace I x),
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x v =
        inner ℝ (cov Y x v) (Z x) + inner ℝ (Y x) (cov Z x v)

end MathlibExt.Geometry.MetricCompatibilityShared
