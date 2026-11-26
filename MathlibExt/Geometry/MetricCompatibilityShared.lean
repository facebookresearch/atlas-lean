/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Geometry/LeviCivita.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `levi_civita_exists_unique` (manifest
`manifests/problems/levi_civita_exists_unique.toml`, rev 1, submitted by Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"). You may obtain a copy at
https://www.apache.org/licenses/LICENSE-2.0. The adapted portions are distributed on an "AS IS"
basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License
for the specific language governing permissions and limitations. lean-eval ships no NOTICE file.

The adapted portion is the definition `IsMetricCompatible`, the trusted (non-hole) helper of the
lean-eval problems on the Levi-Civita connection, the Koszul formula and the sphere theorem (the
module documentation of `LeanEval/Geometry/LeviCivita.lean` records that it adds this definition).
ATLAS placed it, unchanged apart from the namespace, in the shared wanted module
`WantedExt/Geometry/MetricCompatibilityShared.lean`, and moved it to this module when the
Levi-Civita theorem that uses it was proved.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Metric compatibility of covariant derivatives on the tangent bundle

This file defines `IsMetricCompatible`: a covariant derivative on the tangent bundle of a
Riemannian manifold is compatible with the metric when it satisfies the product rule
`v ⟨Y, Z⟩ = ⟨∇_v Y, Z⟩ + ⟨Y, ∇_v Z⟩` for all smooth vector fields `Y` and `Z`.

The definition is shared by the statements on the Koszul formula, the Levi-Civita connection
and the sphere theorem. Mathlib's `CovariantDerivative.IsMetricCompatible` asks for the same
identity for all vector fields that are differentiable at the point, so it implies this one:
this is `IsMetricCompatible.of_isMetricCompatible`.
-/

@[expose] public section

open Bundle
open scoped ContDiff Manifold

namespace MathlibExt.Geometry.MetricCompatibilityShared

/-- **Metric-compatible covariant derivative.** Let $M$ be a smooth manifold (possibly with
corners) modelled on a finite-dimensional real normed space, with a smooth Riemannian metric
$\langle \cdot, \cdot \rangle$ on its tangent bundle. A covariant derivative $\nabla$ on the
tangent bundle is compatible with the metric if for all smooth vector fields $Y, Z$ on $M$,
every point $x \in M$ and every tangent vector $v \in T_x M$,
$$
v \langle Y, Z \rangle = \langle \nabla_v Y, Z(x) \rangle + \langle Y(x), \nabla_v Z \rangle,
$$
where $v \langle Y, Z \rangle$ is the derivative at $x$ in the direction $v$ of the function
$y \mapsto \langle Y(y), Z(y) \rangle$. -/
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

/-- **Mathlib's metric compatibility implies `IsMetricCompatible`.** Let $\nabla$ be a covariant
derivative on the tangent bundle of a smooth manifold $M$ (possibly with corners) modelled on a
finite-dimensional real normed space, with a smooth Riemannian metric on its tangent bundle.
Suppose $\nabla$ is compatible with the metric in the sense of Mathlib's
`CovariantDerivative.IsMetricCompatible`: at every point $x \in M$,
$X \langle Y, Z \rangle = \langle \nabla_X Y, Z \rangle + \langle Y, \nabla_X Z \rangle$ for all
vector fields $X, Y, Z$ differentiable at $x$. Then $\nabla$ satisfies `IsMetricCompatible`, the
same product rule for all smooth vector fields $Y, Z$ and every tangent vector.

Source: direct from the two definitions, original to this formalization: Mathlib's product rule
is applied to a vector field that extends the given tangent vector. -/
theorem IsMetricCompatible.of_isMetricCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I)) :
    IsMetricCompatible cov := by
  intro Y Z hY hZ x v
  simpa using hcov.mvfderiv_inner_eq (FiberBundle.extend E v) (x := x)
    ((hY x).mdifferentiableAt (by simp)) ((hZ x).mdifferentiableAt (by simp))

end MathlibExt.Geometry.MetricCompatibilityShared
