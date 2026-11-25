/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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
The statement and metric-compatibility predicate come from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.KoszulFormula`
(manifest `manifests/problems/koszul_formula.toml`, statement revision 1,
submitter Kim Morrison, status archived).
lean-eval ships no `NOTICE` file. ATLAS moved the declarations into ATLAS namespaces,
shared the predicate with other statements, and revised their docstrings. This file
retains those names, adds a proof in place of `theorem_wanted`, and narrows the imports.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Tactic.LinearCombination

/-!
# Koszul formula

Metric compatibility and vanishing torsion express the pairing of a covariant derivative
with a third vector field in terms of directional derivatives of the metric and Lie brackets.
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

end MathlibExt.Geometry.MetricCompatibilityShared

namespace MathlibExt.Geometry.KoszulFormulaWanted.Geometry.KoszulFormula

open MathlibExt.Geometry.MetricCompatibilityShared
open CovariantDerivative VectorField

-- Keep the existing declaration name (and hence its article link).
set_option linter.dupNamespace false in
/-- **Koszul formula.** Let $M$ be a smooth manifold, modelled with corners on a finite-dimensional
real normed space, whose tangent bundle carries a smooth Riemannian metric $\langle \cdot, \cdot
\rangle$, and let $\nabla$ be a smooth covariant derivative on the tangent bundle of $M$ that is
torsion-free and compatible with the metric. Then for all smooth vector fields $X$, $Y$, $Z$ on
$M$ and every point $x \in M$, evaluating every term at $x$,
$$2 \langle \nabla_X Y, Z \rangle = X \langle Y, Z \rangle + Y \langle X, Z \rangle -
Z \langle X, Y \rangle - \langle X, [Y, Z] \rangle - \langle Y, [X, Z] \rangle +
\langle Z, [X, Y] \rangle,$$
where $\nabla_X Y$ at $x$ is the covariant derivative of $Y$ in the direction $X(x)$,
$X \langle Y, Z \rangle$ at $x$ is the derivative of the function $y \mapsto \langle Y(y), Z(y)
\rangle$ in the direction $X(x)$, and $[\cdot, \cdot]$ is the Lie bracket of vector fields.

Source: J.-L. Koszul (course notes, 1950s); cf. do Carmo, Riemannian Geometry. Listed as §38
additional statement in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `koszul_formula`. -/
theorem koszul_formula
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
      + inner ℝ (Z x) (mlieBracket I X Y x) := by
  have metricX := _hmet Y Z _hY _hZ x (X x)
  have metricY := _hmet X Z _hX _hZ x (Y x)
  have metricZ := _hmet X Y _hX _hY x (Z x)
  rw [← real_inner_comm (cov X x (Z x)) (Y x)] at metricZ
  have torsion {U V : Π y : M, TangentSpace I y}
      (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) :=
    cov.torsion_eq_zero_iff.mp _htor hU hV
  have diffX := _hX.mdifferentiableAt (by simp) (x := x)
  have diffY := _hY.mdifferentiableAt (by simp) (x := x)
  have diffZ := _hZ.mdifferentiableAt (by simp) (x := x)
  have bracketXY := congrArg (inner ℝ (Z x)) (torsion diffX diffY)
  have bracketXZ := congrArg (inner ℝ (Y x)) (torsion diffX diffZ)
  have bracketYZ := congrArg (inner ℝ (X x)) (torsion diffY diffZ)
  simp only [inner_sub_right] at bracketXY bracketXZ bracketYZ
  rw [← real_inner_comm (Z x) (cov Y x (X x)),
    ← real_inner_comm (Z x) (cov X x (Y x))] at bracketXY
  linear_combination -metricX - metricY + metricZ - bracketXZ - bracketYZ + bracketXY

end MathlibExt.Geometry.KoszulFormulaWanted.Geometry.KoszulFormula
