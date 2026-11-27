/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Geometry.Manifold.Riemannian.KoszulFormula

open Bundle CovariantDerivative VectorField
open scoped ContDiff Manifold
open MathlibExt.Geometry.MetricCompatibilityShared
open MathlibExt.Geometry.KoszulFormulaWanted.Geometry.KoszulFormula

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

-- On the diagonal the brackets vanish and only one metric derivative remains.
example (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (X : Π x : M, TangentSpace I x) (hX : CMDiff ∞ (T% X)) (x : M) :
    2 * inner ℝ (cov X x (X x)) (X x) =
      mvfderiv I (fun y : M ↦ inner ℝ (X y) (X y)) x (X x) := by
  simpa using koszul_formula (I := I) (cov := cov) (_htor := htor) (_hmet := hmet)
    (X := X) (Y := X) (Z := X) (_hX := hX) (_hY := hX) (_hZ := hX) (x := x)

/--
info: 'MathlibExt.Geometry.KoszulFormulaWanted.Geometry.KoszulFormula.koszul_formula'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms koszul_formula
