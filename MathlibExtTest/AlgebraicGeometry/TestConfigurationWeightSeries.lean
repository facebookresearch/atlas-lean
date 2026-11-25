/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries

/-!
# Tests for test-configuration weight series

The section measures are normalized relative to the declared polarization: for a test
configuration of exponent `2`, the degree-`m` weights are divided by `2 m`, not by `m`. The
polarization of a test configuration is ample on its total space.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
open MathlibExt.AlgebraicGeometry.EquivariantSectionWeights
open MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries

variable {k : Type} [Field k] {X : CategoryTheory.Over (Base k)} {L : X.left.Modules}

/-- For exponent `2`, the degree-`m` weights are divided by `2 m`. -/
example {T : NormalizedTestConfiguration k X L} (S : WeightSeries T) (m : ℕ)
    (h : T.toTestConfiguration.exponent = 2) :
    letI := S.centralData.action
    sectionMeasure S m = MeasureTheory.Measure.map (fun x : ℝ => -x)
      (weightMeasure (S.finiteWeights m) (2 * m)) := by
  rw [sectionMeasure_eq, h]

/-- The polarization of a test configuration is ample on its total space. -/
example (T : TestConfiguration k X L) :
    MathlibExt.AlgebraicGeometry.ProjectiveLineSystems.IsAmpleLine ⟨T.polarization, T.line⟩ :=
  T.ample
