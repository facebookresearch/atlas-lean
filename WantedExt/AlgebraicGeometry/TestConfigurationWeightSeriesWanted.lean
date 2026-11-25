/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries
public import Batteries.Util.ProofWanted

/-!
# Actual test-configuration section-weight limit

Boucksom--Hisamoto--Jonsson arXiv1504.06568v3, Theorem A.
Weights are kernels of the native linearized H0 coaction of the actual
central fibre, with actual tensor powers and generic-action normalization.
Ample generic/central polarizations are explicit. The measure is fixed by
weak convergence of those actual section measures, not a supplied DH oracle.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations

def_wanted sectionWeightLimit
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    (X : Over (Base k)) [Nonempty X.left] (L : X.left.Modules)
    (T : NormalizedTestConfiguration k X L) (A : AmpleData T.toTestConfiguration)
    (S : WeightSeries T) :
    {measure : MeasureTheory.Measure ℝ // measure Set.univ = 1 ∧ HasWeakLimit S measure ∧
      ∃ r : ℝ, 0 ≤ r ∧ measure (Set.Icc (-r) r)ᶜ = 0}

end MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries
