/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricChowOperators

/-!
# Negative virtual-degree and cycle-coordinate checks

Negative Chow degree must be zero rather than being silently converted to
degree zero. A single genuine cycle must retain its coordinate under the
finite-support transport used by all computed pullbacks and pushforwards.
-/

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow
open MathlibExt.AlgebraicGeometry.GeometricChowOperators

noncomputable section

example (X : ComplexScheme) : Subsingleton (gradedChow X (-1)) := by
  dsimp [gradedChow]
  infer_instance

example (X : Scheme) [IsNoetherian X] [DecidableEq X] (x : X) (a : ℚ) :
    cycleFinsupp X (Function.locallyFinsuppWithin.single x a) = Finsupp.single x a := by
  classical
  ext y
  simp [cycleFinsupp, Finsupp.single_apply, Pi.single_apply, eq_comm]
