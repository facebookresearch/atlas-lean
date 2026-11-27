/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticCyclePairingsPullbackTheory
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Tests of smooth pullback

The pullback theorem supplies smoothness for the identity map on the
one-dimensional complex coordinate space, viewed as a real manifold.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AnalyticCyclePairingsPullbackTheory

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms AnalyticCyclePairings
open scoped Manifold ContDiff

example (p : ℕ) (a : GlobalForms ℝ (Coordinates 1) (Coordinates 1) p) :
    IsSmooth ℝ (Coordinates 1) (Coordinates 1)
      (pullbackRough 1 (Coordinates 1) 1 (Coordinates 1) id a.val) := by
  exact (WantedExt.AlgebraicGeometry.AnalyticCyclePairingsWanted.pullbackTheory
    1 (Coordinates 1) 1 (Coordinates 1) id contMDiff_id).smooth p a

end MathlibExtTest.AlgebraicGeometry.AnalyticCyclePairingsPullbackTheory
