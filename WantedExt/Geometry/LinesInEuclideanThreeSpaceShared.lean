/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lines in Euclidean 3-space (AIM additive combinatorics, Problems 3.12 and 3.13)

Shared definitions for the incidence problems on lines in `ℝ³` of the AIM workshop Recent trends in
additive combinatorics: Euclidean space `ℝ³` and its lines, the affine subspaces whose direction has
dimension `1`. Bourgain's incidence problem (Problem 3.12) and Tao's joints problem (Problem 3.13)
use them.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.LinesInEuclideanThreeSpaceShared

/-- Euclidean space `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- An affine subspace of `ℝ³` is a line when its direction has dimension `1`. -/
def IsLine (l : AffineSubspace ℝ E3) : Prop :=
  Module.finrank ℝ l.direction = 1

end MathlibExt.Geometry.LinesInEuclideanThreeSpaceShared
